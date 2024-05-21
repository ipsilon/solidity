/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0
/** @file Assembly.cpp
 * @author Gav Wood <i@gavwood.com>
 * @date 2014
 */

#include <libevmasm/Assembly.h>

#include <libevmasm/CommonSubexpressionEliminator.h>
#include <libevmasm/ControlFlowGraph.h>
#include <libevmasm/PeepholeOptimiser.h>
#include <libevmasm/Inliner.h>
#include <libevmasm/JumpdestRemover.h>
#include <libevmasm/BlockDeduplicator.h>
#include <libevmasm/ConstantOptimiser.h>

#include <liblangutil/CharStream.h>
#include <liblangutil/Exceptions.h>

#include <libsolutil/JSON.h>
#include <libsolutil/StringUtils.h>

#include <fmt/format.h>

#include <range/v3/algorithm/any_of.hpp>
#include <range/v3/view/drop_exactly.hpp>
#include <range/v3/view/enumerate.hpp>
#include <range/v3/view/map.hpp>

#include <fstream>
#include <limits>
#include <iterator>

using namespace solidity;
using namespace solidity::evmasm;
using namespace solidity::langutil;
using namespace solidity::util;

std::map<std::string, std::shared_ptr<std::string const>> Assembly::s_sharedSourceNames;

AssemblyItem const& Assembly::append(AssemblyItem _i)
{
	assertThrow(m_deposit >= 0, AssemblyException, "Stack underflow.");
	m_deposit += static_cast<int>(_i.deposit());
	auto& currentItems = m_codeSections.at(m_currentCodeSection).items;
	currentItems.emplace_back(std::move(_i));
	if (!currentItems.back().location().isValid() && m_currentSourceLocation.isValid())
		currentItems.back().setLocation(m_currentSourceLocation);
	currentItems.back().m_modifierDepth = m_currentModifierDepth;
	return currentItems.back();
}

unsigned Assembly::codeSize(unsigned subTagSize) const
{
	for (unsigned tagSize = subTagSize; true; ++tagSize)
	{
		size_t ret = 1;

		for (auto const& codeSection: m_codeSections)
			for (AssemblyItem const& i: codeSection.items)
				ret += i.bytesRequired(tagSize, Precision::Approximate);
		if (numberEncodingSize(ret) <= tagSize)
			return static_cast<unsigned>(ret);
	}
}

void Assembly::importAssemblyItemsFromJSON(Json::Value const& _code, std::vector<std::string> const& _sourceList)
{
	solAssert(m_codeSections.empty());
	solAssert(m_codeSections[0].items.empty());
	m_codeSections.resize(1);
	// TODO: Add support for EOF and more than one code sections.
	solRequire(_code.isArray(), AssemblyImportException, "Supplied JSON is not an array.");
	for (auto jsonItemIter = std::begin(_code); jsonItemIter != std::end(_code); ++jsonItemIter)
	{
		AssemblyItem const& newItem = m_codeSections[0].items.emplace_back(createAssemblyItemFromJSON(*jsonItemIter, _sourceList));
		if (newItem == Instruction::JUMPDEST)
			solThrow(AssemblyImportException, "JUMPDEST instruction without a tag");
		else if (newItem.type() == AssemblyItemType::Tag)
		{
			++jsonItemIter;
			if (jsonItemIter != std::end(_code) && createAssemblyItemFromJSON(*jsonItemIter, _sourceList) != Instruction::JUMPDEST)
				solThrow(AssemblyImportException, "JUMPDEST expected after tag.");
		}
	}
}

AssemblyItem Assembly::createAssemblyItemFromJSON(Json::Value const& _json, std::vector<std::string> const& _sourceList)
{
	solRequire(_json.isObject(), AssemblyImportException, "Supplied JSON is not an object.");
	static std::set<std::string> const validMembers{"name", "begin", "end", "source", "value", "modifierDepth", "jumpType"};
	for (std::string const& member: _json.getMemberNames())
		solRequire(
			validMembers.count(member),
			AssemblyImportException,
			fmt::format(
				"Unknown member '{}'. Valid members are: {}.",
				member,
				solidity::util::joinHumanReadable(validMembers, ", ")
			)
		);
	solRequire(isOfType<std::string>(_json["name"]), AssemblyImportException, "Member 'name' missing or not of type string.");
	solRequire(isOfTypeIfExists<int>(_json, "begin"), AssemblyImportException, "Optional member 'begin' not of type int.");
	solRequire(isOfTypeIfExists<int>(_json, "end"), AssemblyImportException, "Optional member 'end' not of type int.");
	solRequire(isOfTypeIfExists<int>(_json, "source"), AssemblyImportException, "Optional member 'source' not of type int.");
	solRequire(isOfTypeIfExists<std::string>(_json, "value"), AssemblyImportException, "Optional member 'value' not of type string.");
	solRequire(isOfTypeIfExists<int>(_json, "modifierDepth"), AssemblyImportException, "Optional member 'modifierDepth' not of type int.");
	solRequire(isOfTypeIfExists<std::string>(_json, "jumpType"), AssemblyImportException, "Optional member 'jumpType' not of type string.");

	std::string name = get<std::string>(_json["name"]);
	solRequire(!name.empty(), AssemblyImportException, "Member 'name' is empty.");

	SourceLocation location;
	if (_json.isMember("begin"))
		location.start = get<int>(_json["begin"]);
	if (_json.isMember("end"))
		location.end = get<int>(_json["end"]);
	int srcIndex = getOrDefault<int>(_json["source"], -1);
	size_t modifierDepth = static_cast<size_t>(getOrDefault<int>(_json["modifierDepth"], 0));
	std::string value = getOrDefault<std::string>(_json["value"], "");
	std::string jumpType = getOrDefault<std::string>(_json["jumpType"], "");

	auto updateUsedTags = [&](u256 const& data)
	{
		m_usedTags = std::max(m_usedTags, static_cast<unsigned>(data) + 1);
		return data;
	};

	auto storeImmutableHash = [&](std::string const& _immutableName) -> h256
	{
		h256 hash(util::keccak256(_immutableName));
		solAssert(m_immutables.count(hash) == 0 || m_immutables[hash] == _immutableName);
		m_immutables[hash] = _immutableName;
		return hash;
	};

	auto storeLibraryHash = [&](std::string const& _libraryName) -> h256
	{
		h256 hash(util::keccak256(_libraryName));
		solAssert(m_libraries.count(hash) == 0 || m_libraries[hash] == _libraryName);
		m_libraries[hash] = _libraryName;
		return hash;
	};

	auto requireValueDefinedForInstruction = [&](std::string const& _name, std::string const& _value)
	{
		solRequire(
			!_value.empty(),
			AssemblyImportException,
			"Member 'value' is missing for instruction '" + _name + "', but the instruction needs a value."
		);
	};

	auto requireValueUndefinedForInstruction = [&](std::string const& _name, std::string const& _value)
	{
		solRequire(
			_value.empty(),
			AssemblyImportException,
			"Member 'value' defined for instruction '" + _name + "', but the instruction does not need a value."
		);
	};

	solRequire(srcIndex >= -1 && srcIndex < static_cast<int>(_sourceList.size()), AssemblyImportException, "Source index out of bounds.");
	if (srcIndex != -1)
		location.sourceName = sharedSourceName(_sourceList[static_cast<size_t>(srcIndex)]);

	AssemblyItem result(0);

	if (c_instructions.count(name))
	{
		AssemblyItem item{c_instructions.at(name), langutil::DebugData::create(location)};
		if (!jumpType.empty())
		{
			if (item.instruction() == Instruction::JUMP || item.instruction() == Instruction::JUMPI)
			{
				std::optional<AssemblyItem::JumpType> parsedJumpType = AssemblyItem::parseJumpType(jumpType);
				if (!parsedJumpType.has_value())
					solThrow(AssemblyImportException, "Invalid jump type.");
				item.setJumpType(parsedJumpType.value());
			}
			else
				solThrow(
					AssemblyImportException,
					"Member 'jumpType' set on instruction different from JUMP or JUMPI (was set on instruction '" + name + "')"
				);
		}
		requireValueUndefinedForInstruction(name, value);
		result = item;
	}
	else
	{
		solRequire(
			jumpType.empty(),
			AssemblyImportException,
			"Member 'jumpType' set on instruction different from JUMP or JUMPI (was set on instruction '" + name + "')"
		);
		if (name == "PUSH")
		{
			requireValueDefinedForInstruction(name, value);
			result = {AssemblyItemType::Push, u256("0x" + value)};
		}
		else if (name == "PUSH [ErrorTag]")
		{
			requireValueUndefinedForInstruction(name, value);
			result = {AssemblyItemType::PushTag, 0};
		}
		else if (name == "PUSH [tag]")
		{
			requireValueDefinedForInstruction(name, value);
			result = {AssemblyItemType::PushTag, updateUsedTags(u256(value))};
		}
		else if (name == "PUSH [$]")
		{
			requireValueDefinedForInstruction(name, value);
			result = {AssemblyItemType::PushSub, u256("0x" + value)};
		}
		else if (name == "PUSH #[$]")
		{
			requireValueDefinedForInstruction(name, value);
			result = {AssemblyItemType::PushSubSize, u256("0x" + value)};
		}
		else if (name == "PUSHSIZE")
		{
			requireValueUndefinedForInstruction(name, value);
			result = {AssemblyItemType::PushProgramSize, 0};
		}
		else if (name == "PUSHLIB")
		{
			requireValueDefinedForInstruction(name, value);
			result = {AssemblyItemType::PushLibraryAddress, storeLibraryHash(value)};
		}
		else if (name == "PUSHDEPLOYADDRESS")
		{
			requireValueUndefinedForInstruction(name, value);
			result = {AssemblyItemType::PushDeployTimeAddress, 0};
		}
		else if (name == "PUSHIMMUTABLE")
		{
			requireValueDefinedForInstruction(name, value);
			result = {AssemblyItemType::PushImmutable, storeImmutableHash(value)};
		}
		else if (name == "ASSIGNIMMUTABLE")
		{
			requireValueDefinedForInstruction(name, value);
			result = {AssemblyItemType::AssignImmutable, storeImmutableHash(value)};
		}
		else if (name == "tag")
		{
			requireValueDefinedForInstruction(name, value);
			result = {AssemblyItemType::Tag, updateUsedTags(u256(value))};
		}
		else if (name == "PUSH data")
		{
			requireValueDefinedForInstruction(name, value);
			result = {AssemblyItemType::PushData, u256("0x" + value)};
		}
		else if (name == "VERBATIM")
		{
			requireValueDefinedForInstruction(name, value);
			AssemblyItem item(fromHex(value), 0, 0);
			result = item;
		}
		else
			solThrow(InvalidOpcode, "Invalid opcode: " + name);
	}
	result.setLocation(location);
	result.m_modifierDepth = modifierDepth;
	return result;
}

namespace
{

std::string locationFromSources(StringMap const& _sourceCodes, SourceLocation const& _location)
{
	if (!_location.hasText() || _sourceCodes.empty())
		return {};

	auto it = _sourceCodes.find(*_location.sourceName);
	if (it == _sourceCodes.end())
		return {};

	return CharStream::singleLineSnippet(it->second, _location);
}

class Functionalizer
{
public:
	Functionalizer (std::ostream& _out, std::string const& _prefix, StringMap const& _sourceCodes, Assembly const& _assembly):
		m_out(_out), m_prefix(_prefix), m_sourceCodes(_sourceCodes), m_assembly(_assembly)
	{}

	void feed(AssemblyItem const& _item, DebugInfoSelection const& _debugInfoSelection)
	{
		if (_item.location().isValid() && _item.location() != m_location)
		{
			flush();
			m_location = _item.location();
			printLocation(_debugInfoSelection);
		}

		std::string expression = _item.toAssemblyText(m_assembly);

		if (!(
			_item.canBeFunctional() &&
			_item.returnValues() <= 1 &&
			_item.arguments() <= m_pending.size()
		))
		{
			flush();
			m_out << m_prefix << (_item.type() == Tag ? "" : "  ") << expression << std::endl;
			return;
		}
		if (_item.arguments() > 0)
		{
			expression += "(";
			for (size_t i = 0; i < _item.arguments(); ++i)
			{
				expression += m_pending.back();
				m_pending.pop_back();
				if (i + 1 < _item.arguments())
					expression += ", ";
			}
			expression += ")";
		}

		m_pending.push_back(expression);
		if (_item.returnValues() != 1)
			flush();
	}

	void flush()
	{
		for (std::string const& expression: m_pending)
			m_out << m_prefix << "  " << expression << std::endl;
		m_pending.clear();
	}

	void printLocation(DebugInfoSelection const& _debugInfoSelection)
	{
		if (!m_location.isValid() || (!_debugInfoSelection.location && !_debugInfoSelection.snippet))
			return;

		m_out << m_prefix << "    /*";

		if (_debugInfoSelection.location)
		{
			if (m_location.sourceName)
				m_out << " " + escapeAndQuoteString(*m_location.sourceName);
			if (m_location.hasText())
				m_out << ":" << std::to_string(m_location.start) + ":" + std::to_string(m_location.end);
		}

		if (_debugInfoSelection.snippet)
		{
			if (_debugInfoSelection.location)
				m_out << "  ";

			m_out << locationFromSources(m_sourceCodes, m_location);
		}

		m_out << " */" << std::endl;
	}

private:
	strings m_pending;
	SourceLocation m_location;

	std::ostream& m_out;
	std::string const& m_prefix;
	StringMap const& m_sourceCodes;
	Assembly const& m_assembly;
};

}

void Assembly::assemblyStream(
	std::ostream& _out,
	DebugInfoSelection const& _debugInfoSelection,
	std::string const& _prefix,
	StringMap const& _sourceCodes
) const
{
	Functionalizer f(_out, _prefix, _sourceCodes, *this);

	// TODO: support EOF
	for (auto const& i: m_codeSections.front().items)
		f.feed(i, _debugInfoSelection);
	f.flush();

	if (!m_data.empty() || !m_subs.empty())
	{
		_out << _prefix << "stop" << std::endl;
		for (auto const& i: m_data)
			if (u256(i.first) >= m_subs.size())
				_out << _prefix << "data_" << toHex(u256(i.first)) << " " << util::toHex(i.second) << std::endl;

		for (size_t i = 0; i < m_subs.size(); ++i)
		{
			_out << std::endl << _prefix << "sub_" << i << ": assembly {\n";
			m_subs[i]->assemblyStream(_out, _debugInfoSelection, _prefix + "    ", _sourceCodes);
			_out << _prefix << "}" << std::endl;
		}
	}

	if (m_auxiliaryData.size() > 0)
		_out << std::endl << _prefix << "auxdata: 0x" << util::toHex(m_auxiliaryData) << std::endl;
}

std::string Assembly::assemblyString(
	DebugInfoSelection const& _debugInfoSelection,
	StringMap const& _sourceCodes
) const
{
	std::ostringstream tmp;
	assemblyStream(tmp, _debugInfoSelection, "", _sourceCodes);
	return tmp.str();
}

Json::Value Assembly::assemblyJSON(std::map<std::string, unsigned> const& _sourceIndices, bool _includeSourceList) const
{
	Json::Value root;
	root[".code"] = Json::arrayValue;
	Json::Value& code = root[".code"];
	// TODO: support EOF
	for (AssemblyItem const& item: m_codeSections.front().items)
	{
		int sourceIndex = -1;
		if (item.location().sourceName)
		{
			auto iter = _sourceIndices.find(*item.location().sourceName);
			if (iter != _sourceIndices.end())
				sourceIndex = static_cast<int>(iter->second);
		}

		auto [name, data] = item.nameAndData(m_evmVersion);
		Json::Value jsonItem;
		jsonItem["name"] = name;
		jsonItem["begin"] = item.location().start;
		jsonItem["end"] = item.location().end;
		if (item.m_modifierDepth != 0)
			jsonItem["modifierDepth"] = static_cast<int>(item.m_modifierDepth);
		std::string jumpType = item.getJumpTypeAsString();
		if (!jumpType.empty())
			jsonItem["jumpType"] = jumpType;
		if (name == "PUSHLIB")
			data = m_libraries.at(h256(data));
		else if (name == "PUSHIMMUTABLE" || name == "ASSIGNIMMUTABLE")
			data = m_immutables.at(h256(data));
		if (!data.empty())
			jsonItem["value"] = data;
		jsonItem["source"] = sourceIndex;
		code.append(std::move(jsonItem));

		if (item.type() == AssemblyItemType::Tag)
		{
			Json::Value jumpdest;
			jumpdest["name"] = "JUMPDEST";
			jumpdest["begin"] = item.location().start;
			jumpdest["end"] = item.location().end;
			jumpdest["source"] = sourceIndex;
			if (item.m_modifierDepth != 0)
				jumpdest["modifierDepth"] = static_cast<int>(item.m_modifierDepth);
			code.append(std::move(jumpdest));
		}
	}
	if (_includeSourceList)
	{
		root["sourceList"] = Json::arrayValue;
		Json::Value& jsonSourceList = root["sourceList"];
		for (auto const& [name, index]: _sourceIndices)
			jsonSourceList[index] = name;
	}

	if (!m_data.empty() || !m_subs.empty())
	{
		root[".data"] = Json::objectValue;
		Json::Value& data = root[".data"];
		for (auto const& i: m_data)
			if (u256(i.first) >= m_subs.size())
				data[util::toHex(toBigEndian((u256)i.first), util::HexPrefix::DontAdd, util::HexCase::Upper)] = util::toHex(i.second);

		for (size_t i = 0; i < m_subs.size(); ++i)
		{
			std::stringstream hexStr;
			hexStr << std::hex << i;
			data[hexStr.str()] = m_subs[i]->assemblyJSON(_sourceIndices, /*_includeSourceList = */false);
		}
	}

	if (!m_auxiliaryData.empty())
		root[".auxdata"] = util::toHex(m_auxiliaryData);

	return root;
}

std::pair<std::shared_ptr<Assembly>, std::vector<std::string>> Assembly::fromJSON(
	Json::Value const& _json,
	std::vector<std::string> const& _sourceList,
	size_t _level
)
{
	solRequire(_json.isObject(), AssemblyImportException, "Supplied JSON is not an object.");
	static std::set<std::string> const validMembers{".code", ".data", ".auxdata", "sourceList"};
	for (std::string const& attribute: _json.getMemberNames())
		solRequire(validMembers.count(attribute), AssemblyImportException, "Unknown attribute '" + attribute + "'.");

	if (_level == 0)
	{
		if (_json.isMember("sourceList"))
		{
			solRequire(_json["sourceList"].isArray(), AssemblyImportException, "Optional member 'sourceList' is not an array.");
			for (Json::Value const& sourceName: _json["sourceList"])
				solRequire(sourceName.isString(), AssemblyImportException, "The 'sourceList' array contains an item that is not a string.");
		}
	}
	else
		solRequire(
			!_json.isMember("sourceList"),
			AssemblyImportException,
			"Member 'sourceList' may only be present in the root JSON object."
		);

	auto result = std::make_shared<Assembly>(EVMVersion{}, _level == 0 /* _creation */, std::nullopt, "" /* _name */);
	std::vector<std::string> parsedSourceList;
	if (_json.isMember("sourceList"))
	{
		solAssert(_level == 0);
		solAssert(_sourceList.empty());
		for (Json::Value const& sourceName: _json["sourceList"])
		{
			solRequire(
				std::find(parsedSourceList.begin(), parsedSourceList.end(), sourceName.asString()) == parsedSourceList.end(),
				AssemblyImportException,
				"Items in 'sourceList' array are not unique."
			);
			parsedSourceList.emplace_back(sourceName.asString());
		}
	}

	solRequire(_json.isMember(".code"), AssemblyImportException, "Member '.code' is missing.");
	solRequire(_json[".code"].isArray(), AssemblyImportException, "Member '.code' is not an array.");
	for (Json::Value const& codeItem: _json[".code"])
		solRequire(codeItem.isObject(), AssemblyImportException, "The '.code' array contains an item that is not an object.");

	result->importAssemblyItemsFromJSON(_json[".code"], _level == 0 ? parsedSourceList : _sourceList);

	if (_json.isMember(".auxdata"))
	{
		solRequire(_json[".auxdata"].isString(), AssemblyImportException, "Optional member '.auxdata' is not a string.");
		result->m_auxiliaryData = fromHex(_json[".auxdata"].asString());
		solRequire(!result->m_auxiliaryData.empty(), AssemblyImportException, "Optional member '.auxdata' is not a valid hexadecimal string.");
	}

	if (_json.isMember(".data"))
	{
		solRequire(_json[".data"].isObject(), AssemblyImportException, "Optional member '.data' is not an object.");
		Json::Value const& data = _json[".data"];
		std::map<size_t, std::shared_ptr<Assembly>> subAssemblies;
		for (Json::ValueConstIterator dataIter = data.begin(); dataIter != data.end(); dataIter++)
		{
			solAssert(dataIter.key().isString());
			std::string dataItemID = dataIter.key().asString();
			Json::Value const& dataItem = data[dataItemID];
			if (dataItem.isString())
			{
				solRequire(
					dataItem.asString().empty() || !fromHex(dataItem.asString()).empty(),
					AssemblyImportException,
					"The value for key '" + dataItemID + "' inside '.data' is not a valid hexadecimal string."
				);
				result->m_data[h256(fromHex(dataItemID))] = fromHex(dataItem.asString());
			}
			else if (dataItem.isObject())
			{
				size_t index{};
				try
				{
					// Using signed variant because stoul() still accepts negative numbers and
					// just lets them wrap around.
					int parsedDataItemID = std::stoi(dataItemID, nullptr, 16);
					solRequire(parsedDataItemID >= 0, AssemblyImportException, "The key '" + dataItemID + "' inside '.data' is out of the supported integer range.");
					index = static_cast<size_t>(parsedDataItemID);
				}
				catch (std::invalid_argument const&)
				{
					solThrow(AssemblyImportException, "The key '" + dataItemID + "' inside '.data' is not an integer.");
				}
				catch (std::out_of_range const&)
				{
					solThrow(AssemblyImportException, "The key '" + dataItemID + "' inside '.data' is out of the supported integer range.");
				}

				auto [subAssembly, emptySourceList] = Assembly::fromJSON(dataItem, _level == 0 ? parsedSourceList : _sourceList, _level + 1);
				solAssert(subAssembly);
				solAssert(emptySourceList.empty());
				solAssert(subAssemblies.count(index) == 0);
				subAssemblies[index] = subAssembly;
			}
			else
				solThrow(AssemblyImportException, "The value of key '" + dataItemID + "' inside '.data' is neither a hex string nor an object.");
		}

		if (!subAssemblies.empty())
			solRequire(
				ranges::max(subAssemblies | ranges::views::keys) == subAssemblies.size() - 1,
				AssemblyImportException,
				fmt::format(
					"Invalid subassembly indices in '.data'. Not all numbers between 0 and {} are present.",
					subAssemblies.size() - 1
				)
			);

		result->m_subs = subAssemblies | ranges::views::values | ranges::to<std::vector>;
	}

	if (_level == 0)
		result->encodeAllPossibleSubPathsInAssemblyTree();

	return std::make_pair(result, _level == 0 ? parsedSourceList : std::vector<std::string>{});
}

void Assembly::encodeAllPossibleSubPathsInAssemblyTree(std::vector<size_t> _pathFromRoot, std::vector<Assembly*> _assembliesOnPath)
{
	_assembliesOnPath.push_back(this);
	for (_pathFromRoot.push_back(0); _pathFromRoot.back() < m_subs.size(); ++_pathFromRoot.back())
	{
		for (size_t distanceFromRoot = 0; distanceFromRoot < _assembliesOnPath.size(); ++distanceFromRoot)
			_assembliesOnPath[distanceFromRoot]->encodeSubPath(
				_pathFromRoot | ranges::views::drop_exactly(distanceFromRoot) | ranges::to<std::vector>
			);

		m_subs[_pathFromRoot.back()]->encodeAllPossibleSubPathsInAssemblyTree(_pathFromRoot, _assembliesOnPath);
	}
}

std::shared_ptr<std::string const> Assembly::sharedSourceName(std::string const& _name) const
{
	if (s_sharedSourceNames.find(_name) == s_sharedSourceNames.end())
		s_sharedSourceNames[_name] = std::make_shared<std::string>(_name);

	return s_sharedSourceNames[_name];
}

AssemblyItem Assembly::namedTag(std::string const& _name, size_t _params, size_t _returns, std::optional<uint64_t> _sourceID)
{
	assertThrow(!_name.empty(), AssemblyException, "Empty named tag.");
	if (m_namedTags.count(_name))
	{
		assertThrow(m_namedTags.at(_name).params == _params, AssemblyException, "");
		assertThrow(m_namedTags.at(_name).returns == _returns, AssemblyException, "");
		assertThrow(m_namedTags.at(_name).sourceID == _sourceID, AssemblyException, "");
	}
	else
		m_namedTags[_name] = {static_cast<size_t>(newTag().data()), _sourceID, _params, _returns};
	return AssemblyItem{Tag, m_namedTags.at(_name).id};
}

AssemblyItem Assembly::newPushLibraryAddress(std::string const& _identifier)
{
	h256 h(util::keccak256(_identifier));
	m_libraries[h] = _identifier;
	return AssemblyItem{PushLibraryAddress, h};
}

AssemblyItem Assembly::newPushImmutable(std::string const& _identifier)
{
	h256 h(util::keccak256(_identifier));
	m_immutables[h] = _identifier;
	return AssemblyItem{PushImmutable, h};
}

AssemblyItem Assembly::newImmutableAssignment(std::string const& _identifier)
{
	h256 h(util::keccak256(_identifier));
	m_immutables[h] = _identifier;
	return AssemblyItem{AssignImmutable, h};
}

AssemblyItem Assembly::newDataLoadN(size_t offset)
{
	return AssemblyItem{DataLoadN, offset};
}

Assembly& Assembly::optimise(OptimiserSettings const& _settings)
{
	optimiseInternal(_settings, {});
	return *this;
}

std::map<u256, u256> const& Assembly::optimiseInternal(
	OptimiserSettings const& _settings,
	std::set<size_t> _tagsReferencedFromOutside
)
{
	if (m_tagReplacements)
		return *m_tagReplacements;

	// Run optimisation for sub-assemblies.
	// TODO: verify and double-check this for EOF.
	for (size_t subId = 0; subId < m_subs.size(); ++subId)
	{
		OptimiserSettings settings = _settings;
		Assembly& sub = *m_subs[subId];
		std::set<size_t> referencedTags;
		for (auto& codeSection: m_codeSections)
			referencedTags += JumpdestRemover::referencedTags(codeSection.items, subId);
		std::map<u256, u256> const& subTagReplacements = sub.optimiseInternal(
			settings,
			referencedTags
		);
		// Apply the replacements (can be empty).
		for (auto& codeSection: m_codeSections)
			BlockDeduplicator::applyTagReplacement(codeSection.items, subTagReplacements, subId);
	}

	std::map<u256, u256> tagReplacements;
	// Iterate until no new optimisation possibilities are found.
	for (unsigned count = 1; count > 0;)
	{
		count = 0;

		if (_settings.runInliner && !m_eofVersion.has_value())
			Inliner{
				m_codeSections.front().items,
				_tagsReferencedFromOutside,
				_settings.expectedExecutionsPerDeployment,
				isCreation(),
				_settings.evmVersion
			}.optimise();

		if (_settings.runJumpdestRemover)
		{
			// TODO: verify this for EOF.
			for (auto& codeSection: m_codeSections)
			{
				JumpdestRemover jumpdestOpt{codeSection.items};
				if (jumpdestOpt.optimise(_tagsReferencedFromOutside))
					count++;
			}
		}

		if (_settings.runPeephole)
		{
			// TODO: verify this for EOF.
			for (auto& codeSection: m_codeSections)
			{
				PeepholeOptimiser peepOpt{codeSection.items};
				while (peepOpt.optimise())
				{
					count++;
					assertThrow(count < 64000, OptimizerException, "Peephole optimizer seems to be stuck.");
				}
			}
		}

		// This only modifies PushTags, we have to run again to actually remove code.
		if (_settings.runDeduplicate && !m_eofVersion.has_value())
			for (auto& section: m_codeSections)
			{
				BlockDeduplicator deduplicator{section.items};
				if (deduplicator.deduplicate())
				{
					for (auto const& replacement: deduplicator.replacedTags())
					{
						assertThrow(
							replacement.first <= std::numeric_limits<size_t>::max() && replacement.second <= std::numeric_limits<size_t>::max(),
							OptimizerException,
							"Invalid tag replacement."
						);
						assertThrow(
							!tagReplacements.count(replacement.first),
							OptimizerException,
							"Replacement already known."
						);
						tagReplacements[replacement.first] = replacement.second;
						if (_tagsReferencedFromOutside.erase(static_cast<size_t>(replacement.first)))
							_tagsReferencedFromOutside.insert(static_cast<size_t>(replacement.second));
					}
					count++;
				}
			}

		// TODO: investigate for EOF
		if (_settings.runCSE && !m_eofVersion.has_value())
		{
			// Control flow graph optimization has been here before but is disabled because it
			// assumes we only jump to tags that are pushed. This is not the case anymore with
			// function types that can be stored in storage.
			AssemblyItems optimisedItems;

			auto& items = m_codeSections.front().items;
			bool usesMSize = ranges::any_of(items, [](AssemblyItem const& _i) {
				return _i == AssemblyItem{Instruction::MSIZE} || _i.type() == VerbatimBytecode;
			});

			auto iter = items.begin();
			while (iter != items.end())
			{
				KnownState emptyState;
				CommonSubexpressionEliminator eliminator{emptyState};
				auto orig = iter;
				iter = eliminator.feedItems(iter, items.end(), usesMSize);
				bool shouldReplace = false;
				AssemblyItems optimisedChunk;
				try
				{
					optimisedChunk = eliminator.getOptimizedItems();
					shouldReplace = (optimisedChunk.size() < static_cast<size_t>(iter - orig));
				}
				catch (StackTooDeepException const&)
				{
					// This might happen if the opcode reconstruction is not as efficient
					// as the hand-crafted code.
				}
				catch (ItemNotAvailableException const&)
				{
					// This might happen if e.g. associativity and commutativity rules
					// reorganise the expression tree, but not all leaves are available.
				}

				if (shouldReplace)
				{
					count++;
					optimisedItems += optimisedChunk;
				}
				else
					copy(orig, iter, back_inserter(optimisedItems));
			}
			if (optimisedItems.size() < items.size())
			{
				items = std::move(optimisedItems);
				count++;
			}
		}
	}

	if (_settings.runConstantOptimiser)
		ConstantOptimisationMethod::optimiseConstants(
			isCreation(),
			isCreation() ? 1 : _settings.expectedExecutionsPerDeployment,
			_settings.evmVersion,
			*this
		);

	m_tagReplacements = std::move(tagReplacements);
	return *m_tagReplacements;
}

namespace
{
uint16_t calcMaxStackHeight(std::vector<AssemblyItem> const& _items, uint16_t _args)
{
	uint16_t maxStackHeight = 0;
	std::stack<size_t> worklist;
	std::vector<int32_t> stack_heights(_items.size(), -1);
	stack_heights[0] = _args;
	worklist.push(0u);
	while (!worklist.empty())
	{
		size_t i = worklist.top();
		worklist.pop();
		AssemblyItem const& item = _items.at(i);
		size_t stack_height_change = item.deposit();
		ptrdiff_t stackHeight = stack_heights.at(i);
		assertThrow(stackHeight != -1, AssemblyException, "");

		std::vector<size_t> successors;

		if (
			item.type() != RelativeJump &&
			!(item.type() == Operation && SemanticInformation::terminatesControlFlow(item.instruction())) &&
			item.type() != RetF &&
			item.type() != ReturnContract &&
			item.type() != JumpF
		)
		{
			assertThrow(i < _items.size() - 1, AssemblyException, "No terminating instruction.");
			successors.emplace_back(i + 1);
		}

		if (item.type() == RelativeJump || item.type() == ConditionalRelativeJump)
		{
			auto it = std::find(_items.begin(), _items.end(), item.tag());
			assertThrow(it != _items.end(), AssemblyException, "Tag not found.");
			successors.emplace_back(static_cast<size_t>(std::distance(_items.begin(), it)));
		}

		maxStackHeight = std::max(maxStackHeight, static_cast<uint16_t>(stackHeight + static_cast<ptrdiff_t>(item.maxStackHeightDelta())));
		stackHeight += static_cast<ptrdiff_t>(stack_height_change);

		for (size_t s: successors)
		{
			if (stack_heights.at(s) == -1)
			{
				stack_heights[s] = static_cast<int32_t>(stackHeight);
				worklist.push(s);
			}
			else
				assertThrow(stack_heights.at(s) == stackHeight, AssemblyException, "Stack height mismatch.");
		}
	}
	return maxStackHeight;
}
}

LinkerObject const& Assembly::assemble() const
{
	assertThrow(!m_invalid, AssemblyException, "Attempted to assemble invalid Assembly object.");
	// Return the already assembled object, if present.
	if (!m_assembledObject.bytecode.empty())
		return m_assembledObject;
	// Otherwise ensure the object is actually clear.
	assertThrow(m_assembledObject.linkReferences.empty(), AssemblyException, "Unexpected link references.");

	LinkerObject& ret = m_assembledObject;

	bool const eof = m_eofVersion.has_value();

	size_t subTagSize = 1;
	std::map<u256, std::pair<std::string, std::vector<size_t>>> immutableReferencesBySub;
	for (auto const& sub: m_subs)
	{
		auto const& linkerObject = sub->assemble();
		if (!linkerObject.immutableReferences.empty())
		{
			assertThrow(
				immutableReferencesBySub.empty(),
				AssemblyException,
				"More than one sub-assembly references immutables."
			);
			immutableReferencesBySub = linkerObject.immutableReferences;
		}
		for (size_t tagPos: sub->m_tagPositionsInBytecode)
			if (tagPos != std::numeric_limits<size_t>::max() && numberEncodingSize(tagPos) > subTagSize)
				subTagSize = numberEncodingSize(tagPos);
	}

	bool setsImmutables = false;
	bool pushesImmutables = false;

	for (auto const& codeSection: m_codeSections)
		for (auto const& i: codeSection.items)
			if (i.type() == AssignImmutable)
			{
				i.setImmutableOccurrences(immutableReferencesBySub[i.data()].second.size());
				setsImmutables = true;
			}
			else if (i.type() == PushImmutable)
				pushesImmutables = true;
	if (setsImmutables || pushesImmutables)
		assertThrow(
			setsImmutables != pushesImmutables,
			AssemblyException,
			"Cannot push and assign immutables in the same assembly subroutine."
		);

	assertThrow(!m_codeSections.empty(), AssemblyException, "Expected at least one code section.");
	assertThrow(eof || m_codeSections.size() == 1, AssemblyException, "Expected exactly one code section in non-EOF code.");
	assertThrow(
		m_codeSections.front().inputs == 0 && m_codeSections.front().outputs == 0x80, AssemblyException,
		"Expected the first code section to have zero inputs and be non-returning."
	);
    
//	unsigned bytesRequiredForCode = codeSize(static_cast<unsigned>(subTagSize));
//	m_tagPositionsInBytecode = std::vector<size_t>(m_usedTags, std::numeric_limits<size_t>::max());
//	std::map<size_t, std::pair<size_t, size_t>> tagRef;
//	std::multimap<h256, unsigned> dataRef;
//	std::multimap<size_t, size_t> subRef;
//	std::vector<unsigned> sizeRef; ///< Pointers to code locations where the size of the program is inserted
//	unsigned bytesPerTag = numberEncodingSize(bytesRequiredForCode);
//	// Adjust bytesPerTag for references to sub assemblies.
//	for (auto&& codeSection: m_codeSections)
//		for (AssemblyItem const& i: codeSection.items)
//			if (i.type() == PushTag)
//			{
//				auto [subId, tagId] = i.splitForeignPushTag();
//				if (subId == std::numeric_limits<size_t>::max())
//					continue;
//				assertThrow(subId < m_subs.size(), AssemblyException, "Invalid sub id");
//				auto subTagPosition = m_subs[subId]->m_tagPositionsInBytecode.at(tagId);
//				assertThrow(subTagPosition != std::numeric_limits<size_t>::max(), AssemblyException, "Reference to tag without position.");
//				bytesPerTag = std::max(bytesPerTag, numberEncodingSize(subTagPosition));
//			}
//	uint8_t tagPush = static_cast<uint8_t>(pushInstruction(bytesPerTag));
    
	// TODO: assert zero inputs/outputs on code section zero
	// TODO: assert one code section being present and *only* one being present unless EOF

	unsigned bytesRequiredForSubs = 0;
	// TODO: consider fully producing all sub and data refs in this pass already.
	for (auto&& codeSection: m_codeSections)
		for (AssemblyItem const& i: codeSection.items)
			if (i.type() == PushSub || i.type() == EofCreate || i.type() == ReturnContract)
				bytesRequiredForSubs += static_cast<unsigned>(subAssemblyById(static_cast<size_t>(i.data()))->assemble().bytecode.size());
	unsigned bytesRequiredForDataUpperBound = static_cast<unsigned>(m_auxiliaryData.size());

	std::optional<size_t> maxDataLoadNOffset = std::nullopt;
	for (auto&& codeSection: m_codeSections)
		for (AssemblyItem const& i: codeSection.items)
			if (i.type() == DataLoadN)
			{
				const auto offset = static_cast<size_t>(i.data());
				if (!maxDataLoadNOffset.has_value() || offset > maxDataLoadNOffset.value())
					maxDataLoadNOffset = offset;

			}

	bytesRequiredForDataUpperBound += maxDataLoadNOffset.has_value() ? (maxDataLoadNOffset.value() + 32) : 0;

	// Some of these may be unreferenced and not actually end up in data.
	for (auto const& dataItem: m_data)
		bytesRequiredForDataUpperBound += static_cast<unsigned>(dataItem.second.size());
	unsigned bytesRequiredForDataAndSubsUpperBound = bytesRequiredForDataUpperBound + bytesRequiredForSubs;

	static auto setBigEndian = [](bytes& _dest, size_t _offset, size_t _size, auto _value) {
		assertThrow(numberEncodingSize(_value) <= _size, AssemblyException, "");
		toBigEndian(_value, bytesRef(_dest.data() + _offset, _size));
	};
	static auto appendBigEndian = [](bytes& _dest, size_t _size, auto _value) {
		_dest.resize(_dest.size() + _size);
		setBigEndian(_dest, _dest.size() - _size, _size, _value);
	};
	static auto appendBigEndianUint16 = [](bytes& _dest, auto _value) {
		static_assert(!std::numeric_limits<decltype(_value)>::is_signed, "only unsigned types or bigint supported");
		assertThrow(_value <= 0xFFFF, AssemblyException, "");
		appendBigEndian(_dest, 2, static_cast<size_t>(_value));
	};
	std::vector<size_t> codeSectionSizeOffsets;
	auto setCodeSectionSize = [&](size_t _section, size_t _size) {
		if (eof)
			toBigEndian(_size, bytesRef(ret.bytecode.data() + codeSectionSizeOffsets.at(_section), 2));
	};
	std::optional<size_t> dataSectionSizeOffset;
	auto setDataSectionSize = [&](size_t _size) {
		if (eof)
		{
			assertThrow(dataSectionSizeOffset.has_value(), AssemblyException, "");
			assertThrow(_size <= 0xFFFF, AssemblyException, "Invalid data section size.");
			toBigEndian(_size, bytesRef(ret.bytecode.data() + *dataSectionSizeOffset, 2));
		}
	};

	size_t startOfContainerSectionHeader = 0;

	// Insert EOF1 header.
	if (eof)
	{
		ret.bytecode.push_back(0xef);
		ret.bytecode.push_back(0x00);
		ret.bytecode.push_back(0x01); // version 1

		ret.bytecode.push_back(0x01);									 // kind=type
		appendBigEndianUint16(ret.bytecode, m_codeSections.size() * 4u); // length of type section

		ret.bytecode.push_back(0x02);								// kind=code
		appendBigEndianUint16(ret.bytecode, m_codeSections.size()); // placeholder for number of code sections

		for (auto const& codeSection: m_codeSections)
		{
			(void) codeSection;
			codeSectionSizeOffsets.emplace_back(ret.bytecode.size());
			appendBigEndianUint16(ret.bytecode, 0u); // placeholder for length of code
		}

		startOfContainerSectionHeader = ret.bytecode.size();
//		if (!m_subs.empty())
//		{
//			ret.bytecode.push_back(0x03);
//			containerSectionNumOffset = ret.bytecode.size();
//			appendBigEndianUint16(ret.bytecode, 0xFFFFu);
//			containerSectionSizeOffset = ret.bytecode.size();
//			appendBigEndianUint16(ret.bytecode, 0u); // length of sub containers section
//		}

		ret.bytecode.push_back(0x04); // kind=data
		dataSectionSizeOffset = ret.bytecode.size();
		appendBigEndianUint16(ret.bytecode, 0u); // length of data

		ret.bytecode.push_back(0x00); // terminator

		for (auto const& codeSection: m_codeSections)
		{
			ret.bytecode.push_back(codeSection.inputs);
			ret.bytecode.push_back(codeSection.outputs);
			appendBigEndianUint16(ret.bytecode, calcMaxStackHeight(codeSection.items, codeSection.inputs));
		}
	}

	unsigned headerSize = static_cast<unsigned>(ret.bytecode.size());
	unsigned bytesRequiredForCode = codeSize(static_cast<unsigned>(subTagSize));
	m_tagPositionsInBytecode = std::vector<size_t>(m_usedTags, std::numeric_limits<size_t>::max());
	struct TagRef
	{
		size_t subId = 0;
		size_t tagId = 0;
		bool isRelative = 0;
	};
	std::map<size_t, TagRef> tagRef;
	std::multimap<h256, unsigned> dataRef;
	std::multimap<size_t, size_t> subRef;
	std::vector<unsigned> sizeRef; ///< Pointers to code locations where the size of the program is inserted
	unsigned bytesPerTag = numberEncodingSize(headerSize + bytesRequiredForCode + bytesRequiredForDataUpperBound);
	uint8_t tagPush = static_cast<uint8_t>(pushInstruction(bytesPerTag));

	if (eof)
	{
		bytesPerTag = 2;
		tagPush = static_cast<uint8_t>(Instruction::INVALID);
	}
	else
		++bytesRequiredForCode; ///< Additional INVALID marker.

	unsigned bytesRequiredIncludingDataAndSubsUpperBound = headerSize + bytesRequiredForCode + bytesRequiredForDataAndSubsUpperBound;
	unsigned bytesPerDataRef = !eof ? numberEncodingSize(bytesRequiredIncludingDataAndSubsUpperBound) : 1;
	uint8_t dataRefPush = static_cast<uint8_t>(pushInstruction(bytesPerDataRef));
	ret.bytecode.reserve(bytesRequiredIncludingDataAndSubsUpperBound);

	for (auto&& [codeSectionIndex, codeSection]: m_codeSections | ranges::views::enumerate)
	{
		auto const sectionStart = ret.bytecode.size();

		for (AssemblyItem const& i: codeSection.items)
		{
			// store position of the invalid jump destination
			if (i.type() != Tag && m_tagPositionsInBytecode[0] == std::numeric_limits<size_t>::max())
				m_tagPositionsInBytecode[0] = ret.bytecode.size();

			switch (i.type())
			{
				case Operation:
					if (i.instruction() == Instruction::RETURNCONTRACT || i.instruction() == Instruction::EOFCREATE)
					{
						(void)i;
					}
					ret.bytecode.push_back(static_cast<uint8_t>(i.instruction()));
					break;
				case Push:
				{
					unsigned b = numberEncodingSize(i.data());
					if (b == 0 && !m_evmVersion.hasPush0())
					{
						b = 1;
					}
					ret.bytecode.push_back(static_cast<uint8_t>(pushInstruction(b)));
					if (b > 0)
					{
						ret.bytecode.resize(ret.bytecode.size() + b);
						bytesRef byr(&ret.bytecode.back() + 1 - b, b);
						toBigEndian(i.data(), byr);
					}
					break;
				}
				case PushTag:
				{
					assertThrow(!eof, AssemblyException, "Push tag in EOF code");
					ret.bytecode.push_back(tagPush);
					auto [subId, tagId] = i.splitForeignPushTag();
					tagRef[ret.bytecode.size()] = TagRef{subId, tagId, false};
					ret.bytecode.resize(ret.bytecode.size() + bytesPerTag);
					break;
				}
				case PushData:
					// assertThrow(!eof, AssemblyException, "Push data in EOF code");
					ret.bytecode.push_back(dataRefPush);
					dataRef.insert(std::make_pair(h256(i.data()), ret.bytecode.size()));
					ret.bytecode.resize(ret.bytecode.size() + bytesPerDataRef);
					break;
				case PushSub:
					assertThrow(!eof, AssemblyException, "Push sub in EOF code");
					assertThrow(i.data() <= std::numeric_limits<size_t>::max(), AssemblyException, "");
					ret.bytecode.push_back(dataRefPush);
					subRef.insert(std::make_pair(static_cast<size_t>(i.data()), ret.bytecode.size()));
					ret.bytecode.resize(ret.bytecode.size() + bytesPerDataRef);
					break;
				case PushSubSize:
				{
					assertThrow(!eof, AssemblyException, "Push sub size in EOF code");
					assertThrow(i.data() <= std::numeric_limits<size_t>::max(), AssemblyException, "");
					auto s = subAssemblyById(static_cast<size_t>(i.data()))->assemble().bytecode.size();
					i.setPushedValue(u256(s));
					unsigned b = std::max<unsigned>(1, numberEncodingSize(s));
					ret.bytecode.push_back(static_cast<uint8_t>(pushInstruction(b)));
					ret.bytecode.resize(ret.bytecode.size() + b);
					bytesRef byr(&ret.bytecode.back() + 1 - b, b);
					toBigEndian(s, byr);
					break;
				}
				case PushProgramSize:
				{
					assertThrow(!eof, AssemblyException, "Push program size in EOF code");
					ret.bytecode.push_back(dataRefPush);
					sizeRef.push_back(static_cast<unsigned>(ret.bytecode.size()));
					ret.bytecode.resize(ret.bytecode.size() + bytesPerDataRef);
					break;
				}
				case PushLibraryAddress:
					ret.bytecode.push_back(static_cast<uint8_t>(Instruction::PUSH20));
					ret.linkReferences[ret.bytecode.size()] = m_libraries.at(i.data());
					ret.bytecode.resize(ret.bytecode.size() + 20);
					break;
				case PushImmutable:
					assertThrow(!eof, AssemblyException, "Push immutable in EOF code");
					ret.bytecode.push_back(static_cast<uint8_t>(Instruction::PUSH32));
					// Maps keccak back to the "identifier" std::string of that immutable.
					ret.immutableReferences[i.data()].first = m_immutables.at(i.data());
					// Record the bytecode offset of the PUSH32 argument.
					ret.immutableReferences[i.data()].second.emplace_back(ret.bytecode.size());
					// Advance bytecode by 32 bytes (default initialized).
					ret.bytecode.resize(ret.bytecode.size() + 32);
					break;
				case VerbatimBytecode:
					ret.bytecode += i.verbatimData();
					break;
				case AssignImmutable:
				{
					assertThrow(!eof, AssemblyException, "Assign immutable in EOF code");
					// Expect 2 elements on stack (source, dest_base)
					auto const& offsets = immutableReferencesBySub[i.data()].second;
					for (auto [j, offset]: offsets | ranges::views::enumerate)
					{
						if (j != offsets.size() - 1)
						{
							ret.bytecode.push_back(uint8_t(Instruction::DUP2));
							ret.bytecode.push_back(uint8_t(Instruction::DUP2));
						}
						// TODO: should we make use of the constant optimizer methods for pushing the offsets?
						bytes offsetBytes = toCompactBigEndian(u256(offset));
						ret.bytecode.push_back(static_cast<uint8_t>(pushInstruction(static_cast<unsigned>(offsetBytes.size()))));
						ret.bytecode += offsetBytes;
						ret.bytecode.push_back(uint8_t(Instruction::ADD));
						ret.bytecode.push_back(uint8_t(Instruction::MSTORE));
					}
					if (offsets.empty())
					{
						ret.bytecode.push_back(uint8_t(Instruction::POP));
						ret.bytecode.push_back(uint8_t(Instruction::POP));
					}
					immutableReferencesBySub.erase(i.data());
					break;
				}
				case DataLoadN:
				{
					ret.bytecode.push_back(uint8_t(Instruction::DATALOADN));
					appendBigEndianUint16(ret.bytecode, i.data());
					break;
				}
				case PushDeployTimeAddress:
					ret.bytecode.push_back(static_cast<uint8_t>(Instruction::PUSH20));
					ret.bytecode.resize(ret.bytecode.size() + 20);
					break;
				case Tag:
				{
					assertThrow(i.data() != 0, AssemblyException, "Invalid tag position.");
					assertThrow(i.splitForeignPushTag().first == std::numeric_limits<size_t>::max(), AssemblyException, "Foreign tag.");
					size_t tagId = static_cast<size_t>(i.data());
					assertThrow(ret.bytecode.size() < 0xffffffffL, AssemblyException, "Tag too large.");
					assertThrow(m_tagPositionsInBytecode[tagId] == std::numeric_limits<size_t>::max(), AssemblyException, "Duplicate tag position.");
					m_tagPositionsInBytecode[tagId] = ret.bytecode.size();
					if (!eof)
						ret.bytecode.push_back(static_cast<uint8_t>(Instruction::JUMPDEST));
					break;
				}
				case CallF:
				{
					assertThrow(eof, AssemblyException, "Function call (CALLF) in non-EOF code");
					ret.bytecode.push_back(static_cast<uint8_t>(Instruction::CALLF));
					appendBigEndianUint16(ret.bytecode, i.data());
					break;
				}
				case JumpF:
				{
					assertThrow(eof, AssemblyException, "Function call (JUMPF) in non-EOF code");
					ret.bytecode.push_back(static_cast<uint8_t>(Instruction::JUMPF));
					appendBigEndianUint16(ret.bytecode, i.data());
					break;
				}
				case RetF:
				{
					assertThrow(eof, AssemblyException, "Function return (RETF) in non-EOF code");
					ret.bytecode.push_back(static_cast<uint8_t>(Instruction::RETF));
					break;
				}
				case EofCreate:
				{
					assertThrow(eof, AssemblyException, "Eof create (EOFCREATE) in non-EOF code");
					ret.bytecode.push_back(static_cast<uint8_t>(Instruction::EOFCREATE));
					subRef.insert(std::make_pair(static_cast<size_t>(i.data()), ret.bytecode.size()));
					ret.bytecode.push_back(static_cast<uint8_t>(i.data()));
					break;
				}
				case ReturnContract:
				{
					assertThrow(eof, AssemblyException, "Return contract (RETURNCONTRACT) in non-EOF code");
					ret.bytecode.push_back(static_cast<uint8_t>(Instruction::RETURNCONTRACT));
					subRef.insert(std::make_pair(static_cast<size_t>(i.data()), ret.bytecode.size()));
					ret.bytecode.push_back(static_cast<uint8_t>(i.data()));
					break;
				}
				case RelativeJump:
				case ConditionalRelativeJump:
				{
					assertThrow(eof, AssemblyException, "Relative jump in non-EOF code");
					ret.bytecode.push_back(static_cast<uint8_t>(i.type() == RelativeJump ? Instruction::RJUMP : Instruction::RJUMPI));
					auto [subId, tagId] = i.splitForeignPushTag();
					tagRef[ret.bytecode.size()] = TagRef{subId, tagId, true};
					appendBigEndianUint16(ret.bytecode, 0u);
					break;
				}
				default:
					assertThrow(false, InvalidOpcode, "Unexpected opcode while assembling.");
			}
		}

		auto sectionEnd = ret.bytecode.size();

		setCodeSectionSize(codeSectionIndex, sectionEnd - sectionStart);
	}

	if (!immutableReferencesBySub.empty())
		throw
			langutil::Error(
				1284_error,
				langutil::Error::Type::CodeGenerationError,
				"Some immutables were read from but never assigned, possibly because of optimization."
			);

	if (!eof && (!m_subs.empty() || !m_data.empty() || !m_auxiliaryData.empty()))
		// Append an INVALID here to help tests find miscompilation.
		ret.bytecode.push_back(static_cast<uint8_t>(Instruction::INVALID));

	std::map<LinkerObject, size_t> subAssemblyOffsets;
	std::map<size_t, size_t> containerSizes;
	for (auto const& [subIdPath, bytecodeOffset]: subRef)
	{
		LinkerObject subObject = subAssemblyById(subIdPath)->assemble();
		bytesRef r(ret.bytecode.data() + bytecodeOffset, bytesPerDataRef);

		// In order for de-duplication to kick in, not only must the bytecode be identical, but
		// link and immutables references as well.
		const auto it = subAssemblyOffsets.find(subObject);
		if (it != subAssemblyOffsets.end())
		{
			if (!eof)
				toBigEndian(it->second, r);
			else
				r[0] = static_cast<uint8_t>(it->second);
		}
		else
		{
			if (!eof)
				toBigEndian(ret.bytecode.size(), r);
			else
				r[0] = static_cast<uint8_t>(subIdPath);

			subAssemblyOffsets[subObject] = !eof ? ret.bytecode.size() : subIdPath;
			ret.bytecode += subObject.bytecode;
			containerSizes[subIdPath] = subObject.bytecode.size();
		}
		for (auto const& ref: subObject.linkReferences)
			ret.linkReferences[ref.first + subAssemblyOffsets[subObject]] = ref.second;
	}

	for (auto const& [bytecodeOffset, ref]: tagRef)
	{
		size_t subId = ref.subId;
		size_t tagId = ref.tagId;
		bool relative = ref.isRelative;
		assertThrow(subId == std::numeric_limits<size_t>::max() || subId < m_subs.size(), AssemblyException, "Invalid sub id");
		std::vector<size_t> const& tagPositions =
			subId == std::numeric_limits<size_t>::max() ?
			m_tagPositionsInBytecode :
			m_subs[subId]->m_tagPositionsInBytecode;
		assertThrow(tagId < tagPositions.size(), AssemblyException, "Reference to non-existing tag.");
		size_t pos = tagPositions[tagId];
		assertThrow(pos != std::numeric_limits<size_t>::max(), AssemblyException, "Reference to tag without position.");
		assertThrow(numberEncodingSize(pos) <= bytesPerTag, AssemblyException, "Tag too large for reserved space.");
		if (relative)
		{
			assertThrow(m_eofVersion.has_value(), AssemblyException, "Relative jump outside EOF");
			assertThrow(subId == std::numeric_limits<size_t>::max(), AssemblyException, "Relative jump to sub");
			assertThrow(
				static_cast<ptrdiff_t>(pos) - static_cast<ptrdiff_t>(bytecodeOffset + 2u) < 0x7FFF &&
				static_cast<ptrdiff_t>(pos) - static_cast<ptrdiff_t>(bytecodeOffset + 2u) >= -0x8000,
				AssemblyException,
				"Relative jump too far"
			);
			toBigEndian(pos - (bytecodeOffset + 2u), bytesRef(ret.bytecode.data() + bytecodeOffset, 2));
		}
		else
		{
			assertThrow(!m_eofVersion.has_value(), AssemblyException, "Dynamic tag reference within EOF");
			toBigEndian(pos, bytesRef(ret.bytecode.data() + bytecodeOffset, bytesPerTag));
		}
	}
	for (auto const& [name, tagInfo]: m_namedTags)
	{
		size_t position = m_tagPositionsInBytecode.at(tagInfo.id);
		std::optional<size_t> tagIndex;
		for (auto& codeSection: m_codeSections)
			for (auto&& [index, item]: codeSection.items | ranges::views::enumerate)
				if (item.type() == Tag && static_cast<size_t>(item.data()) == tagInfo.id)
				{
					tagIndex = index;
					break;
				}
		ret.functionDebugData[name] = {
			position == std::numeric_limits<size_t>::max() ? std::nullopt : std::optional<size_t>{position},
			tagIndex,
			tagInfo.sourceID,
			tagInfo.params,
			tagInfo.returns
		};
	}

	if (eof)
	{
		// Fill the num_container_sections
		const auto numContainers = subAssemblyOffsets.size();
		if (numContainers > 0)
		{
			bytes containerSectionHeader = {};
			containerSectionHeader.push_back(0x03);
			appendBigEndianUint16(containerSectionHeader, numContainers);

			assertThrow(numContainers == containerSizes.size(), AssemblyException, "Invalid container size");

			for (auto s : containerSizes)
				appendBigEndianUint16(containerSectionHeader, s.second);

			ret.bytecode.insert(ret.bytecode.begin() + static_cast<int64_t>(startOfContainerSectionHeader),
								containerSectionHeader.begin(), containerSectionHeader.end());

			assertThrow(dataSectionSizeOffset.has_value(), AssemblyException, "Invalid data section size offset");
			dataSectionSizeOffset.value() += containerSectionHeader.size();
		}
		else
			assertThrow(0 == containerSizes.size(), AssemblyException, "Invalid container size");
	}

	auto const dataStart = ret.bytecode.size();

	for (auto const& dataItem: m_data)
	{
		auto references = dataRef.equal_range(dataItem.first);
		if (references.first == references.second)
			continue;
		for (auto ref = references.first; ref != references.second; ++ref)
			toBigEndian(ret.bytecode.size(), bytesRef(ret.bytecode.data() + ref->second, bytesPerDataRef));
		ret.bytecode += dataItem.second;
	}

	ret.bytecode += m_auxiliaryData;

	for (unsigned pos: sizeRef)
		setBigEndian(ret.bytecode, pos, bytesPerDataRef, ret.bytecode.size());

	auto dataLength = ret.bytecode.size() - dataStart + (maxDataLoadNOffset.has_value() ? (maxDataLoadNOffset.value() + 32) : 0);
	assertThrow(
		bytesRequiredForDataAndSubsUpperBound >= dataLength,
		AssemblyException,
		"More data than expected. " + std::to_string(dataLength) + " > " + std::to_string(bytesRequiredForDataUpperBound)
	);
	setDataSectionSize(dataLength);

	return ret;
}

std::vector<size_t> Assembly::decodeSubPath(size_t _subObjectId) const
{
	if (_subObjectId < m_subs.size())
		return {_subObjectId};

	auto subIdPathIt = find_if(
		m_subPaths.begin(),
		m_subPaths.end(),
		[_subObjectId](auto const& subId) { return subId.second == _subObjectId; }
	);

	assertThrow(subIdPathIt != m_subPaths.end(), AssemblyException, "");
	return subIdPathIt->first;
}

size_t Assembly::encodeSubPath(std::vector<size_t> const& _subPath)
{
	assertThrow(!_subPath.empty(), AssemblyException, "");
	if (_subPath.size() == 1)
	{
		assertThrow(_subPath[0] < m_subs.size(), AssemblyException, "");
		return _subPath[0];
	}

	if (m_subPaths.find(_subPath) == m_subPaths.end())
	{
		size_t objectId = std::numeric_limits<size_t>::max() - m_subPaths.size();
		assertThrow(objectId >= m_subs.size(), AssemblyException, "");
		m_subPaths[_subPath] = objectId;
	}

	return m_subPaths[_subPath];
}

Assembly const* Assembly::subAssemblyById(size_t _subId) const
{
	std::vector<size_t> subIds = decodeSubPath(_subId);
	Assembly const* currentAssembly = this;
	for (size_t currentSubId: subIds)
	{
		currentAssembly = currentAssembly->m_subs.at(currentSubId).get();
		assertThrow(currentAssembly, AssemblyException, "");
	}

	assertThrow(currentAssembly != this, AssemblyException, "");
	return currentAssembly;
}

Assembly::OptimiserSettings Assembly::OptimiserSettings::translateSettings(frontend::OptimiserSettings const& _settings, langutil::EVMVersion const& _evmVersion)
{
	// Constructing it this way so that we notice changes in the fields.
	evmasm::Assembly::OptimiserSettings asmSettings{false,  false, false, false, false, false, _evmVersion, 0};
	asmSettings.runInliner = _settings.runInliner;
	asmSettings.runJumpdestRemover = _settings.runJumpdestRemover;
	asmSettings.runPeephole = _settings.runPeephole;
	asmSettings.runDeduplicate = _settings.runDeduplicate;
	asmSettings.runCSE = _settings.runCSE;
	asmSettings.runConstantOptimiser = _settings.runConstantOptimiser;
	asmSettings.expectedExecutionsPerDeployment = _settings.expectedExecutionsPerDeployment;
	asmSettings.evmVersion = _evmVersion;
	return asmSettings;
}
