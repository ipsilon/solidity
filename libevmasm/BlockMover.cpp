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
/**
* @file BlockDeduplicator.cpp
* @author Christian <c@ethdev.com>
* @date 2015
* Unifies basic blocks that share content.
*/

#include <libevmasm/BlockMover.h>

#include <libevmasm/AssemblyItem.h>
#include <libevmasm/SemanticInformation.h>

#include <functional>
#include <set>
#include <range/v3/view/reverse.hpp>

using namespace solidity;
using namespace solidity::evmasm;

namespace
{

struct Block
{
	std::set<Block*> entries;
	std::set<Block*> children;
	AssemblyItems items;
};

class ControlFlowGraph
{
	std::list<Block> m_blocks;
	Block* m_entry = {};

public:
	static ControlFlowGraph build(AssemblyItems const& items)
	{
		ControlFlowGraph cfg;

		std::map<AssemblyItem, Block*> blocks;

		auto const rootTag = AssemblyItem(Tag, std::numeric_limits<u256>::max());

		Block* current = &cfg.m_blocks.emplace_back(Block{{}, {}, {}});
		blocks.insert({rootTag, current});

		cfg.m_entry = current;

		for (size_t i = 0; i < items.size(); ++i)
		{
			auto const& item = items[i];

			if (item.type() == Tag)
			{
				auto newBlockIt = blocks.find(item.tag());
				if (newBlockIt != blocks.end())
				{
					assertThrow(newBlockIt->second->items.empty(), AssemblyException, "Invalid block. Block already filled");
					current = newBlockIt->second;
				}
				else
				{
					current = &cfg.m_blocks.emplace_back(Block{{}, {}, {}});
					blocks.insert({rootTag, current});
				}
			}

			current->items.push_back(item);

			if(item.type() == RelativeJump || item.type() == ConditionalRelativeJump)
			{
				assertThrow(item.type() != RelativeJump || i + 1 == items.size() || items[i + 1].type() == Tag, AssemblyException, "");
				assertThrow(item.type() != ConditionalRelativeJump || i + 1 < items.size() || items[i + 1].type() == RelativeJump, AssemblyException, "");

				auto childIt = blocks.find(item.tag());
				if (childIt != blocks.end())
					childIt->second->entries.insert(current);
				else
				{
					auto* child = &cfg.m_blocks.emplace_back(Block{{current}, {}, {}});
					childIt = blocks.insert({item.tag(), child}).first;
				}

				current->children.insert(childIt->second);
			}
		}

		return cfg;
	}

	void sort(AssemblyItems& output) const
	{
		std::vector<const Block*> sorted_blocks;
		std::set<const Block*> visited;

		std::function<void(const Block* block)> dfs = [&](const Block* block){
			visited.insert(block);
			for (auto const& child_block: block->children)
			{
				if (!visited.count(child_block))
					dfs(child_block);
			}
			sorted_blocks.push_back(block);
		};

		for (auto const& block: m_blocks)
		{
			if (!visited.count(&block))
				dfs(&block);
		}


		if (sorted_blocks[0]->items[0].type() == Tag && sorted_blocks[0]->items[0].data() == 209)
			(void)sorted_blocks;

		for (auto const& block: sorted_blocks | ranges::views::reverse)
		{
			for (auto&& item: block->items)
				output.emplace_back(item);
		}
	}
};
}

bool BlockMover::move()
{
	auto cfg = ControlFlowGraph::build(m_items);
	m_items.clear();
	cfg.sort(m_items);

	return true;
}
