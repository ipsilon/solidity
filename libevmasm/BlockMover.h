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
* @file BlockMover.h
* @author rodiazer <c@ethdev.com>
* @date 2024
* Move blocks to after jumps to them.
*/

#pragma once

#include <libsolutil/Common.h>
#include <libsolutil/Numeric.h>


#include <cstddef>
#include <vector>
#include <functional>
#include <map>

namespace solidity::evmasm
{

class Assembly;
class AssemblyItem;
using AssemblyItems = std::vector<AssemblyItem>;

class BlockMover
{
public:
	//explicit BlockMover(AssemblyItems& _items, std::function<AssemblyItem()> _newTagGenerator):
	explicit BlockMover(AssemblyItems& _items):
	m_items(_items) {}
	/// @returns true if something was changed
	bool move();

private:

	std::map<std::pair<ptrdiff_t, ptrdiff_t>, std::vector<AssemblyItem*>> m_blocksToMove;
	AssemblyItems& m_items;
	// std::function<AssemblyItem()> m_newTagGenerator;
};

}
