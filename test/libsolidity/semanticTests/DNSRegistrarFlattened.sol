
// Sources flattened with hardhat v2.12.2 https://hardhat.org

// File contracts/dnssec-oracle/DNSSEC.sol

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;
pragma experimental ABIEncoderV2;

abstract contract DNSSEC {
    bytes public anchors;

    struct RRSetWithSignature {
        bytes rrset;
        bytes sig;
    }

    event AlgorithmUpdated(uint8 id, address addr);
    event DigestUpdated(uint8 id, address addr);

    function verifyRRSet(
        RRSetWithSignature[] memory input
    ) external view virtual returns (bytes memory rrs, uint32 inception);

    function verifyRRSet(
        RRSetWithSignature[] memory input,
        uint256 now
    ) public view virtual returns (bytes memory rrs, uint32 inception);
}


// File contracts/registry/ENS.sol


pragma solidity >=0.8.4;

interface ENS {
    // Logged when the owner of a node assigns a new owner to a subnode.
    event NewOwner(bytes32 indexed node, bytes32 indexed label, address owner);

    // Logged when the owner of a node transfers ownership to a new account.
    event Transfer(bytes32 indexed node, address owner);

    // Logged when the resolver for a node changes.
    event NewResolver(bytes32 indexed node, address resolver);

    // Logged when the TTL of a node changes
    event NewTTL(bytes32 indexed node, uint64 ttl);

    // Logged when an operator is added or removed.
    event ApprovalForAll(
        address indexed owner,
        address indexed operator,
        bool approved
    );

    function setRecord(
        bytes32 node,
        address owner,
        address resolver,
        uint64 ttl
    ) external;

    function setSubnodeRecord(
        bytes32 node,
        bytes32 label,
        address owner,
        address resolver,
        uint64 ttl
    ) external;

    function setSubnodeOwner(
        bytes32 node,
        bytes32 label,
        address owner
    ) external returns (bytes32);

    function setResolver(bytes32 node, address resolver) external;

    function setOwner(bytes32 node, address owner) external;

    function setTTL(bytes32 node, uint64 ttl) external;

    function setApprovalForAll(address operator, bool approved) external;

    function owner(bytes32 node) external view returns (address);

    function resolver(bytes32 node) external view returns (address);

    function ttl(bytes32 node) external view returns (uint64);

    function recordExists(bytes32 node) external view returns (bool);

    function isApprovedForAll(
        address owner,
        address operator
    ) external view returns (bool);
}


// File contracts/reverseRegistrar/IReverseRegistrar.sol

pragma solidity >=0.8.4;

interface IReverseRegistrar {
    function setDefaultResolver(address resolver) external;

    function claim(address owner) external returns (bytes32);

    function claimForAddr(
        address addr,
        address owner,
        address resolver
    ) external returns (bytes32);

    function claimWithResolver(
        address owner,
        address resolver
    ) external returns (bytes32);

    function setName(string memory name) external returns (bytes32);

    function setNameForAddr(
        address addr,
        address owner,
        address resolver,
        string memory name
    ) external returns (bytes32);

    function node(address addr) external pure returns (bytes32);
}


// File @openzeppelin/contracts/utils/Context.sol@v4.8.0

// OpenZeppelin Contracts v4.4.1 (utils/Context.sol)

pragma solidity ^0.8.0;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}


// File @openzeppelin/contracts/access/Ownable.sol@v4.8.0

// OpenZeppelin Contracts (last updated v4.7.0) (access/Ownable.sol)

pragma solidity ^0.8.0;

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}


// File contracts/root/Controllable.sol

pragma solidity ^0.8.4;

contract Controllable is Ownable {
    mapping(address => bool) public controllers;

    event ControllerChanged(address indexed controller, bool enabled);

    modifier onlyController() {
        require(
            controllers[msg.sender],
            "Controllable: Caller is not a controller"
        );
        _;
    }

    function setController(address controller, bool enabled) public onlyOwner {
        controllers[controller] = enabled;
        emit ControllerChanged(controller, enabled);
    }
}


// File contracts/reverseRegistrar/ReverseRegistrar.sol

pragma solidity >=0.8.4;




abstract contract NameResolver {
    function setName(bytes32 node, string memory name) public virtual;
}

bytes32 constant lookup = 0x3031323334353637383961626364656600000000000000000000000000000000;

bytes32 constant ADDR_REVERSE_NODE = 0x91d1777781884d03a6757a803996e38de2a42967fb37eeaca72729271025a9e2;

// namehash('addr.reverse')

contract ReverseRegistrar is Ownable, Controllable, IReverseRegistrar {
    ENS public immutable ens;
    NameResolver public defaultResolver;

    event ReverseClaimed(address indexed addr, bytes32 indexed node);
    event DefaultResolverChanged(NameResolver indexed resolver);

    /**
     * @dev Constructor
     * @param ensAddr The address of the ENS registry.
     */
    constructor(ENS ensAddr) {
        ens = ensAddr;

        // Assign ownership of the reverse record to our deployer
        ReverseRegistrar oldRegistrar = ReverseRegistrar(
            ensAddr.owner(ADDR_REVERSE_NODE)
        );
        if (address(oldRegistrar) != address(0x0)) {
            oldRegistrar.claim(msg.sender);
        }
    }

    modifier authorised(address addr) {
        require(
            addr == msg.sender ||
            controllers[msg.sender] ||
            ens.isApprovedForAll(addr, msg.sender) ||
            ownsContract(addr),
            "ReverseRegistrar: Caller is not a controller or authorised by address or the address itself"
        );
        _;
    }

    function setDefaultResolver(address resolver) public override onlyOwner {
        require(
            address(resolver) != address(0),
            "ReverseRegistrar: Resolver address must not be 0"
        );
        defaultResolver = NameResolver(resolver);
        emit DefaultResolverChanged(NameResolver(resolver));
    }

    /**
     * @dev Transfers ownership of the reverse ENS record associated with the
     *      calling account.
     * @param owner The address to set as the owner of the reverse record in ENS.
     * @return The ENS node hash of the reverse record.
     */
    function claim(address owner) public override returns (bytes32) {
        return claimForAddr(msg.sender, owner, address(defaultResolver));
    }

    /**
     * @dev Transfers ownership of the reverse ENS record associated with the
     *      calling account.
     * @param addr The reverse record to set
     * @param owner The address to set as the owner of the reverse record in ENS.
     * @param resolver The resolver of the reverse node
     * @return The ENS node hash of the reverse record.
     */
    function claimForAddr(
        address addr,
        address owner,
        address resolver
    ) public override authorised(addr) returns (bytes32) {
        bytes32 labelHash = sha3HexAddress(addr);
        bytes32 reverseNode = keccak256(
            abi.encodePacked(ADDR_REVERSE_NODE, labelHash)
        );
        emit ReverseClaimed(addr, reverseNode);
        ens.setSubnodeRecord(ADDR_REVERSE_NODE, labelHash, owner, resolver, 0);
        return reverseNode;
    }

    /**
     * @dev Transfers ownership of the reverse ENS record associated with the
     *      calling account.
     * @param owner The address to set as the owner of the reverse record in ENS.
     * @param resolver The address of the resolver to set; 0 to leave unchanged.
     * @return The ENS node hash of the reverse record.
     */
    function claimWithResolver(
        address owner,
        address resolver
    ) public override returns (bytes32) {
        return claimForAddr(msg.sender, owner, resolver);
    }

    /**
     * @dev Sets the `name()` record for the reverse ENS record associated with
     * the calling account. First updates the resolver to the default reverse
     * resolver if necessary.
     * @param name The name to set for this address.
     * @return The ENS node hash of the reverse record.
     */
    function setName(string memory name) public override returns (bytes32) {
        return
            setNameForAddr(
            msg.sender,
            msg.sender,
            address(defaultResolver),
            name
        );
    }

    /**
     * @dev Sets the `name()` record for the reverse ENS record associated with
     * the account provided. Updates the resolver to a designated resolver
     * Only callable by controllers and authorised users
     * @param addr The reverse record to set
     * @param owner The owner of the reverse node
     * @param resolver The resolver of the reverse node
     * @param name The name to set for this address.
     * @return The ENS node hash of the reverse record.
     */
    function setNameForAddr(
        address addr,
        address owner,
        address resolver,
        string memory name
    ) public override returns (bytes32) {
        bytes32 node = claimForAddr(addr, owner, resolver);
        NameResolver(resolver).setName(node, name);
        return node;
    }

    /**
     * @dev Returns the node hash for a given account's reverse records.
     * @param addr The address to hash
     * @return The ENS node hash.
     */
    function node(address addr) public pure override returns (bytes32) {
        return
            keccak256(
            abi.encodePacked(ADDR_REVERSE_NODE, sha3HexAddress(addr))
        );
    }

    /**
     * @dev An optimised function to compute the sha3 of the lower-case
     *      hexadecimal representation of an Ethereum address.
     * @param addr The address to hash
     * @return ret The SHA3 hash of the lower-case hexadecimal encoding of the
     *         input address.
     */
    function sha3HexAddress(address addr) private pure returns (bytes32 ret) {
        assembly {
            for {
                let i := 40
            } gt(i, 0) {

            } {
                i := sub(i, 1)
                mstore8(i, byte(and(addr, 0xf), lookup))
                addr := div(addr, 0x10)
                i := sub(i, 1)
                mstore8(i, byte(and(addr, 0xf), lookup))
                addr := div(addr, 0x10)
            }

            ret := keccak256(0, 40)
        }
    }

    function ownsContract(address addr) internal view returns (bool) {
        try Ownable(addr).owner() returns (address owner) {
            return owner == msg.sender;
        } catch {
            return false;
        }
    }
}


// File contracts/registry/ENSRegistry.sol

pragma solidity >=0.8.4;

/**
 * The ENS registry contract.
 */
contract ENSRegistry is ENS {
    struct Record {
        address owner;
        address resolver;
        uint64 ttl;
    }

    mapping(bytes32 => Record) public records;
    mapping(address => mapping(address => bool)) operators;

    // Permits modifications only by the owner of the specified node.
    modifier authorised(bytes32 node) {
        address owner = records[node].owner;
        require(owner == msg.sender || operators[owner][msg.sender]);
        _;
    }

    /**
     * @dev Constructs a new ENS registry.
     */
    constructor() public {
        records[0x0].owner = msg.sender;
    }

    /**
     * @dev Sets the record for a node.
     * @param node The node to update.
     * @param owner The address of the new owner.
     * @param resolver The address of the resolver.
     * @param ttl The TTL in seconds.
     */
    function setRecord(
        bytes32 node,
        address owner,
        address resolver,
        uint64 ttl
    ) external virtual override {
        setOwner(node, owner);
        _setResolverAndTTL(node, resolver, ttl);
    }

    /**
     * @dev Sets the record for a subnode.
     * @param node The parent node.
     * @param label The hash of the label specifying the subnode.
     * @param owner The address of the new owner.
     * @param resolver The address of the resolver.
     * @param ttl The TTL in seconds.
     */
    function setSubnodeRecord(
        bytes32 node,
        bytes32 label,
        address owner,
        address resolver,
        uint64 ttl
    ) external virtual override {
        bytes32 subnode = setSubnodeOwner(node, label, owner);
        _setResolverAndTTL(subnode, resolver, ttl);
    }

    /**
     * @dev Transfers ownership of a node to a new address. May only be called by the current owner of the node.
     * @param node The node to transfer ownership of.
     * @param owner The address of the new owner.
     */
    function setOwner(
        bytes32 node,
        address owner
    ) public virtual override authorised(node) {
        _setOwner(node, owner);
        emit Transfer(node, owner);
    }

    /**
     * @dev Transfers ownership of a subnode keccak256(node, label) to a new address. May only be called by the owner of the parent node.
     * @param node The parent node.
     * @param label The hash of the label specifying the subnode.
     * @param owner The address of the new owner.
     */
    function setSubnodeOwner(
        bytes32 node,
        bytes32 label,
        address owner
    ) public virtual override authorised(node) returns (bytes32) {
        bytes32 subnode = keccak256(abi.encodePacked(node, label));
        _setOwner(subnode, owner);
        emit NewOwner(node, label, owner);
        return subnode;
    }

    /**
     * @dev Sets the resolver address for the specified node.
     * @param node The node to update.
     * @param resolver The address of the resolver.
     */
    function setResolver(
        bytes32 node,
        address resolver
    ) public virtual override authorised(node) {
        emit NewResolver(node, resolver);
        records[node].resolver = resolver;
    }

    /**
     * @dev Sets the TTL for the specified node.
     * @param node The node to update.
     * @param ttl The TTL in seconds.
     */
    function setTTL(
        bytes32 node,
        uint64 ttl
    ) public virtual override authorised(node) {
        emit NewTTL(node, ttl);
        records[node].ttl = ttl;
    }

    /**
     * @dev Enable or disable approval for a third party ("operator") to manage
     *  all of `msg.sender`'s ENS records. Emits the ApprovalForAll event.
     * @param operator Address to add to the set of authorized operators.
     * @param approved True if the operator is approved, false to revoke approval.
     */
    function setApprovalForAll(
        address operator,
        bool approved
    ) external virtual override {
        operators[msg.sender][operator] = approved;
        emit ApprovalForAll(msg.sender, operator, approved);
    }

    /**
     * @dev Returns the address that owns the specified node.
     * @param node The specified node.
     * @return address of the owner.
     */
    function owner(
        bytes32 node
    ) public view virtual override returns (address) {
        address addr = records[node].owner;
        if (addr == address(this)) {
            return address(0x0);
        }

        return addr;
    }

    /**
     * @dev Returns the address of the resolver for the specified node.
     * @param node The specified node.
     * @return address of the resolver.
     */
    function resolver(
        bytes32 node
    ) public view virtual override returns (address) {
        return records[node].resolver;
    }

    /**
     * @dev Returns the TTL of a node, and any records associated with it.
     * @param node The specified node.
     * @return ttl of the node.
     */
    function ttl(bytes32 node) public view virtual override returns (uint64) {
        return records[node].ttl;
    }

    /**
     * @dev Returns whether a record has been imported to the registry.
     * @param node The specified node.
     * @return Bool if record exists
     */
    function recordExists(
        bytes32 node
    ) public view virtual override returns (bool) {
        return records[node].owner != address(0x0);
    }

    /**
     * @dev Query if an address is an authorized operator for another address.
     * @param owner The address that owns the records.
     * @param operator The address that acts on behalf of the owner.
     * @return True if `operator` is an approved operator for `owner`, false otherwise.
     */
    function isApprovedForAll(
        address owner,
        address operator
    ) external view virtual override returns (bool) {
        return operators[owner][operator];
    }

    function _setOwner(bytes32 node, address owner) internal virtual {
        records[node].owner = owner;
    }

    function _setResolverAndTTL(
        bytes32 node,
        address resolver,
        uint64 ttl
    ) internal {
        if (resolver != records[node].resolver) {
            records[node].resolver = resolver;
            emit NewResolver(node, resolver);
        }

        if (ttl != records[node].ttl) {
            records[node].ttl = ttl;
            emit NewTTL(node, ttl);
        }
    }
}


// File contracts/root/Root.sol

pragma solidity ^0.8.4;



contract Root is Ownable, Controllable {
    bytes32 private constant ROOT_NODE = bytes32(0);

    bytes4 private constant INTERFACE_META_ID =
        bytes4(keccak256("supportsInterface(bytes4)"));

    event TLDLocked(bytes32 indexed label);

    ENS public ens;
    mapping(bytes32 => bool) public locked;

    constructor(ENS _ens) public {
        ens = _ens;
    }

    function setSubnodeOwner(
        bytes32 label,
        address owner
    ) external onlyController {
        require(!locked[label]);
        ens.setSubnodeOwner(ROOT_NODE, label, owner);
    }

    function setResolver(address resolver) external onlyOwner {
        ens.setResolver(ROOT_NODE, resolver);
    }

    function lock(bytes32 label) external onlyOwner {
        emit TLDLocked(label);
        locked[label] = true;
    }

    function supportsInterface(
        bytes4 interfaceID
    ) external pure returns (bool) {
        return interfaceID == INTERFACE_META_ID;
    }
}


// File contracts/utils/BytesUtils.sol


pragma solidity ^0.8.4;

library BytesUtils {
    error OffsetOutOfBoundsError(uint256 offset, uint256 length);

    /*
     * @dev Returns the keccak-256 hash of a byte range.
     * @param self The byte string to hash.
     * @param offset The position to start hashing at.
     * @param len The number of bytes to hash.
     * @return The hash of the byte range.
     */
    function keccak(
        bytes memory self,
        uint256 offset,
        uint256 len
    ) internal pure returns (bytes32 ret) {
        require(offset + len <= self.length);
        assembly {
            ret := keccak256(add(add(self, 32), offset), len)
        }
    }

    /**
     * @dev Returns the ENS namehash of a DNS-encoded name.
     * @param self The DNS-encoded name to hash.
     * @param offset The offset at which to start hashing.
     * @return The namehash of the name.
     */
    function namehash(
        bytes memory self,
        uint256 offset
    ) internal pure returns (bytes32) {
        (bytes32 labelhash, uint256 newOffset) = readLabel(self, offset);
        if (labelhash == bytes32(0)) {
            require(offset == self.length - 1, "namehash: Junk at end of name");
            return bytes32(0);
        }
        return
            keccak256(abi.encodePacked(namehash(self, newOffset), labelhash));
    }

    /**
     * @dev Returns the keccak-256 hash of a DNS-encoded label, and the offset to the start of the next label.
     * @param self The byte string to read a label from.
     * @param idx The index to read a label at.
     * @return labelhash The hash of the label at the specified index, or 0 if it is the last label.
     * @return newIdx The index of the start of the next label.
     */
    function readLabel(
        bytes memory self,
        uint256 idx
    ) internal pure returns (bytes32 labelhash, uint256 newIdx) {
        require(idx < self.length, "readLabel: Index out of bounds");
        uint256 len = uint256(uint8(self[idx]));
        if (len > 0) {
            labelhash = keccak(self, idx + 1, len);
        } else {
            labelhash = bytes32(0);
        }
        newIdx = idx + len + 1;
    }

    /*
     * @dev Returns a positive number if `other` comes lexicographically after
     *      `self`, a negative number if it comes before, or zero if the
     *      contents of the two bytes are equal.
     * @param self The first bytes to compare.
     * @param other The second bytes to compare.
     * @return The result of the comparison.
     */
    function compare(
        bytes memory self,
        bytes memory other
    ) internal pure returns (int256) {
        return compare(self, 0, self.length, other, 0, other.length);
    }

    /*
     * @dev Returns a positive number if `other` comes lexicographically after
     *      `self`, a negative number if it comes before, or zero if the
     *      contents of the two bytes are equal. Comparison is done per-rune,
     *      on unicode codepoints.
     * @param self The first bytes to compare.
     * @param offset The offset of self.
     * @param len    The length of self.
     * @param other The second bytes to compare.
     * @param otheroffset The offset of the other string.
     * @param otherlen    The length of the other string.
     * @return The result of the comparison.
     */
    function compare(
        bytes memory self,
        uint256 offset,
        uint256 len,
        bytes memory other,
        uint256 otheroffset,
        uint256 otherlen
    ) internal pure returns (int256) {
        if (offset + len > self.length) {
            revert OffsetOutOfBoundsError(offset + len, self.length);
        }
        if (otheroffset + otherlen > other.length) {
            revert OffsetOutOfBoundsError(otheroffset + otherlen, other.length);
        }

        uint256 shortest = len;
        if (otherlen < len) shortest = otherlen;

        uint256 selfptr;
        uint256 otherptr;

        assembly {
            selfptr := add(self, add(offset, 32))
            otherptr := add(other, add(otheroffset, 32))
        }
        for (uint256 idx = 0; idx < shortest; idx += 32) {
            uint256 a;
            uint256 b;
            assembly {
                a := mload(selfptr)
                b := mload(otherptr)
            }
            if (a != b) {
                // Mask out irrelevant bytes and check again
                uint256 mask;
                if (shortest - idx >= 32) {
                    mask = type(uint256).max;
                } else {
                    mask = ~(2 ** (8 * (idx + 32 - shortest)) - 1);
                }
                int256 diff = int256(a & mask) - int256(b & mask);
                if (diff != 0) return diff;
            }
            selfptr += 32;
            otherptr += 32;
        }

        return int256(len) - int256(otherlen);
    }

    /*
     * @dev Returns true if the two byte ranges are equal.
     * @param self The first byte range to compare.
     * @param offset The offset into the first byte range.
     * @param other The second byte range to compare.
     * @param otherOffset The offset into the second byte range.
     * @param len The number of bytes to compare
     * @return True if the byte ranges are equal, false otherwise.
     */
    function equals(
        bytes memory self,
        uint256 offset,
        bytes memory other,
        uint256 otherOffset,
        uint256 len
    ) internal pure returns (bool) {
        return keccak(self, offset, len) == keccak(other, otherOffset, len);
    }

    /*
     * @dev Returns true if the two byte ranges are equal with offsets.
     * @param self The first byte range to compare.
     * @param offset The offset into the first byte range.
     * @param other The second byte range to compare.
     * @param otherOffset The offset into the second byte range.
     * @return True if the byte ranges are equal, false otherwise.
     */
    function equals(
        bytes memory self,
        uint256 offset,
        bytes memory other,
        uint256 otherOffset
    ) internal pure returns (bool) {
        return
            keccak(self, offset, self.length - offset) ==
            keccak(other, otherOffset, other.length - otherOffset);
    }

    /*
     * @dev Compares a range of 'self' to all of 'other' and returns True iff
     *      they are equal.
     * @param self The first byte range to compare.
     * @param offset The offset into the first byte range.
     * @param other The second byte range to compare.
     * @return True if the byte ranges are equal, false otherwise.
     */
    function equals(
        bytes memory self,
        uint256 offset,
        bytes memory other
    ) internal pure returns (bool) {
        return
            self.length == offset + other.length &&
            equals(self, offset, other, 0, other.length);
    }

    /*
     * @dev Returns true if the two byte ranges are equal.
     * @param self The first byte range to compare.
     * @param other The second byte range to compare.
     * @return True if the byte ranges are equal, false otherwise.
     */
    function equals(
        bytes memory self,
        bytes memory other
    ) internal pure returns (bool) {
        return
            self.length == other.length &&
            equals(self, 0, other, 0, self.length);
    }

    /*
     * @dev Returns the 8-bit number at the specified index of self.
     * @param self The byte string.
     * @param idx The index into the bytes
     * @return The specified 8 bits of the string, interpreted as an integer.
     */
    function readUint8(
        bytes memory self,
        uint256 idx
    ) internal pure returns (uint8 ret) {
        return uint8(self[idx]);
    }

    /*
     * @dev Returns the 16-bit number at the specified index of self.
     * @param self The byte string.
     * @param idx The index into the bytes
     * @return The specified 16 bits of the string, interpreted as an integer.
     */
    function readUint16(
        bytes memory self,
        uint256 idx
    ) internal pure returns (uint16 ret) {
        require(idx + 2 <= self.length);
        assembly {
            ret := and(mload(add(add(self, 2), idx)), 0xFFFF)
        }
    }

    /*
     * @dev Returns the 32-bit number at the specified index of self.
     * @param self The byte string.
     * @param idx The index into the bytes
     * @return The specified 32 bits of the string, interpreted as an integer.
     */
    function readUint32(
        bytes memory self,
        uint256 idx
    ) internal pure returns (uint32 ret) {
        require(idx + 4 <= self.length);
        assembly {
            ret := and(mload(add(add(self, 4), idx)), 0xFFFFFFFF)
        }
    }

    /*
     * @dev Returns the 32 byte value at the specified index of self.
     * @param self The byte string.
     * @param idx The index into the bytes
     * @return The specified 32 bytes of the string.
     */
    function readBytes32(
        bytes memory self,
        uint256 idx
    ) internal pure returns (bytes32 ret) {
        require(idx + 32 <= self.length);
        assembly {
            ret := mload(add(add(self, 32), idx))
        }
    }

    /*
     * @dev Returns the 32 byte value at the specified index of self.
     * @param self The byte string.
     * @param idx The index into the bytes
     * @return The specified 32 bytes of the string.
     */
    function readBytes20(
        bytes memory self,
        uint256 idx
    ) internal pure returns (bytes20 ret) {
        require(idx + 20 <= self.length);
        assembly {
            ret := and(
                mload(add(add(self, 32), idx)),
                0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000000
            )
        }
    }

    /*
     * @dev Returns the n byte value at the specified index of self.
     * @param self The byte string.
     * @param idx The index into the bytes.
     * @param len The number of bytes.
     * @return The specified 32 bytes of the string.
     */
    function readBytesN(
        bytes memory self,
        uint256 idx,
        uint256 len
    ) internal pure returns (bytes32 ret) {
        require(len <= 32);
        require(idx + len <= self.length);
        assembly {
            let mask := not(sub(exp(256, sub(32, len)), 1))
            ret := and(mload(add(add(self, 32), idx)), mask)
        }
    }

    function memcpy(uint256 dest, uint256 src, uint256 len) private pure {
        // Copy word-length chunks while possible
        for (; len >= 32; len -= 32) {
            assembly {
                mstore(dest, mload(src))
            }
            dest += 32;
            src += 32;
        }

        // Copy remaining bytes
        unchecked {
            uint256 mask = (256 ** (32 - len)) - 1;
            assembly {
                let srcpart := and(mload(src), not(mask))
                let destpart := and(mload(dest), mask)
                mstore(dest, or(destpart, srcpart))
            }
        }
    }

    /*
     * @dev Copies a substring into a new byte string.
     * @param self The byte string to copy from.
     * @param offset The offset to start copying at.
     * @param len The number of bytes to copy.
     */
    function substring(
        bytes memory self,
        uint256 offset,
        uint256 len
    ) internal pure returns (bytes memory) {
        require(offset + len <= self.length);

        bytes memory ret = new bytes(len);
        uint256 dest;
        uint256 src;

        assembly {
            dest := add(ret, 32)
            src := add(add(self, 32), offset)
        }
        memcpy(dest, src, len);

        return ret;
    }

    // Maps characters from 0x30 to 0x7A to their base32 values.
    // 0xFF represents invalid characters in that range.
    bytes constant base32HexTable =
        hex"00010203040506070809FFFFFFFFFFFFFF0A0B0C0D0E0F101112131415161718191A1B1C1D1E1FFFFFFFFFFFFFFFFFFFFF0A0B0C0D0E0F101112131415161718191A1B1C1D1E1F";

    /**
     * @dev Decodes unpadded base32 data of up to one word in length.
     * @param self The data to decode.
     * @param off Offset into the string to start at.
     * @param len Number of characters to decode.
     * @return The decoded data, left aligned.
     */
    function base32HexDecodeWord(
        bytes memory self,
        uint256 off,
        uint256 len
    ) internal pure returns (bytes32) {
        require(len <= 52);

        uint256 ret = 0;
        uint8 decoded;
        for (uint256 i = 0; i < len; i++) {
            bytes1 char = self[off + i];
            require(char >= 0x30 && char <= 0x7A);
            decoded = uint8(base32HexTable[uint256(uint8(char)) - 0x30]);
            require(decoded <= 0x20);
            if (i == len - 1) {
                break;
            }
            ret = (ret << 5) | decoded;
        }

        uint256 bitlen = len * 5;
        if (len % 8 == 0) {
            // Multiple of 8 characters, no padding
            ret = (ret << 5) | decoded;
        } else if (len % 8 == 2) {
            // Two extra characters - 1 byte
            ret = (ret << 3) | (decoded >> 2);
            bitlen -= 2;
        } else if (len % 8 == 4) {
            // Four extra characters - 2 bytes
            ret = (ret << 1) | (decoded >> 4);
            bitlen -= 4;
        } else if (len % 8 == 5) {
            // Five extra characters - 3 bytes
            ret = (ret << 4) | (decoded >> 1);
            bitlen -= 1;
        } else if (len % 8 == 7) {
            // Seven extra characters - 4 bytes
            ret = (ret << 2) | (decoded >> 3);
            bitlen -= 3;
        } else {
            revert();
        }

        return bytes32(ret << (256 - bitlen));
    }

    /**
     * @dev Finds the first occurrence of the byte `needle` in `self`.
     * @param self The string to search
     * @param off The offset to start searching at
     * @param len The number of bytes to search
     * @param needle The byte to search for
     * @return The offset of `needle` in `self`, or 2**256-1 if it was not found.
     */
    function find(
        bytes memory self,
        uint256 off,
        uint256 len,
        bytes1 needle
    ) internal pure returns (uint256) {
        for (uint256 idx = off; idx < off + len; idx++) {
            if (self[idx] == needle) {
                return idx;
            }
        }
        return type(uint256).max;
    }
}


// File @ensdomains/buffer/contracts/Buffer.sol@v0.1.1


pragma solidity ^0.8.4;

/**
* @dev A library for working with mutable byte buffers in Solidity.
*
* Byte buffers are mutable and expandable, and provide a variety of primitives
* for appending to them. At any time you can fetch a bytes object containing the
* current contents of the buffer. The bytes object should not be stored between
* operations, as it may change due to resizing of the buffer.
*/
library Buffer {
    /**
    * @dev Represents a mutable buffer. Buffers have a current value (buf) and
    *      a capacity. The capacity may be longer than the current value, in
    *      which case it can be extended without the need to allocate more memory.
    */
    struct buffer {
        bytes buf;
        uint capacity;
    }

    /**
    * @dev Initializes a buffer with an initial capacity.
    * @param buf The buffer to initialize.
    * @param capacity The number of bytes of space to allocate the buffer.
    * @return The buffer, for chaining.
    */
    function init(buffer memory buf, uint capacity) internal pure returns(buffer memory) {
        if (capacity % 32 != 0) {
            capacity += 32 - (capacity % 32);
        }
        // Allocate space for the buffer data
        buf.capacity = capacity;
        assembly {
            let ptr := mload(0x40)
            mstore(buf, ptr)
            mstore(ptr, 0)
            let fpm := add(32, add(ptr, capacity))
            if lt(fpm, ptr) {
                revert(0, 0)
            }
            mstore(0x40, fpm)
        }
        return buf;
    }

    /**
    * @dev Initializes a new buffer from an existing bytes object.
    *      Changes to the buffer may mutate the original value.
    * @param b The bytes object to initialize the buffer with.
    * @return A new buffer.
    */
    function fromBytes(bytes memory b) internal pure returns(buffer memory) {
        buffer memory buf;
        buf.buf = b;
        buf.capacity = b.length;
        return buf;
    }

    function resize(buffer memory buf, uint capacity) private pure {
        bytes memory oldbuf = buf.buf;
        init(buf, capacity);
        append(buf, oldbuf);
    }

    /**
    * @dev Sets buffer length to 0.
    * @param buf The buffer to truncate.
    * @return The original buffer, for chaining..
    */
    function truncate(buffer memory buf) internal pure returns (buffer memory) {
        assembly {
            let bufptr := mload(buf)
            mstore(bufptr, 0)
        }
        return buf;
    }

    /**
    * @dev Appends len bytes of a byte string to a buffer. Resizes if doing so would exceed
    *      the capacity of the buffer.
    * @param buf The buffer to append to.
    * @param data The data to append.
    * @param len The number of bytes to copy.
    * @return The original buffer, for chaining.
    */
    function append(buffer memory buf, bytes memory data, uint len) internal pure returns(buffer memory) {
        require(len <= data.length);

        uint off = buf.buf.length;
        uint newCapacity = off + len;
        if (newCapacity > buf.capacity) {
            resize(buf, newCapacity * 2);
        }

        uint dest;
        uint src;
        assembly {
            // Memory address of the buffer data
            let bufptr := mload(buf)
            // Length of existing buffer data
            let buflen := mload(bufptr)
            // Start address = buffer address + offset + sizeof(buffer length)
            dest := add(add(bufptr, 32), off)
            // Update buffer length if we're extending it
            if gt(newCapacity, buflen) {
                mstore(bufptr, newCapacity)
            }
            src := add(data, 32)
        }

        // Copy word-length chunks while possible
        for (; len >= 32; len -= 32) {
            assembly {
                mstore(dest, mload(src))
            }
            dest += 32;
            src += 32;
        }

        // Copy remaining bytes
        unchecked {
            uint mask = (256 ** (32 - len)) - 1;
            assembly {
                let srcpart := and(mload(src), not(mask))
                let destpart := and(mload(dest), mask)
                mstore(dest, or(destpart, srcpart))
            }
        }

        return buf;
    }

    /**
    * @dev Appends a byte string to a buffer. Resizes if doing so would exceed
    *      the capacity of the buffer.
    * @param buf The buffer to append to.
    * @param data The data to append.
    * @return The original buffer, for chaining.
    */
    function append(buffer memory buf, bytes memory data) internal pure returns (buffer memory) {
        return append(buf, data, data.length);
    }

    /**
    * @dev Appends a byte to the buffer. Resizes if doing so would exceed the
    *      capacity of the buffer.
    * @param buf The buffer to append to.
    * @param data The data to append.
    * @return The original buffer, for chaining.
    */
    function appendUint8(buffer memory buf, uint8 data) internal pure returns(buffer memory) {
        uint off = buf.buf.length;
        uint offPlusOne = off + 1;
        if (off >= buf.capacity) {
            resize(buf, offPlusOne * 2);
        }

        assembly {
            // Memory address of the buffer data
            let bufptr := mload(buf)
            // Address = buffer address + sizeof(buffer length) + off
            let dest := add(add(bufptr, off), 32)
            mstore8(dest, data)
            // Update buffer length if we extended it
            if gt(offPlusOne, mload(bufptr)) {
                mstore(bufptr, offPlusOne)
            }
        }

        return buf;
    }

    /**
    * @dev Appends len bytes of bytes32 to a buffer. Resizes if doing so would
    *      exceed the capacity of the buffer.
    * @param buf The buffer to append to.
    * @param data The data to append.
    * @param len The number of bytes to write (left-aligned).
    * @return The original buffer, for chaining.
    */
    function append(buffer memory buf, bytes32 data, uint len) private pure returns(buffer memory) {
        uint off = buf.buf.length;
        uint newCapacity = len + off;
        if (newCapacity > buf.capacity) {
            resize(buf, newCapacity * 2);
        }

        unchecked {
            uint mask = (256 ** len) - 1;
            // Right-align data
            data = data >> (8 * (32 - len));
            assembly {
                // Memory address of the buffer data
                let bufptr := mload(buf)
                // Address = buffer address + sizeof(buffer length) + newCapacity
                let dest := add(bufptr, newCapacity)
                mstore(dest, or(and(mload(dest), not(mask)), data))
                // Update buffer length if we extended it
                if gt(newCapacity, mload(bufptr)) {
                    mstore(bufptr, newCapacity)
                }
            }
        }
        return buf;
    }

    /**
    * @dev Appends a bytes20 to the buffer. Resizes if doing so would exceed
    *      the capacity of the buffer.
    * @param buf The buffer to append to.
    * @param data The data to append.
    * @return The original buffer, for chhaining.
    */
    function appendBytes20(buffer memory buf, bytes20 data) internal pure returns (buffer memory) {
        return append(buf, bytes32(data), 20);
    }

    /**
    * @dev Appends a bytes32 to the buffer. Resizes if doing so would exceed
    *      the capacity of the buffer.
    * @param buf The buffer to append to.
    * @param data The data to append.
    * @return The original buffer, for chaining.
    */
    function appendBytes32(buffer memory buf, bytes32 data) internal pure returns (buffer memory) {
        return append(buf, data, 32);
    }

    /**
     * @dev Appends a byte to the end of the buffer. Resizes if doing so would
     *      exceed the capacity of the buffer.
     * @param buf The buffer to append to.
     * @param data The data to append.
     * @param len The number of bytes to write (right-aligned).
     * @return The original buffer.
     */
    function appendInt(buffer memory buf, uint data, uint len) internal pure returns(buffer memory) {
        uint off = buf.buf.length;
        uint newCapacity = len + off;
        if (newCapacity > buf.capacity) {
            resize(buf, newCapacity * 2);
        }

        uint mask = (256 ** len) - 1;
        assembly {
            // Memory address of the buffer data
            let bufptr := mload(buf)
            // Address = buffer address + sizeof(buffer length) + newCapacity
            let dest := add(bufptr, newCapacity)
            mstore(dest, or(and(mload(dest), not(mask)), data))
            // Update buffer length if we extended it
            if gt(newCapacity, mload(bufptr)) {
                mstore(bufptr, newCapacity)
            }
        }
        return buf;
    }
}


// File contracts/dnssec-oracle/RRUtils.sol


pragma solidity ^0.8.4;


/**
 * @dev RRUtils is a library that provides utilities for parsing DNS resource records.
 */
library RRUtils {
    using BytesUtils for *;
    using Buffer for *;

    /**
     * @dev Returns the number of bytes in the DNS name at 'offset' in 'self'.
     * @param self The byte array to read a name from.
     * @param offset The offset to start reading at.
     * @return The length of the DNS name at 'offset', in bytes.
     */
    function nameLength(
        bytes memory self,
        uint256 offset
    ) internal pure returns (uint256) {
        uint256 idx = offset;
        while (true) {
            assert(idx < self.length);
            uint256 labelLen = self.readUint8(idx);
            idx += labelLen + 1;
            if (labelLen == 0) {
                break;
            }
        }
        return idx - offset;
    }

    /**
     * @dev Returns a DNS format name at the specified offset of self.
     * @param self The byte array to read a name from.
     * @param offset The offset to start reading at.
     * @return ret The name.
     */
    function readName(
        bytes memory self,
        uint256 offset
    ) internal pure returns (bytes memory ret) {
        uint256 len = nameLength(self, offset);
        return self.substring(offset, len);
    }

    /**
     * @dev Returns the number of labels in the DNS name at 'offset' in 'self'.
     * @param self The byte array to read a name from.
     * @param offset The offset to start reading at.
     * @return The number of labels in the DNS name at 'offset', in bytes.
     */
    function labelCount(
        bytes memory self,
        uint256 offset
    ) internal pure returns (uint256) {
        uint256 count = 0;
        while (true) {
            assert(offset < self.length);
            uint256 labelLen = self.readUint8(offset);
            offset += labelLen + 1;
            if (labelLen == 0) {
                break;
            }
            count += 1;
        }
        return count;
    }

    uint256 constant RRSIG_TYPE = 0;
    uint256 constant RRSIG_ALGORITHM = 2;
    uint256 constant RRSIG_LABELS = 3;
    uint256 constant RRSIG_TTL = 4;
    uint256 constant RRSIG_EXPIRATION = 8;
    uint256 constant RRSIG_INCEPTION = 12;
    uint256 constant RRSIG_KEY_TAG = 16;
    uint256 constant RRSIG_SIGNER_NAME = 18;

    struct SignedSet {
        uint16 typeCovered;
        uint8 algorithm;
        uint8 labels;
        uint32 ttl;
        uint32 expiration;
        uint32 inception;
        uint16 keytag;
        bytes signerName;
        bytes data;
        bytes name;
    }

    function readSignedSet(
        bytes memory data
    ) internal pure returns (SignedSet memory self) {
        self.typeCovered = data.readUint16(RRSIG_TYPE);
        self.algorithm = data.readUint8(RRSIG_ALGORITHM);
        self.labels = data.readUint8(RRSIG_LABELS);
        self.ttl = data.readUint32(RRSIG_TTL);
        self.expiration = data.readUint32(RRSIG_EXPIRATION);
        self.inception = data.readUint32(RRSIG_INCEPTION);
        self.keytag = data.readUint16(RRSIG_KEY_TAG);
        self.signerName = readName(data, RRSIG_SIGNER_NAME);
        self.data = data.substring(
            RRSIG_SIGNER_NAME + self.signerName.length,
            data.length - RRSIG_SIGNER_NAME - self.signerName.length
        );
    }

    function rrs(
        SignedSet memory rrset
    ) internal pure returns (RRIterator memory) {
        return iterateRRs(rrset.data, 0);
    }

    /**
     * @dev An iterator over resource records.
     */
    struct RRIterator {
        bytes data;
        uint256 offset;
        uint16 dnstype;
        uint16 class;
        uint32 ttl;
        uint256 rdataOffset;
        uint256 nextOffset;
    }

    /**
     * @dev Begins iterating over resource records.
     * @param self The byte string to read from.
     * @param offset The offset to start reading at.
     * @return ret An iterator object.
     */
    function iterateRRs(
        bytes memory self,
        uint256 offset
    ) internal pure returns (RRIterator memory ret) {
        ret.data = self;
        ret.nextOffset = offset;
        next(ret);
    }

    /**
     * @dev Returns true iff there are more RRs to iterate.
     * @param iter The iterator to check.
     * @return True iff the iterator has finished.
     */
    function done(RRIterator memory iter) internal pure returns (bool) {
        return iter.offset >= iter.data.length;
    }

    /**
     * @dev Moves the iterator to the next resource record.
     * @param iter The iterator to advance.
     */
    function next(RRIterator memory iter) internal pure {
        iter.offset = iter.nextOffset;
        if (iter.offset >= iter.data.length) {
            return;
        }

        // Skip the name
        uint256 off = iter.offset + nameLength(iter.data, iter.offset);

        // Read type, class, and ttl
        iter.dnstype = iter.data.readUint16(off);
        off += 2;
        iter.class = iter.data.readUint16(off);
        off += 2;
        iter.ttl = iter.data.readUint32(off);
        off += 4;

        // Read the rdata
        uint256 rdataLength = iter.data.readUint16(off);
        off += 2;
        iter.rdataOffset = off;
        iter.nextOffset = off + rdataLength;
    }

    /**
     * @dev Returns the name of the current record.
     * @param iter The iterator.
     * @return A new bytes object containing the owner name from the RR.
     */
    function name(RRIterator memory iter) internal pure returns (bytes memory) {
        return
            iter.data.substring(
                iter.offset,
                nameLength(iter.data, iter.offset)
            );
    }

    /**
     * @dev Returns the rdata portion of the current record.
     * @param iter The iterator.
     * @return A new bytes object containing the RR's RDATA.
     */
    function rdata(
        RRIterator memory iter
    ) internal pure returns (bytes memory) {
        return
            iter.data.substring(
                iter.rdataOffset,
                iter.nextOffset - iter.rdataOffset
            );
    }

    uint256 constant DNSKEY_FLAGS = 0;
    uint256 constant DNSKEY_PROTOCOL = 2;
    uint256 constant DNSKEY_ALGORITHM = 3;
    uint256 constant DNSKEY_PUBKEY = 4;

    struct DNSKEY {
        uint16 flags;
        uint8 protocol;
        uint8 algorithm;
        bytes publicKey;
    }

    function readDNSKEY(
        bytes memory data,
        uint256 offset,
        uint256 length
    ) internal pure returns (DNSKEY memory self) {
        self.flags = data.readUint16(offset + DNSKEY_FLAGS);
        self.protocol = data.readUint8(offset + DNSKEY_PROTOCOL);
        self.algorithm = data.readUint8(offset + DNSKEY_ALGORITHM);
        self.publicKey = data.substring(
            offset + DNSKEY_PUBKEY,
            length - DNSKEY_PUBKEY
        );
    }

    uint256 constant DS_KEY_TAG = 0;
    uint256 constant DS_ALGORITHM = 2;
    uint256 constant DS_DIGEST_TYPE = 3;
    uint256 constant DS_DIGEST = 4;

    struct DS {
        uint16 keytag;
        uint8 algorithm;
        uint8 digestType;
        bytes digest;
    }

    function readDS(
        bytes memory data,
        uint256 offset,
        uint256 length
    ) internal pure returns (DS memory self) {
        self.keytag = data.readUint16(offset + DS_KEY_TAG);
        self.algorithm = data.readUint8(offset + DS_ALGORITHM);
        self.digestType = data.readUint8(offset + DS_DIGEST_TYPE);
        self.digest = data.substring(offset + DS_DIGEST, length - DS_DIGEST);
    }

    function isSubdomainOf(
        bytes memory self,
        bytes memory other
    ) internal pure returns (bool) {
        uint256 off = 0;
        uint256 counts = labelCount(self, 0);
        uint256 othercounts = labelCount(other, 0);

        while (counts > othercounts) {
            off = progress(self, off);
            counts--;
        }

        return self.equals(off, other, 0);
    }

    function compareNames(
        bytes memory self,
        bytes memory other
    ) internal pure returns (int256) {
        if (self.equals(other)) {
            return 0;
        }

        uint256 off;
        uint256 otheroff;
        uint256 prevoff;
        uint256 otherprevoff;
        uint256 counts = labelCount(self, 0);
        uint256 othercounts = labelCount(other, 0);

        // Keep removing labels from the front of the name until both names are equal length
        while (counts > othercounts) {
            prevoff = off;
            off = progress(self, off);
            counts--;
        }

        while (othercounts > counts) {
            otherprevoff = otheroff;
            otheroff = progress(other, otheroff);
            othercounts--;
        }

        // Compare the last nonequal labels to each other
        while (counts > 0 && !self.equals(off, other, otheroff)) {
            prevoff = off;
            off = progress(self, off);
            otherprevoff = otheroff;
            otheroff = progress(other, otheroff);
            counts -= 1;
        }

        if (off == 0) {
            return -1;
        }
        if (otheroff == 0) {
            return 1;
        }

        return
            self.compare(
                prevoff + 1,
                self.readUint8(prevoff),
                other,
                otherprevoff + 1,
                other.readUint8(otherprevoff)
            );
    }

    /**
     * @dev Compares two serial numbers using RFC1982 serial number math.
     */
    function serialNumberGte(
        uint32 i1,
        uint32 i2
    ) internal pure returns (bool) {
        unchecked {
            return int32(i1) - int32(i2) >= 0;
        }
    }

    function progress(
        bytes memory body,
        uint256 off
    ) internal pure returns (uint256) {
        return off + 1 + body.readUint8(off);
    }

    /**
     * @dev Computes the keytag for a chunk of data.
     * @param data The data to compute a keytag for.
     * @return The computed key tag.
     */
    function computeKeytag(bytes memory data) internal pure returns (uint16) {
        /* This function probably deserves some explanation.
         * The DNSSEC keytag function is a checksum that relies on summing up individual bytes
         * from the input string, with some mild bitshifting. Here's a Naive solidity implementation:
         *
         *     function computeKeytag(bytes memory data) internal pure returns (uint16) {
         *         uint ac;
         *         for (uint i = 0; i < data.length; i++) {
         *             ac += i & 1 == 0 ? uint16(data.readUint8(i)) << 8 : data.readUint8(i);
         *         }
         *         return uint16(ac + (ac >> 16));
         *     }
         *
         * The EVM, with its 256 bit words, is exceedingly inefficient at doing byte-by-byte operations;
         * the code above, on reasonable length inputs, consumes over 100k gas. But we can make the EVM's
         * large words work in our favour.
         *
         * The code below works by treating the input as a series of 256 bit words. It first masks out
         * even and odd bytes from each input word, adding them to two separate accumulators `ac1` and `ac2`.
         * The bytes are separated by empty bytes, so as long as no individual sum exceeds 2^16-1, we're
         * effectively summing 16 different numbers with each EVM ADD opcode.
         *
         * Once it's added up all the inputs, it has to add all the 16 bit values in `ac1` and `ac2` together.
         * It does this using the same trick - mask out every other value, shift to align them, add them together.
         * After the first addition on both accumulators, there's enough room to add the two accumulators together,
         * and the remaining sums can be done just on ac1.
         */
        unchecked {
            require(data.length <= 8192, "Long keys not permitted");
            uint256 ac1;
            uint256 ac2;
            for (uint256 i = 0; i < data.length + 31; i += 32) {
                uint256 word;
                assembly {
                    word := mload(add(add(data, 32), i))
                }
                if (i + 32 > data.length) {
                    uint256 unused = 256 - (data.length - i) * 8;
                    word = (word >> unused) << unused;
                }
                ac1 +=
                    (word &
                        0xFF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00) >>
                    8;
                ac2 += (word &
                    0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF);
            }
            ac1 =
                (ac1 &
                    0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF) +
                ((ac1 &
                    0xFFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000) >>
                    16);
            ac2 =
                (ac2 &
                    0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF) +
                ((ac2 &
                    0xFFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000) >>
                    16);
            ac1 = (ac1 << 8) + ac2;
            ac1 =
                (ac1 &
                    0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF) +
                ((ac1 &
                    0xFFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000) >>
                    32);
            ac1 =
                (ac1 &
                    0x0000000000000000FFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF) +
                ((ac1 &
                    0xFFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF0000000000000000) >>
                    64);
            ac1 =
                (ac1 &
                    0x00000000000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) +
                (ac1 >> 128);
            ac1 += (ac1 >> 16) & 0xFFFF;
            return uint16(ac1);
        }
    }
}


// File contracts/utils/HexUtils.sol


pragma solidity ^0.8.4;

library HexUtils {
    /**
     * @dev Attempts to parse bytes32 from a hex string
     * @param str The string to parse
     * @param idx The offset to start parsing at
     * @param lastIdx The (exclusive) last index in `str` to consider. Use `str.length` to scan the whole string.
     */
    function hexStringToBytes32(
        bytes memory str,
        uint256 idx,
        uint256 lastIdx
    ) internal pure returns (bytes32, bool) {
        require(lastIdx - idx <= 64);
        (bytes memory r, bool valid) = hexToBytes(str, idx, lastIdx);
        if (!valid) {
            return (bytes32(0), false);
        }
        bytes32 ret;
        assembly {
            ret := shr(mul(4, sub(64, sub(lastIdx, idx))), mload(add(r, 32)))
        }
        return (ret, true);
    }

    function hexToBytes(
        bytes memory str,
        uint256 idx,
        uint256 lastIdx
    ) internal pure returns (bytes memory r, bool valid) {
        uint256 hexLength = lastIdx - idx;
        if (hexLength % 2 == 1) {
            revert("Invalid string length");
        }
        r = new bytes(hexLength / 2);
        valid = true;
        assembly {
            // check that the index to read to is not past the end of the string
            if gt(lastIdx, mload(str)) {
                revert(0, 0)
            }

            function getHex(c) -> ascii {
                // chars 48-57: 0-9
                if and(gt(c, 47), lt(c, 58)) {
                    ascii := sub(c, 48)
                    leave
                }
                // chars 65-70: A-F
                if and(gt(c, 64), lt(c, 71)) {
                    ascii := add(sub(c, 65), 10)
                    leave
                }
                // chars 97-102: a-f
                if and(gt(c, 96), lt(c, 103)) {
                    ascii := add(sub(c, 97), 10)
                    leave
                }
                // invalid char
                ascii := 0xff
            }

            let ptr := add(str, 32)
            for {
                let i := idx
            } lt(i, lastIdx) {
                i := add(i, 2)
            } {
                let byte1 := getHex(byte(0, mload(add(ptr, i))))
                let byte2 := getHex(byte(0, mload(add(ptr, add(i, 1)))))
                // if either byte is invalid, set invalid and break loop
                if or(eq(byte1, 0xff), eq(byte2, 0xff)) {
                    valid := false
                    break
                }
                let combined := or(shl(4, byte1), byte2)
                mstore8(add(add(r, 32), div(sub(i, idx), 2)), combined)
            }
        }
    }

    /**
     * @dev Attempts to parse an address from a hex string
     * @param str The string to parse
     * @param idx The offset to start parsing at
     * @param lastIdx The (exclusive) last index in `str` to consider. Use `str.length` to scan the whole string.
     */
    function hexToAddress(
        bytes memory str,
        uint256 idx,
        uint256 lastIdx
    ) internal pure returns (address, bool) {
        if (lastIdx - idx < 40) return (address(0x0), false);
        (bytes32 r, bool valid) = hexStringToBytes32(str, idx, lastIdx);
        return (address(uint160(uint256(r))), valid);
    }

    /**
     * @dev Attempts to convert an address to a hex string
     * @param addr The _addr to parse
     */
    function addressToHex(address addr) internal pure returns (string memory) {
        bytes memory hexString = new bytes(40);
        for (uint i = 0; i < 20; i++) {
            bytes1 byteValue = bytes1(uint8(uint160(addr) >> (8 * (19 - i))));
            bytes1 highNibble = bytes1(uint8(byteValue) / 16);
            bytes1 lowNibble = bytes1(
                uint8(byteValue) - 16 * uint8(highNibble)
            );
            hexString[2 * i] = _nibbleToHexChar(highNibble);
            hexString[2 * i + 1] = _nibbleToHexChar(lowNibble);
        }
        return string(hexString);
    }

    function _nibbleToHexChar(
        bytes1 nibble
    ) internal pure returns (bytes1 hexChar) {
        if (uint8(nibble) < 10) return bytes1(uint8(nibble) + 0x30);
        else return bytes1(uint8(nibble) + 0x57);
    }
}


// File contracts/dnsregistrar/DNSClaimChecker.sol


pragma solidity ^0.8.4;





library DNSClaimChecker {
    using BytesUtils for bytes;
    using HexUtils for bytes;
    using RRUtils for *;
    using Buffer for Buffer.buffer;

    uint16 constant CLASS_INET = 1;
    uint16 constant TYPE_TXT = 16;

    function getOwnerAddress(
        bytes memory name,
        bytes memory data
    ) internal pure returns (address, bool) {
        // Add "_ens." to the front of the name.
        Buffer.buffer memory buf;
        buf.init(name.length + 5);
        buf.append("\x04_ens");
        buf.append(name);

        for (
            RRUtils.RRIterator memory iter = data.iterateRRs(0);
            !iter.done();
            iter.next()
        ) {
            if (iter.name().compareNames(buf.buf) != 0) continue;
            bool found;
            address addr;
            (addr, found) = parseRR(data, iter.rdataOffset, iter.nextOffset);
            if (found) {
                return (addr, true);
            }
        }

        return (address(0x0), false);
    }

    function parseRR(
        bytes memory rdata,
        uint256 idx,
        uint256 endIdx
    ) internal pure returns (address, bool) {
        while (idx < endIdx) {
            uint256 len = rdata.readUint8(idx);
            idx += 1;

            bool found;
            address addr;
            (addr, found) = parseString(rdata, idx, len);

            if (found) return (addr, true);
            idx += len;
        }

        return (address(0x0), false);
    }

    function parseString(
        bytes memory str,
        uint256 idx,
        uint256 len
    ) internal pure returns (address, bool) {
        // TODO: More robust parsing that handles whitespace and multiple key/value pairs
        if (str.readUint32(idx) != 0x613d3078) return (address(0x0), false); // 0x613d3078 == 'a=0x'
        return str.hexToAddress(idx + 4, idx + len);
    }
}


// File contracts/dnsregistrar/IDNSRegistrar.sol


pragma solidity ^0.8.4;

interface IDNSRegistrar {
    function proveAndClaim(
        bytes memory name,
        DNSSEC.RRSetWithSignature[] memory input
    ) external;

    function proveAndClaimWithResolver(
        bytes memory name,
        DNSSEC.RRSetWithSignature[] memory input,
        address resolver,
        address addr
    ) external;
}


// File contracts/dnsregistrar/PublicSuffixList.sol

pragma solidity ^0.8.4;

interface PublicSuffixList {
    function isPublicSuffix(bytes calldata name) external view returns (bool);
}


// File contracts/resolvers/profiles/IVersionableResolver.sol


pragma solidity >=0.8.4;

interface IVersionableResolver {
    event VersionChanged(bytes32 indexed node, uint64 newVersion);

    function recordVersions(bytes32 node) external view returns (uint64);
}


// File @openzeppelin/contracts/utils/introspection/IERC165.sol@v4.8.0


// OpenZeppelin Contracts v4.4.1 (utils/introspection/IERC165.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC165 standard, as defined in the
 * https://eips.ethereum.org/EIPS/eip-165[EIP].
 *
 * Implementers can declare support of contract interfaces, which can then be
 * queried by others ({ERC165Checker}).
 *
 * For an implementation, see {ERC165}.
 */
interface IERC165 {
    /**
     * @dev Returns true if this contract implements the interface defined by
     * `interfaceId`. See the corresponding
     * https://eips.ethereum.org/EIPS/eip-165#how-interfaces-are-identified[EIP section]
     * to learn more about how these ids are created.
     *
     * This function call must use less than 30 000 gas.
     */
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}


// File @openzeppelin/contracts/utils/introspection/ERC165.sol@v4.8.0


// OpenZeppelin Contracts v4.4.1 (utils/introspection/ERC165.sol)

pragma solidity ^0.8.0;

/**
 * @dev Implementation of the {IERC165} interface.
 *
 * Contracts that want to implement ERC165 should inherit from this contract and override {supportsInterface} to check
 * for the additional interface id that will be supported. For example:
 *
 * ```solidity
 * function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
 *     return interfaceId == type(MyInterface).interfaceId || super.supportsInterface(interfaceId);
 * }
 * ```
 *
 * Alternatively, {ERC165Storage} provides an easier to use but more expensive implementation.
 */
abstract contract ERC165 is IERC165 {
    /**
     * @dev See {IERC165-supportsInterface}.
     */
    function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
        return interfaceId == type(IERC165).interfaceId;
    }
}


// File contracts/resolvers/ResolverBase.sol


pragma solidity >=0.8.4;


abstract contract ResolverBase is ERC165, IVersionableResolver {
    mapping(bytes32 => uint64) public recordVersions;

    function isAuthorised(bytes32 node) internal view virtual returns (bool);

    modifier authorised(bytes32 node) {
        require(isAuthorised(node));
        _;
    }

    /**
     * Increments the record version associated with an ENS node.
     * May only be called by the owner of that node in the ENS registry.
     * @param node The node to update.
     */
    function clearRecords(bytes32 node) public virtual authorised(node) {
        recordVersions[node]++;
        emit VersionChanged(node, recordVersions[node]);
    }

    function supportsInterface(
        bytes4 interfaceID
    ) public view virtual override returns (bool) {
        return
            interfaceID == type(IVersionableResolver).interfaceId ||
            super.supportsInterface(interfaceID);
    }
}


// File contracts/resolvers/profiles/IAddressResolver.sol


pragma solidity >=0.8.4;

/**
 * Interface for the new (multicoin) addr function.
 */
interface IAddressResolver {
    event AddressChanged(
        bytes32 indexed node,
        uint256 coinType,
        bytes newAddress
    );

    function addr(
        bytes32 node,
        uint256 coinType
    ) external view returns (bytes memory);
}


// File contracts/resolvers/profiles/IAddrResolver.sol


pragma solidity >=0.8.4;

/**
 * Interface for the legacy (ETH-only) addr function.
 */
interface IAddrResolver {
    event AddrChanged(bytes32 indexed node, address a);

    /**
     * Returns the address associated with an ENS node.
     * @param node The ENS node to query.
     * @return The associated address.
     */
    function addr(bytes32 node) external view returns (address payable);
}


// File contracts/resolvers/profiles/AddrResolver.sol


pragma solidity >=0.8.4;



abstract contract AddrResolver is
    IAddrResolver,
    IAddressResolver,
    ResolverBase
{
    uint256 private constant COIN_TYPE_ETH = 60;

    mapping(uint64 => mapping(bytes32 => mapping(uint256 => bytes))) versionable_addresses;

    /**
     * Sets the address associated with an ENS node.
     * May only be called by the owner of that node in the ENS registry.
     * @param node The node to update.
     * @param a The address to set.
     */
    function setAddr(
        bytes32 node,
        address a
    ) external virtual authorised(node) {
        setAddr(node, COIN_TYPE_ETH, addressToBytes(a));
    }

    /**
     * Returns the address associated with an ENS node.
     * @param node The ENS node to query.
     * @return The associated address.
     */
    function addr(
        bytes32 node
    ) public view virtual override returns (address payable) {
        bytes memory a = addr(node, COIN_TYPE_ETH);
        if (a.length == 0) {
            return payable(0);
        }
        return bytesToAddress(a);
    }

    function setAddr(
        bytes32 node,
        uint256 coinType,
        bytes memory a
    ) public virtual authorised(node) {
        emit AddressChanged(node, coinType, a);
        if (coinType == COIN_TYPE_ETH) {
            emit AddrChanged(node, bytesToAddress(a));
        }
        versionable_addresses[recordVersions[node]][node][coinType] = a;
    }

    function addr(
        bytes32 node,
        uint256 coinType
    ) public view virtual override returns (bytes memory) {
        return versionable_addresses[recordVersions[node]][node][coinType];
    }

    function supportsInterface(
        bytes4 interfaceID
    ) public view virtual override returns (bool) {
        return
            interfaceID == type(IAddrResolver).interfaceId ||
            interfaceID == type(IAddressResolver).interfaceId ||
            super.supportsInterface(interfaceID);
    }

    function bytesToAddress(
        bytes memory b
    ) internal pure returns (address payable a) {
        require(b.length == 20);
        assembly {
            a := div(mload(add(b, 32)), exp(256, 12))
        }
    }

    function addressToBytes(address a) internal pure returns (bytes memory b) {
        b = new bytes(20);
        assembly {
            mstore(add(b, 32), mul(a, exp(256, 12)))
        }
    }
}


// File contracts/dnsregistrar/DNSRegistrar.sol



pragma solidity ^0.8.4;











/**
 * @dev An ENS registrar that allows the owner of a DNS name to claim the
 *      corresponding name in ENS.
 */
contract DNSRegistrar is IDNSRegistrar, IERC165 {
    using BytesUtils for bytes;
    using Buffer for Buffer.buffer;
    using RRUtils for *;

    ENS public immutable ens;
    DNSSEC public immutable oracle;
    PublicSuffixList public suffixes;
    address public immutable previousRegistrar;
    address public immutable resolver;
    // A mapping of the most recent signatures seen for each claimed domain.
    mapping(bytes32 => uint32) public inceptions;

    error NoOwnerRecordFound();
    error PermissionDenied(address caller, address owner);
    error PreconditionNotMet();
    error StaleProof();
    error InvalidPublicSuffix(bytes name);

    struct OwnerRecord {
        bytes name;
        address owner;
        address resolver;
        uint64 ttl;
    }

    event Claim(
        bytes32 indexed node,
        address indexed owner,
        bytes dnsname,
        uint32 inception
    );
    event NewPublicSuffixList(address suffixes);

    constructor(
        address _previousRegistrar,
        address _resolver,
        DNSSEC _dnssec,
        PublicSuffixList _suffixes,
        ENS _ens
    ) {
        previousRegistrar = _previousRegistrar;
        resolver = _resolver;
        oracle = _dnssec;
        suffixes = _suffixes;
        emit NewPublicSuffixList(address(suffixes));
        ens = _ens;
    }

    /**
     * @dev This contract's owner-only functions can be invoked by the owner of the ENS root.
     */
    modifier onlyOwner() {
        Root root = Root(ens.owner(bytes32(0)));
        address owner = root.owner();
        require(msg.sender == owner);
        _;
    }

    function setPublicSuffixList(PublicSuffixList _suffixes) public onlyOwner {
        suffixes = _suffixes;
        emit NewPublicSuffixList(address(suffixes));
    }

    /**
     * @dev Submits proofs to the DNSSEC oracle, then claims a name using those proofs.
     * @param name The name to claim, in DNS wire format.
     * @param input A chain of signed DNS RRSETs ending with a text record.
     */
    function proveAndClaim(
        bytes memory name,
        DNSSEC.RRSetWithSignature[] memory input
    ) public override {
        (bytes32 rootNode, bytes32 labelHash, address addr) = _claim(
            name,
            input
        );
        ens.setSubnodeOwner(rootNode, labelHash, addr);
    }

    function proveAndClaimWithResolver(
        bytes memory name,
        DNSSEC.RRSetWithSignature[] memory input,
        address resolver,
        address addr
    ) public override {
        (bytes32 rootNode, bytes32 labelHash, address owner) = _claim(
            name,
            input
        );
        if (msg.sender != owner) {
            revert PermissionDenied(msg.sender, owner);
        }
        ens.setSubnodeRecord(rootNode, labelHash, owner, resolver, 0);
        if (addr != address(0)) {
            if (resolver == address(0)) {
                revert PreconditionNotMet();
            }
            bytes32 node = keccak256(abi.encodePacked(rootNode, labelHash));
            // Set the resolver record
            AddrResolver(resolver).setAddr(node, addr);
        }
    }

    function supportsInterface(
        bytes4 interfaceID
    ) external pure override returns (bool) {
        return
            interfaceID == type(IERC165).interfaceId ||
            interfaceID == type(IDNSRegistrar).interfaceId;
    }

    function _claim(
        bytes memory name,
        DNSSEC.RRSetWithSignature[] memory input
    ) internal returns (bytes32 parentNode, bytes32 labelHash, address addr) {
        (bytes memory data, uint32 inception) = oracle.verifyRRSet(input);

        // Get the first label
        uint256 labelLen = name.readUint8(0);
        labelHash = name.keccak(1, labelLen);

        bytes memory parentName = name.substring(
            labelLen + 1,
            name.length - labelLen - 1
        );

        // Make sure the parent name is enabled
        parentNode = enableNode(parentName);

        bytes32 node = keccak256(abi.encodePacked(parentNode, labelHash));
        if (!RRUtils.serialNumberGte(inception, inceptions[node])) {
            revert StaleProof();
        }
        inceptions[node] = inception;

        bool found;
        (addr, found) = DNSClaimChecker.getOwnerAddress(name, data);
        if (!found) {
            revert NoOwnerRecordFound();
        }

        emit Claim(node, addr, name, inception);
    }

    function enableNode(bytes memory domain) public returns (bytes32 node) {
        // Name must be in the public suffix list.
        if (!suffixes.isPublicSuffix(domain)) {
            revert InvalidPublicSuffix(domain);
        }
        return _enableNode(domain, 0);
    }

    function _enableNode(
        bytes memory domain,
        uint256 offset
    ) internal returns (bytes32 node) {
        uint256 len = domain.readUint8(offset);
        if (len == 0) {
            return bytes32(0);
        }

        bytes32 parentNode = _enableNode(domain, offset + len + 1);
        bytes32 label = domain.keccak(offset + 1, len);
        node = keccak256(abi.encodePacked(parentNode, label));
        address owner = ens.owner(node);
        if (owner == address(0) || owner == previousRegistrar) {
            if (parentNode == bytes32(0)) {
                Root root = Root(ens.owner(bytes32(0)));
                root.setSubnodeOwner(label, address(this));
                ens.setResolver(node, resolver);
            } else {
                ens.setSubnodeRecord(
                    parentNode,
                    label,
                    address(this),
                    resolver,
                    0
                );
            }
        } else if (owner != address(this)) {
            revert PreconditionNotMet();
        }
        return node;
    }
}


// File contracts/dnssec-oracle/Owned.sol

pragma solidity ^0.8.4;

/**
 * @dev Contract mixin for 'owned' contracts.
 */
contract Owned {
    address public owner;

    modifier owner_only() {
        require(msg.sender == owner);
        _;
    }

    constructor() public {
        owner = msg.sender;
    }

    function setOwner(address newOwner) public owner_only {
        owner = newOwner;
    }
}


// File contracts/dnssec-oracle/digests/Digest.sol

pragma solidity ^0.8.4;

/**
 * @dev An interface for contracts implementing a DNSSEC digest.
 */
interface Digest {
    /**
     * @dev Verifies a cryptographic hash.
     * @param data The data to hash.
     * @param hash The hash to compare to.
     * @return True iff the hashed data matches the provided hash value.
     */
    function verify(
        bytes calldata data,
        bytes calldata hash
    ) external pure virtual returns (bool);
}


// File contracts/dnssec-oracle/algorithms/Algorithm.sol

pragma solidity ^0.8.4;

/**
 * @dev An interface for contracts implementing a DNSSEC (signing) algorithm.
 */
interface Algorithm {
    /**
     * @dev Verifies a signature.
     * @param key The public key to verify with.
     * @param data The signed data to verify.
     * @param signature The signature to verify.
     * @return True iff the signature is valid.
     */
    function verify(
        bytes calldata key,
        bytes calldata data,
        bytes calldata signature
    ) external view virtual returns (bool);
}


// File contracts/dnssec-oracle/DNSSECImpl.sol


pragma solidity ^0.8.4;







/*
 * @dev An oracle contract that verifies and stores DNSSEC-validated DNS records.
 * @note This differs from the DNSSEC spec defined in RFC4034 and RFC4035 in some key regards:
 *       - NSEC & NSEC3 are not supported; only positive proofs are allowed.
 *       - Proofs involving wildcard names will not validate.
 *       - TTLs on records are ignored, as data is not stored persistently.
 *       - Canonical form of names is not checked; in ENS this is done on the frontend, so submitting
 *         proofs with non-canonical names will only result in registering unresolvable ENS names.
 */
contract DNSSECImpl is DNSSEC, Owned {
    using Buffer for Buffer.buffer;
    using BytesUtils for bytes;
    using RRUtils for *;

    uint16 constant DNSCLASS_IN = 1;

    uint16 constant DNSTYPE_DS = 43;
    uint16 constant DNSTYPE_DNSKEY = 48;

    uint256 constant DNSKEY_FLAG_ZONEKEY = 0x100;

    error InvalidLabelCount(bytes name, uint256 labelsExpected);
    error SignatureNotValidYet(uint32 inception, uint32 now);
    error SignatureExpired(uint32 expiration, uint32 now);
    error InvalidClass(uint16 class);
    error InvalidRRSet();
    error SignatureTypeMismatch(uint16 rrsetType, uint16 sigType);
    error InvalidSignerName(bytes rrsetName, bytes signerName);
    error InvalidProofType(uint16 proofType);
    error ProofNameMismatch(bytes signerName, bytes proofName);
    error NoMatchingProof(bytes signerName);

    mapping(uint8 => Algorithm) public algorithms;
    mapping(uint8 => Digest) public digests;

    /**
     * @dev Constructor.
     * @param _anchors The binary format RR entries for the root DS records.
     */
    constructor(bytes memory _anchors) {
        // Insert the 'trust anchors' - the key hashes that start the chain
        // of trust for all other records.
        anchors = _anchors;
    }

    /**
     * @dev Sets the contract address for a signature verification algorithm.
     *      Callable only by the owner.
     * @param id The algorithm ID
     * @param algo The address of the algorithm contract.
     */
    function setAlgorithm(uint8 id, Algorithm algo) public owner_only {
        algorithms[id] = algo;
        emit AlgorithmUpdated(id, address(algo));
    }

    /**
     * @dev Sets the contract address for a digest verification algorithm.
     *      Callable only by the owner.
     * @param id The digest ID
     * @param digest The address of the digest contract.
     */
    function setDigest(uint8 id, Digest digest) public owner_only {
        digests[id] = digest;
        emit DigestUpdated(id, address(digest));
    }

    /**
     * @dev Takes a chain of signed DNS records, verifies them, and returns the data from the last record set in the chain.
     *      Reverts if the records do not form an unbroken chain of trust to the DNSSEC anchor records.
     * @param input A list of signed RRSets.
     * @return rrs The RRData from the last RRSet in the chain.
     * @return inception The inception time of the signed record set.
     */
    function verifyRRSet(
        RRSetWithSignature[] memory input
    )
        external
        view
        virtual
        override
        returns (bytes memory rrs, uint32 inception)
    {
        return verifyRRSet(input, block.timestamp);
    }

    /**
     * @dev Takes a chain of signed DNS records, verifies them, and returns the data from the last record set in the chain.
     *      Reverts if the records do not form an unbroken chain of trust to the DNSSEC anchor records.
     * @param input A list of signed RRSets.
     * @param now The Unix timestamp to validate the records at.
     * @return rrs The RRData from the last RRSet in the chain.
     * @return inception The inception time of the signed record set.
     */
    function verifyRRSet(
        RRSetWithSignature[] memory input,
        uint256 now
    )
        public
        view
        virtual
        override
        returns (bytes memory rrs, uint32 inception)
    {
        bytes memory proof = anchors;
        for (uint256 i = 0; i < input.length; i++) {
            RRUtils.SignedSet memory rrset = validateSignedSet(
                input[i],
                proof,
                now
            );
            proof = rrset.data;
            inception = rrset.inception;
        }
        return (proof, inception);
    }

    /**
     * @dev Validates an RRSet against the already trusted RR provided in `proof`.
     *
     * @param input The signed RR set. This is in the format described in section
     *        5.3.2 of RFC4035: The RRDATA section from the RRSIG without the signature
     *        data, followed by a series of canonicalised RR records that the signature
     *        applies to.
     * @param proof The DNSKEY or DS to validate the signature against.
     * @param now The current timestamp.
     */
    function validateSignedSet(
        RRSetWithSignature memory input,
        bytes memory proof,
        uint256 now
    ) internal view returns (RRUtils.SignedSet memory rrset) {
        rrset = input.rrset.readSignedSet();

        // Do some basic checks on the RRs and extract the name
        bytes memory name = validateRRs(rrset, rrset.typeCovered);
        if (name.labelCount(0) != rrset.labels) {
            // revert InvalidLabelCount(name, rrset.labels);
        }
        rrset.name = name;

        // All comparisons involving the Signature Expiration and
        // Inception fields MUST use "serial number arithmetic", as
        // defined in RFC 1982

        // o  The validator's notion of the current time MUST be less than or
        //    equal to the time listed in the RRSIG RR's Expiration field.
        if (!RRUtils.serialNumberGte(rrset.expiration, uint32(now))) {
            // revert SignatureExpired(rrset.expiration, uint32(now));
        }

        // o  The validator's notion of the current time MUST be greater than or
        //    equal to the time listed in the RRSIG RR's Inception field.
        if (!RRUtils.serialNumberGte(uint32(now), rrset.inception)) {
            // revert SignatureNotValidYet(rrset.inception, uint32(now));
        }

        // Validate the signature
        verifySignature(name, rrset, input, proof);

        return rrset;
    }

    /**
     * @dev Validates a set of RRs.
     * @param rrset The RR set.
     * @param typecovered The type covered by the RRSIG record.
     */
    function validateRRs(
        RRUtils.SignedSet memory rrset,
        uint16 typecovered
    ) internal pure returns (bytes memory name) {
        // Iterate over all the RRs
        for (
            RRUtils.RRIterator memory iter = rrset.rrs();
            !iter.done();
            iter.next()
        ) {
            // We only support class IN (Internet)
            if (iter.class != DNSCLASS_IN) {
                //revert InvalidClass(iter.class);
            }

            if (name.length == 0) {
                name = iter.name();
            } else {
                // Name must be the same on all RRs. We do things this way to avoid copying the name
                // repeatedly.
                if (
                    name.length != iter.data.nameLength(iter.offset) ||
                    !name.equals(0, iter.data, iter.offset, name.length)
                ) {
                    //revert InvalidRRSet();
                }
            }

            // o  The RRSIG RR's Type Covered field MUST equal the RRset's type.
            if (iter.dnstype != typecovered) {
                //revert SignatureTypeMismatch(iter.dnstype, typecovered);
            }
        }
    }

    /**
     * @dev Performs signature verification.
     *
     * Throws or reverts if unable to verify the record.
     *
     * @param name The name of the RRSIG record, in DNS label-sequence format.
     * @param data The original data to verify.
     * @param proof A DS or DNSKEY record that's already verified by the oracle.
     */
    function verifySignature(
        bytes memory name,
        RRUtils.SignedSet memory rrset,
        RRSetWithSignature memory data,
        bytes memory proof
    ) internal view {
        // o  The RRSIG RR's Signer's Name field MUST be the name of the zone
        //    that contains the RRset.
        if (!name.isSubdomainOf(rrset.signerName)) {
            // revert InvalidSignerName(name, rrset.signerName);
        }

        RRUtils.RRIterator memory proofRR = proof.iterateRRs(0);
        // Check the proof
        if (proofRR.dnstype == DNSTYPE_DS) {
            verifyWithDS(rrset, data, proofRR);
        } else if (proofRR.dnstype == DNSTYPE_DNSKEY) {
            verifyWithKnownKey(rrset, data, proofRR);
        } else {
            //revert InvalidProofType(proofRR.dnstype);
        }
    }

    /**
     * @dev Attempts to verify a signed RRSET against an already known public key.
     * @param rrset The signed set to verify.
     * @param data The original data the signed set was read from.
     * @param proof The serialized DS or DNSKEY record to use as proof.
     */
    function verifyWithKnownKey(
        RRUtils.SignedSet memory rrset,
        RRSetWithSignature memory data,
        RRUtils.RRIterator memory proof
    ) internal view {
        // Check the DNSKEY's owner name matches the signer name on the RRSIG
        for (; !proof.done(); proof.next()) {
            bytes memory proofName = proof.name();
            if (!proofName.equals(rrset.signerName)) {
                //revert ProofNameMismatch(rrset.signerName, proofName);
            }

            bytes memory keyrdata = proof.rdata();
            RRUtils.DNSKEY memory dnskey = keyrdata.readDNSKEY(
                0,
                keyrdata.length
            );
            if (verifySignatureWithKey(dnskey, keyrdata, rrset, data)) {
                return;
            }
        }
        //revert NoMatchingProof(rrset.signerName);
    }

    /**
     * @dev Attempts to verify some data using a provided key and a signature.
     * @param dnskey The dns key record to verify the signature with.
     * @param rrset The signed RRSET being verified.
     * @param data The original data `rrset` was decoded from.
     * @return True iff the key verifies the signature.
     */
    function verifySignatureWithKey(
        RRUtils.DNSKEY memory dnskey,
        bytes memory keyrdata,
        RRUtils.SignedSet memory rrset,
        RRSetWithSignature memory data
    ) internal view returns (bool) {
        // TODO: Check key isn't expired, unless updating key itself

        // The Protocol Field MUST have value 3 (RFC4034 2.1.2)
        if (dnskey.protocol != 3) {
            return false;
        }

        // o The RRSIG RR's Signer's Name, Algorithm, and Key Tag fields MUST
        //   match the owner name, algorithm, and key tag for some DNSKEY RR in
        //   the zone's apex DNSKEY RRset.
        if (dnskey.algorithm != rrset.algorithm) {
            return false;
        }
        uint16 computedkeytag = keyrdata.computeKeytag();
        if (computedkeytag != rrset.keytag) {
            return false;
        }

        // o The matching DNSKEY RR MUST be present in the zone's apex DNSKEY
        //   RRset, and MUST have the Zone Flag bit (DNSKEY RDATA Flag bit 7)
        //   set.
        if (dnskey.flags & DNSKEY_FLAG_ZONEKEY == 0) {
            return false;
        }

        Algorithm algorithm = algorithms[dnskey.algorithm];
        if (address(algorithm) == address(0)) {
            return false;
        }
        return algorithm.verify(keyrdata, data.rrset, data.sig);
    }

    /**
     * @dev Attempts to verify a signed RRSET against an already known hash. This function assumes
     *      that the record
     * @param rrset The signed set to verify.
     * @param data The original data the signed set was read from.
     * @param proof The serialized DS or DNSKEY record to use as proof.
     */
    function verifyWithDS(
        RRUtils.SignedSet memory rrset,
        RRSetWithSignature memory data,
        RRUtils.RRIterator memory proof
    ) internal view {
        uint256 proofOffset = proof.offset;
        for (
            RRUtils.RRIterator memory iter = rrset.rrs();
            !iter.done();
            iter.next()
        ) {
            if (iter.dnstype != DNSTYPE_DNSKEY) {
                //revert InvalidProofType(iter.dnstype);
            }

            bytes memory keyrdata = iter.rdata();
            RRUtils.DNSKEY memory dnskey = keyrdata.readDNSKEY(
                0,
                keyrdata.length
            );
            if (verifySignatureWithKey(dnskey, keyrdata, rrset, data)) {
                // It's self-signed - look for a DS record to verify it.
                if (
                    verifyKeyWithDS(rrset.signerName, proof, dnskey, keyrdata)
                ) {
                    return;
                }
                // Rewind proof iterator to the start for the next loop iteration.
                proof.nextOffset = proofOffset;
                proof.next();
            }
        }
        //revert NoMatchingProof(rrset.signerName);
    }

    /**
     * @dev Attempts to verify a key using DS records.
     * @param keyname The DNS name of the key, in DNS label-sequence format.
     * @param dsrrs The DS records to use in verification.
     * @param dnskey The dnskey to verify.
     * @param keyrdata The RDATA section of the key.
     * @return True if a DS record verifies this key.
     */
    function verifyKeyWithDS(
        bytes memory keyname,
        RRUtils.RRIterator memory dsrrs,
        RRUtils.DNSKEY memory dnskey,
        bytes memory keyrdata
    ) internal view returns (bool) {
        uint16 keytag = keyrdata.computeKeytag();
        for (; !dsrrs.done(); dsrrs.next()) {
            bytes memory proofName = dsrrs.name();
            if (!proofName.equals(keyname)) {
                //revert ProofNameMismatch(keyname, proofName);
            }

            RRUtils.DS memory ds = dsrrs.data.readDS(
                dsrrs.rdataOffset,
                dsrrs.nextOffset - dsrrs.rdataOffset
            );
            if (ds.keytag != keytag) {
                continue;
            }
            if (ds.algorithm != dnskey.algorithm) {
                continue;
            }

            Buffer.buffer memory buf;
            buf.init(keyname.length + keyrdata.length);
            buf.append(keyname);
            buf.append(keyrdata);
            if (verifyDSHash(ds.digestType, buf.buf, ds.digest)) {
                return true;
            }
        }
        return false;
    }

    /**
     * @dev Attempts to verify a DS record's hash value against some data.
     * @param digesttype The digest ID from the DS record.
     * @param data The data to digest.
     * @param digest The digest data to check against.
     * @return True iff the digest matches.
     */
    function verifyDSHash(
        uint8 digesttype,
        bytes memory data,
        bytes memory digest
    ) internal view returns (bool) {
        if (address(digests[digesttype]) == address(0)) {
            return false;
        }
        return digests[digesttype].verify(data, digest);
    }
}


//// File contracts/root/Ownable.sol
//
//pragma solidity ^0.8.4;
//
//contract Ownable {
//    address public owner;
//
//    event OwnershipTransferred(
//        address indexed previousOwner,
//        address indexed newOwner
//    );
//
//    modifier onlyOwner() {
//        require(isOwner(msg.sender));
//        _;
//    }
//
//    constructor() public {
//        owner = msg.sender;
//    }
//
//    function transferOwnership(address newOwner) public onlyOwner {
//        emit OwnershipTransferred(owner, newOwner);
//        owner = newOwner;
//    }
//
//    function isOwner(address addr) public view returns (bool) {
//        return owner == addr;
//    }
//}


// File contracts/dnsregistrar/SimplePublicSuffixList.sol

pragma solidity ^0.8.4;


contract SimplePublicSuffixList is PublicSuffixList, Ownable {
    mapping(bytes => bool) suffixes;

    event SuffixAdded(bytes suffix);

    function addPublicSuffixes(bytes[] memory names) public onlyOwner {
        for (uint256 i = 0; i < names.length; i++) {
            suffixes[names[i]] = true;
            emit SuffixAdded(names[i]);
        }
    }

    function isPublicSuffix(
        bytes calldata name
    ) external view override returns (bool) {
        return suffixes[name];
    }
}


// File contracts/SmokeTest.sol

pragma solidity ^0.8.4;


contract Test
{
    SimplePublicSuffixList suffixes;
    ENSRegistry ens;
    DNSSECImpl dnssec;
    ReverseRegistrar rr;
    Root root;

    DNSRegistrar registrar;

    DNSSEC.RRSetWithSignature[] test_input;


    constructor()
    {
        ens = new ENSRegistry();

        rr = new ReverseRegistrar(ens);

        ens.setSubnodeOwner(bytes32(0), 0xdec08c9dbbdd0890e300eb5062089b2d4b1c40e3673bbccb5423f7b37dcf9a9c, address(this)); // 0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266
        ens.setSubnodeOwner(
            0xa097f6721ce401e757d1223a763fef49b8b5f90bb18567ddb86fd205dff71d34,
            0xe5e14487b78f85faa6e1808e89246cf57dd34831548ff2e6097380d98db2504a,
            address(rr)
        );

        root = new Root(ens);
        ens.setOwner(bytes32(0), address(root));

        suffixes = new SimplePublicSuffixList();

        dnssec = new DNSSECImpl(hex"00002b000100000e1000244a5c080249aac11d7b6f6446702e54a1607371607a1a41855200fd2ce1cdde32f24e8fb500002b000100000e1000244f660802e06d44b80b8f1d39a95c0b0d7c65d08458e880409bbc683457104237c7f8ec8d00002b000100000e10000404fefdfd");

        bytes[] memory suffs = new bytes[](3);
        suffs[0] = hex"03636f6d00";
        suffs[1] = hex"02636f00";
        suffs[2] = hex"02706c00";

        suffixes.addPublicSuffixes(suffs);

        registrar = new DNSRegistrar(address(0), address(0), dnssec, suffixes, ens);

        root.setController(address(registrar), true);
    }

    function prepareInput() public
    {
        test_input = new DNSSEC.RRSetWithSignature[](2);
        test_input[0] = DNSSEC.RRSetWithSignature(hex"0030fd0000000e1066830592665e1b9204fe00000030000100000e100006000003fd0000000030000100000e100006000003fd1112000030000100000e100006010103fd0000", hex"");
        test_input[1] = DNSSEC.RRSetWithSignature(hex"0010fd0300000e1066830592665e1b9204fe00045f656e7303666f6f03636f6d000010000100000e10002d2c613d307866333946643665353161616438384636463463653661423838323732373963666646623932323636", hex"");
    }

    function proveAndClaim() public
    {
        registrar.proveAndClaim(hex"03666f6f03636f6d00", test_input);
    }
}

// ====
// compileViaYul: true
// ----
// constructor() ->
// ~ emit OwnershipTransferred(address,address) from 0x7dc9180eff459918543f0a1e2f7c3be189aca9d7: #0x00, #0x16ebd253e0a5fba9217153992aaf8efa7d9b8c1b
// ~ emit NewOwner(bytes32,bytes32,address) from 0xa7a6372fd270aaaa1f366ef4e3befacf74c3d885: #0x00, #0xdec08c9dbbdd0890e300eb5062089b2d4b1c40e3673bbccb5423f7b37dcf9a9c, 0x16ebd253e0a5fba9217153992aaf8efa7d9b8c1b
// ~ emit NewOwner(bytes32,bytes32,address) from 0xa7a6372fd270aaaa1f366ef4e3befacf74c3d885: #0xa097f6721ce401e757d1223a763fef49b8b5f90bb18567ddb86fd205dff71d34, #0xe5e14487b78f85faa6e1808e89246cf57dd34831548ff2e6097380d98db2504a, 0x7dc9180eff459918543f0a1e2f7c3be189aca9d7
// ~ emit OwnershipTransferred(address,address) from 0x324d49a57b78e7b74ec10bea974543a4f65fdaa3: #0x00, #0x16ebd253e0a5fba9217153992aaf8efa7d9b8c1b
// ~ emit Transfer(bytes32,address) from 0xa7a6372fd270aaaa1f366ef4e3befacf74c3d885: #0x00, 0x324d49a57b78e7b74ec10bea974543a4f65fdaa3
// ~ emit OwnershipTransferred(address,address) from 0x6c786c6082af1f6f3b18b095b3ccd989a8a54e5b: #0x00, #0x16ebd253e0a5fba9217153992aaf8efa7d9b8c1b
// ~ emit SuffixAdded(bytes) from 0x6c786c6082af1f6f3b18b095b3ccd989a8a54e5b: 0x20, 0x05, 0x03636f6d00000000000000000000000000000000000000000000000000000000
// ~ emit SuffixAdded(bytes) from 0x6c786c6082af1f6f3b18b095b3ccd989a8a54e5b: 0x20, 0x04, 0x02636f0000000000000000000000000000000000000000000000000000000000
// ~ emit SuffixAdded(bytes) from 0x6c786c6082af1f6f3b18b095b3ccd989a8a54e5b: 0x20, 0x04, 0x02706c0000000000000000000000000000000000000000000000000000000000
// ~ emit NewPublicSuffixList(address) from 0x39e1efa45642a066479ce3bed6fb148c4286b27d: 0x6c786c6082af1f6f3b18b095b3ccd989a8a54e5b
// ~ emit ControllerChanged(address,bool) from 0x324d49a57b78e7b74ec10bea974543a4f65fdaa3: #0x39e1efa45642a066479ce3bed6fb148c4286b27d, true
// prepareInput() ->
// proveAndClaim() ->
// ~ emit NewOwner(bytes32,bytes32,address) from 0xa7a6372fd270aaaa1f366ef4e3befacf74c3d885: #0x00, #0xb5fcf7e95d62d6d62a9de5c98619595652bd6d90a3ef4a4b23bde43cb10e3035, 0x39e1efa45642a066479ce3bed6fb148c4286b27d
// ~ emit NewResolver(bytes32,address) from 0xa7a6372fd270aaaa1f366ef4e3befacf74c3d885: #0xac2c11ea5d4a4826f418d3befbf0537de7f13572d2a433edfe4a7314ea5dc896, 0x00
// ~ emit Claim(bytes32,address,bytes,uint32) from 0x39e1efa45642a066479ce3bed6fb148c4286b27d: #0xcbcf79455769bee2f1da73c50afdda0c4dba752339a4b3cf7bc4ea2afba5426b, #0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266, 0x40, 0x665e1b92, 0x09, 0x03666f6f03636f6d000000000000000000000000000000000000000000000000
// ~ emit NewOwner(bytes32,bytes32,address) from 0xa7a6372fd270aaaa1f366ef4e3befacf74c3d885: #0xac2c11ea5d4a4826f418d3befbf0537de7f13572d2a433edfe4a7314ea5dc896, #0x41b1a0649752af1b28b3dc29a1556eee781e4a4c3a1f7f53f90fa834de098c4d, 0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266
