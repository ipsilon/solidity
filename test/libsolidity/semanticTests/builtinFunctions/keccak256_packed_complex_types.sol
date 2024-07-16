contract C {
    uint120[3] x;
    function f() public returns (bytes32 hash1, bytes32 hash2, bytes32 hash3) {
        uint120[] memory y = new uint120[](3);
        x[0] = y[0] = uint120(type(uint).max - 1);
        x[1] = y[1] = uint120(type(uint).max - 2);
        x[2] = y[2] = uint120(type(uint).max - 3);
        hash1 = keccak256(abi.encodePacked(x));
        hash2 = keccak256(abi.encodePacked(y));
        hash3 = keccak256(abi.encodePacked(this.f));
    }
}
// ----
// f() -> 0xba4f20407251e4607cd66b90bfea19ec6971699c03e4a4f3ea737d5818ac27ae, 0xba4f20407251e4607cd66b90bfea19ec6971699c03e4a4f3ea737d5818ac27ae, 0xac0f10dbc9a77a452b23a23822d100a2509faaa3efd15c6602e913a17b3e6cc8
