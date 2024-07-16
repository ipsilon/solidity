contract C {
    function g() public returns (uint a, function() external h, uint b) {
        a = 1;
        h = this.fun;
        b = 9;
    }
    function f() public returns (uint, function() external, uint) {
        // Note that the function type uses two stack slots.
        try this.g() returns (uint a, function() external h, uint b) {
            return (a, h, b);
        } catch {
        }
    }
    function fun() public pure {}
}
// ----
// f() -> 0x1, 0x23010d650727c5a8114c0d9bb05acf12e4e3b75e946644cd0000000000000000, 9
