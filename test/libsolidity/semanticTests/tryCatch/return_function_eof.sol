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
// ====
// compileToEOF: true
// ----
// f() -> 0x1, 0xef6dada687e3c73c90ef44b4bbc681d1853df567946644cd0000000000000000, 9
