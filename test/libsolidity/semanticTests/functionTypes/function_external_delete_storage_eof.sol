contract C {
    function() external public x;
    uint public y = 0;

    function increment() public {
        ++y;
    }

    function set() external {
        x = this.increment;
    }

    function incrementIndirectly() public {
        x();
    }

    function deleteFunction() public {
        // used to lead to an ICE during IR
        delete x;
    }
}
// ====
// compileToEOF: true
// ----
// x() -> 0
// y() -> 0
// increment() ->
// y() -> 1
// set() ->
// x() -> 0xd8c629386050e31d183410168c183795beaa3ae1d09de08a0000000000000000
// increment() ->
// y() -> 2
// incrementIndirectly() ->
// y() -> 3
// deleteFunction() ->
// increment() ->
// y() -> 4
// incrementIndirectly() ->
// y() -> 4
