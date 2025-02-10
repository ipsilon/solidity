contract C {
    function f() external returns (uint ret)
    {
        assembly
        {
            mstore(0, 11)
            setmodx(0, 32, 21)

            mstore(0, 9)
            mstore(32, 7)

            storex(1, 0, 2)

            addmodx(0, 0, 1, 0, 2, 0, 1)

            loadx(0, 0, 1)

            ret := mload(0)
        }
    }
}
// ====
// bytecodeFormat: >=EOFv1
// ----
// f() -> 5
