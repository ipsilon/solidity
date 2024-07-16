error CustomError(function(uint256) external pure returns (uint256));

contract C
{
    function e(uint256 x) external pure returns (uint256)
    {
        return x;
    }

    function f() external view
    {
        // more than one stack slot
        require(false, CustomError(this.e));
    }
}

// ----
// f() -> FAILURE, hex"271b1dfa", hex"7f5417cf91e6e2618deffc9ca4266c509783dd54f37cdc8e0000000000000000"
