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
// f() -> FAILURE, hex"271b1dfa", hex"8ff77dee959af275e2a83aeb93366e425c1abf0ff37cdc8e0000000000000000"
