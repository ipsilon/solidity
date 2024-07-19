contract C {
	function f(uint x) public pure returns (uint) {
		return 2 * x;
	}
	function g() public view returns (function (uint) external returns (uint)) {
		return this.f;
	}
	function h(uint x) public returns (uint) {
		return this.g()(x) + 1;
	}
	function t() external view returns (
			function(uint) external returns (uint) a,
			function(uint) external view returns (uint) b) {
		a = this.f;
		b = this.f;
	}
}
// ====
// compileToEOF: true
// ----
// f(uint256): 2 -> 4
// h(uint256): 2 -> 5
// t() -> 0xe5a9dba5a652993d03e40636d48fa32f95992b6eb3de648b0000000000000000, 0xe5a9dba5a652993d03e40636d48fa32f95992b6eb3de648b0000000000000000

