contract C {
	function testFunction() external {}

	function testYul() public returns (address adr) {
		function() external fp = this.testFunction;

		assembly {
			adr := fp.address
		}
	}
	function testSol() public returns (address) {
		return this.testFunction.address;
	}
}
// ----
// testYul() -> 0x3d689b5eed4dd93b4b0e53d737a1e1e558e1d78f
// testSol() -> 0x3d689b5eed4dd93b4b0e53d737a1e1e558e1d78f
