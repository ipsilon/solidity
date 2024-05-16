contract A1 {}
contract B1 is A1 { constructor() payable {} }

contract A2 { constructor() {} }
contract B2 is A2 { constructor() payable {} }

contract B3 { constructor() payable {} }

contract C {
	function f() public payable returns (bool) {
		// Make sure none of these revert.
		new B1{value: 10}();
		bytes32 s1 = 0x0000000000000000000000000000000000000000000000000000000000000001;
		new B2{value: 10, salt: s1}();
		bytes32 s2 = 0x0000000000000000000000000000000000000000000000000000000000000002;
		new B3{value: 10, salt: s2}();
		return true;
	}
}
// ----
// f(), 2000 ether -> true
// gas irOptimized: 117623
// gas irOptimized code: 1800
// gas legacy: 117821
// gas legacy code: 4800
// gas legacyOptimized: 117690
// gas legacyOptimized code: 4800
