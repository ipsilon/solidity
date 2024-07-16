contract C {
    function f() external returns (address) {
        return this.f.address;
    }
    function g() external returns (bool) {
      return this.f.address == address(this);
    }
    function h(function() external a) public returns (address) {
      return a.address;
    }
}
// ----
// f() -> 0xf3db55f48d1ff0cc12f1e5ea92013a9acf4313c0
// g() -> true
// h(function): left(0x1122334400112233445566778899AABBCCDDEEFF42424242) -> 0x1122334400112233445566778899AABBCCDDEEFF
