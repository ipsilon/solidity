contract C {
    function f() public view returns (address a1, address a2) {
        a1 = this.f.address;
        this.f.address;
        [this.f.address][0];
        a2 = [this.f.address][0];
    }
}
// ----
// f() -> 0xee15a2dceade4d1f9c57c8ec5b96baa2ac6d1ca2, 0xee15a2dceade4d1f9c57c8ec5b96baa2ac6d1ca2
