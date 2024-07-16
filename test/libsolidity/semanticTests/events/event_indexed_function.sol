contract C {
    event Test(function() external indexed);
    function f() public {
        emit Test(this.f);
    }
}
// ----
// f() ->
// ~ emit Test(function): #0x3442700685a3d83e888ae28060861622cbb4f91826121ff00000000000000000
