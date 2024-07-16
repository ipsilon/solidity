contract C {
    event TestA(function() external indexed);
    event TestB(function(uint256) external indexed);
    function f1() public {
        emit TestA(this.f1);
    }
    function f2(uint256 a) public {
        emit TestB(this.f2);
    }
}
// ----
// f1() ->
// ~ emit TestA(function): #0x67fed740fd93f58f441e36ff4a2291b381bc6a62c27fc3050000000000000000
// f2(uint256): 1 ->
// ~ emit TestB(function): #0x67fed740fd93f58f441e36ff4a2291b381bc6a62bf3724af0000000000000000
