contract D {
    event Deposit(address indexed _from, bytes32 indexed _id, uint _value);
    function deposit(bytes32 _id) public payable {
        emit Deposit(msg.sender, _id, msg.value);
    }
}
contract C {
    D d;
    constructor() {
        d = new D();
    }
    function deposit(bytes32 _id) public payable {
        d.deposit(_id);
    }
}
// ====
// compileToEOF: true
// ----
// constructor() ->
// gas irOptimized: 113970
// gas irOptimized code: 51400
// gas legacy: 119776
// gas legacy code: 125000
// gas legacyOptimized: 114187
// gas legacyOptimized code: 57400
// deposit(bytes32), 18 wei: 0x1234 ->
// ~ emit Deposit(address,bytes32,uint256) from 0x656c5fc1197ddad8289d7c0731107d9c3ed9685a: #0xcd9d6f9679ddaa23078bd0054c87b238f13f930f, #0x1234, 0x00
