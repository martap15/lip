//SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.2;

contract C2 {
    mapping (uint => uint) m;
    uint x;
    
    function f(uint k, uint v) public { m[k] = v; }
    
    function g(uint k) public { x = m[k]; }

    function h(uint i, uint j) public { m[m[i]] = m[m[j]]+3; }
}