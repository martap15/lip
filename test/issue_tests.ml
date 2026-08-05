open Semantics
open Typechecker


(*test issue 4*)
let%test "test_pure_with_args" = test_exec_tx
  "contract C { 
      uint x; 
      function f(uint y) public pure returns(uint) { return (y+2); } 
      function g() public { x = this.f(3); } 
  }"
  ["0xA:0xC.g()"]
  [("x==5");]

let%test "test_pure_read_state_returns_default" = test_exec_tx
  "contract C { 
      uint x; 
      constructor() { x = 7; } 
      function f() public pure returns(uint) { return (x+1); } 
      function g() public { x = this.f() + 1; } 
  }"
  ["0xA:0xC.g()"]
  [("x==7");] 

let%test "test_pure_cannot_modify_state" = test_exec_tx
  "contract C { 
      uint x; 
      function f() public pure { x = 1; } 
      function g() public { this.f(); } 
    }"
  ["0xA:0xC.g()"]
  [("x==0");] 


let%test "pure_this_reverts_leaves_storage" = test_exec_tx
  "contract C { 
      address a;
      constructor() { a = \"0xC\"; } 
      function f() public pure returns(address) { return this; } 
      function g() public { a = this.f(); }
    }"
  ["0xA:0xC.g()"]
  [("a==\"0xC\"");]

  
let%test "pure_blocknum_reverts_leaves_storage" = test_exec_tx
  "contract C { 
      uint x; 
      constructor() { x = 9; } 
      function f() public pure returns(uint) { return block.number; } 
      function g() public { x = this.f() + 1; } }"
  ["0xA:0xC.g()"]
  [("x==9");]

let%test "pure_var_storage_read_reverts" = test_exec_tx
  "contract C { 
      uint x; 
      constructor() { x = 42; } 
      function f() public pure returns(uint) { return x; } 
      function g() public { x = this.f() + 1; } 
  }"
  ["0xA:0xC.g()"]
  [("x==42");]

let%test "pure_mapR_reverts" = test_exec_tx
  "contract C { 
      mapping(uint => uint) m; 
      uint x; 
      constructor() { m[1] = 5; }
      function f() public pure returns(uint) { return m[1]; } 
      function g() public { x = this.f(); } }"
  ["0xA:0xC.g()"]
  [("x==0");]

let%test "pure_balanceOf_reverts" = test_exec_tx
  "contract C { 
      uint x; 
      function f() public pure returns(uint) { return this.balance; } 
      function g() public { x = this.f(); } 
  }"
  ["0xA:0xC.g()"]
  [("x==0");]

let%test "pure_payableCast_reverts" = test_exec_tx
  "contract C { 
      address payable p; 
      uint x; 
      function f() public pure returns(address) { return payable(this); } 
      function g() public { p = this.f(); } }"
  ["0xA:0xC.g()"]
  [("p==\"0x0\"");]

let%test "pure_funCall_calls_nonpure_revert" = test_exec_tx
  "contract C { 
    uint x; 
    function np() public returns(uint) { x = 3; return 7; } 
    function f() public pure returns(uint) { return this.np(); } 
    function g() public { x = this.f(); } }"
  ["0xA:0xC.g()"]
  [("x==0");]

let%test "pure_assign_storage_reverts" = test_exec_tx
  "contract C { 
      uint x; 
      function f() public pure { x = 1; } 
      function g() public { this.f(); } 
    }"
  ["0xA:0xC.g()"]
  [("x==0");]

let%test "pure_mapW_reverts" = test_exec_tx
  "contract C { 
      mapping(uint => uint) m; 
      uint x; 
      function f() public pure { m[2] = 8; } 
      function g() public { this.f(); x = m[2]; } 
      }"
  ["0xA:0xC.g()"]
  [("x==0");]

let%test "pure_send_reverts_no_balance_change" = test_exec_fun
  "contract C { 
      uint x; 
      receive() external payable { x += 1; } 
    }"
  "contract D { C c; constructor() payable { c = \"0xC\"; } function puretry() public pure { payable(c).transfer(1); } function callit() public { this.puretry(); } }"
  ["0xA:0xD.callit()"]
  [("0xC","this.balance==0 && x==0"); ("0xD","this.balance==100")]

let%test "pure_procCall_nonpure_reverts" = test_exec_tx
  "contract C { 
      uint x; 
      function np() public { x = 11; } 
      function f() public pure { this.np(); } 
      function g() public { this.f(); }
   }"
  ["0xA:0xC.g()"]
  [("x==0");]

let%test "pure_procCall_pure_not_allowed" = test_exec_tx
  "contract C { 
      uint x; 
      function p() public pure { } 
      function f() public pure { this.p(); } 
      function g() public { 
        this.f(); 
        x = 1; 
      }
        
    }"
  ["0xA:0xC.g()"]
  [("x==0");]


(* test issue 6 *)
let%test "test_receive_declaration_correct" = test_typecheck
  "contract C {
      receive() external payable { }
  }"
  true

let%test "test_receive_declaration_with_params" = test_typecheck
  "contract C {
      receive(uint x) external payable { }
  }"
  false

let%test "test_receive_declaration_not_external" = test_typecheck
  "contract C {
      receive() public payable { }
  }"
  false

let%test "test_receive_declaration_not_payable" = test_typecheck
  "contract C {
      receive() external { }
  }"
  false
let%test "test_receive_declaration_multiple" = test_typecheck
  "contract C {
      receive() external payable { }
      receive() external payable { }
  }"
  false

let%test "issue9" = test_typecheck
  "contract C {
    uint x;
    function f() public pure returns(int) { return(1); }
    function g() public { bool b; b = this.f(); }
  }"
  false

(* ---- Function call tests (Issue 9) ---- *)

(* Return: type mismatch - returns bool instead of uint *)
let%test "test_typecheck_funcall_return_1" = test_typecheck
  "contract C {
      int x;
      function f() public view returns (uint) { return(x>0); }
  }"
  false

(* Return: correct return type *)
let%test "test_typecheck_funcall_return_2" = test_typecheck
  "contract C {
      int x;
      function f() public view returns (int) { return(x+1); }
  }"
  true

(* Return: int constant is subtype of uint *)
let%test "test_typecheck_funcall_return_3" = test_typecheck
  "contract C {
      function f() public pure returns (uint) { return(1); }
  }"
  true

(* Return: negative constant not subtype of uint *)
let%test "test_typecheck_funcall_return_4" = test_typecheck
  "contract C {
      function f() public pure returns (uint) { return(-1); }
  }"
  false

(* Return: wrong return type (bool instead of int) *)
let%test "test_typecheck_funcall_return_5" = test_typecheck
  "contract C {
      function f() public pure returns (int) { return(0); }
      function g() public pure returns (int) { int x; x = 1; return(true); }
  }"
  false

(* Return: return value when none expected *)
let%test "test_typecheck_funcall_return_6" = test_typecheck
  "contract C {
      function f() public pure { return(1); }
  }"
  false

(* Return: correct bool return *)
let%test "test_typecheck_funcall_return_7" = test_typecheck
  "contract C {
      function f() public pure returns (bool) { return(true); }
  }"
  true

(* Return: return address *)
let%test "test_typecheck_funcall_return_8" = test_typecheck
  "contract C {
      function f() public view returns (address) { return(msg.sender); }
  }"
  true

(* ProcCall: wrong number of arguments (expects 1, gets 0) *)
let%test "test_typecheck_funcall_proccall_1" = test_typecheck
  "contract C {
      int x;
      function f(int y) public { x = y; }
      function g() public { this.f(); }
  }"
  false

(* ProcCall: correct call *)
let%test "test_typecheck_funcall_proccall_2" = test_typecheck
  "contract C {
      int x;
      function f(int y) public { x = y; }
      function g() public { this.f(3); }
  }"
  true

(* ProcCall: wrong argument type *)
let%test "test_typecheck_funcall_proccall_3" = test_typecheck
  "contract C {
      int x;
      function f(int y) public { x = y; }
      function g() public { this.f(true); }
  }"
  false

(* ProcCall: too many arguments *)
let%test "test_typecheck_funcall_proccall_4" = test_typecheck
  "contract C {
      int x;
      function f(int y) public { x = y; }
      function g() public { this.f(1, 2); }
  }"
  false

(* ProcCall: undeclared function *)
let%test "test_typecheck_funcall_proccall_5" = test_typecheck
  "contract C {
      function g() public { this.h(); }
  }"
  false

(* ProcCall: calling with no args when no args expected *)
let%test "test_typecheck_funcall_proccall_6" = test_typecheck
  "contract C {
      int x;
      function f() public { x = 1; }
      function g() public { this.f(); }
  }"
  true

(* FunCall: return type mismatch at caller site - expects bool, gets int *)
let%test "test_typecheck_funcall_expr_1" = test_typecheck
  "contract C {
      uint x;
      function f() public pure returns(int) { return(1); }
      function g() public { bool b; b = this.f(); }
  }"
  false

(* FunCall: correct assignment from return *)
let%test "test_typecheck_funcall_expr_2" = test_typecheck
  "contract C {
      uint x;
      function f() public pure returns(int) { return(1); }
      function g() public { int b; b = this.f(); }
  }"
  true

(* FunCall: void function used as expression *)
let%test "test_typecheck_funcall_expr_3" = test_typecheck
  "contract C {
      uint x;
      function f() public { x = 1; }
      function g() public { x = this.f(); }
  }"
  false

(* FunCall: wrong arg type in expression call *)
let%test "test_typecheck_funcall_expr_4" = test_typecheck
  "contract C {
      function f(uint y) public pure returns(uint) { return(y+1); }
      function g() public { uint x; x = this.f(true); }
  }"
  false

(* FunCall: arg count mismatch in expression call *)
let%test "test_typecheck_funcall_expr_5" = test_typecheck
  "contract C {
      function f(uint y) public pure returns(uint) { return(y+1); }
      function g() public { uint x; x = this.f(); }
  }"
  false

(* FunCall: uint return assigned to uint *)
let%test "test_typecheck_funcall_expr_6" = test_typecheck
  "contract C {
      uint x;
      function f() public pure returns(uint) { return(5); }
      function g() public { x = this.f(); }
  }"
  true

(* FunCall: result used in arithmetic *)
let%test "test_typecheck_funcall_expr_7" = test_typecheck
  "contract C {
      uint x;
      function f() public pure returns(uint) { return(5); }
      function g() public { x = this.f() + 1; }
  }"
  true

(* FunCall: multiple params, all correct *)
let%test "test_typecheck_funcall_expr_8" = test_typecheck
  "contract C {
      function f(uint a, int b) public pure returns(uint) { return(a); }
      function g() public { uint x; x = this.f(1, 2); }
  }"
  true

(* ProcCall: multiple params, second arg wrong type *)
let%test "test_typecheck_funcall_proccall_7" = test_typecheck
  "contract C {
      uint x;
      function f(uint a, int b) public { x = a; }
      function g() public { this.f(1, true); }
  }"
  false

let%test "test_nested_call" = test_typecheck
  "contract C {
    function f(uint x) public pure returns(uint) { return(x); }
    function g() public { uint x; x = this.f(this.f(1)); }
  }"
  true
