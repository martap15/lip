(******************************************************************************)
(*                                    Tinysol CLI                             *)
(******************************************************************************)

open Ast

type cli_cmd = 
  | Faucet of addr * int
  | Deploy of transaction * ide * string
  | CallFun of transaction
  | Revert of transaction
  | Assert of addr * expr
  | LastReverted 
  | NotLastReverted 
  | SetBlockNum of int