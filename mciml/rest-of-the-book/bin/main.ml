
open Parser
open Ast
open Lexing

let print_error_position lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.printf "Line:%d Position:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let () =
  let chan = open_in "test_suite/first.tg" in
  let buf = Lexing.from_channel chan in
  try print_endline (node_to_string (expr_to_node (entry Lexer.lex buf))) with
  | Parser.Error -> print_error_position buf