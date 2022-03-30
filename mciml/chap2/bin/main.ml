
open Tokens
open Lexer 

let () =
  let buf = Lexing.from_string "be /* aaaa/* be */ aaaaaa */ ata \"bbb\" e" in
  let rec loop buf = (
      let tkn = lex buf in
      print_endline (show_token tkn);
      match tkn with 
      | Eof -> print_endline "."
      | _ -> loop buf )
  in loop buf