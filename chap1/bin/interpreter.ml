open Ast

let get_op = function 
  | Plus  -> ( + )
  | Minus -> ( - )
  | Times -> ( * )
  | Div   -> ( / )

let operate fn op (tbl, res) = let (tbl', res2) = fn tbl in (tbl', op res res2)
 
let flip fn a b = fn b a 

let on fn b c d = fn (b c) (b d)

let concat_map fn sep ls = List.map fn ls |> String.concat sep

let update id value tbl = (id, value) :: tbl

let lookup id tbl = List.find (fun x -> fst x = id) tbl |> snd

let rec interp table = function 
  | CompoundStm (a, b) -> let table' = interp table a in interp table' b
  | AssignStm (id, exp) -> let (tbl, res) = interp_exp table exp in update id res tbl
  | PrintStm exp ->
      let (tbl, res) = List.fold_right (fun exp -> operate (flip interp_exp exp) (flip List.cons)) exp (table, []) in
      print_endline (concat_map string_of_int " " res);
      tbl

and interp_exp table = function 
  | IdExp name         -> (table, lookup name table)
  | NumExp num         -> (table, num)
  | OpExp (ep, op, e2) -> operate (flip interp_exp e2) (get_op op) (interp_exp table ep)
  | EseqExp (stm, exp) -> interp_exp (interp table stm) exp

let rec max_args = function 
  | CompoundStm (a, b) -> (on max max_args) a b
  | AssignStm (_, exp) -> max_args_exp exp
  | PrintStm exp -> List.fold_left max (List.length exp) (List.map max_args_exp exp)
and max_args_exp = function 
  | IdExp _            -> 0
  | NumExp _           -> 0
  | OpExp (ep, _, e2)  -> (on max max_args_exp) ep e2
  | EseqExp (stm, exp) -> max (max_args stm) (max_args_exp exp)

let prog =
  CompoundStm (
    AssignStm("a",OpExp(NumExp 5, Plus, NumExp 3)),
    CompoundStm (
      AssignStm("b", 
        EseqExp(PrintStm [IdExp "a"; OpExp (IdExp "a", Minus, NumExp 1)],
                OpExp(NumExp 10, Times, IdExp"a"))),
    PrintStm[IdExp "b"]))