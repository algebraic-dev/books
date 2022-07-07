
type loc = Lexing.position * Lexing.position

type ty_ident = string * loc

type ident = string * loc

type ty_field = {
  id: ident;
  ty: ident
}

and binder =
  | Raw of ident * loc
  | Typed of ident * ident * loc

and var_dec = {
  var_binder: binder;
  var_exp: expr;
  var_loc: loc;
}

and ty =
  | TySimple of ident * loc
  | TyRecord of ty_field list  * loc
  | TyArray  of ident * loc

and ty_dec = {
  ident: ident;
  body: ty;
  dec_loc: loc;
}

and ef_field = {
  ef_ident: ty_ident;
  ef_args: ty_ident list;
  ef_body: ty_ident;
  ef_loc: loc;
}

and ef_decl = {
  e_name: ident;
  e_fields: ef_field list;
  e_loc: loc;
}

and decl =
  | TyDec of ty_dec
  | VarDec of var_dec
  | FunDec of func_dec
  | EfDec of ef_decl

and func_dec = {
  fn_name: ident;
  fn_args: ty_field list;
  fn_ret: ident option;
  fn_body: expr;
  fn_loc: loc;
}

and lvalue =
  | Id of ident
  | Field of lvalue * ident * loc
  | ArrayIdx of lvalue * expr * loc

and op =
  | Plus
  | Minus
  | Div
  | Mul
  | Greater
  | Less
  | GreaterEq
  | LessEq
  | And
  | Or
  | BinAnd
  | BinOr
  | BinXor
  | Diff
  | EqEq

and expr_field = {
  eff_id: ident;
  eff_ty: expr;
  eff_loc: loc;
}

and expr =
  | Nil of loc
  | LVal of lvalue
  | Hole of ident
  | Seq of expr * expr * loc
  | Int of int * loc
  | Str of string * loc
  | Bin of op * expr * expr * loc
  | Neg of expr
  | Record of ident * expr_field list * loc
  | Apply of ident * expr list * loc
  | Array of expr list * loc
  | If of expr * expr * expr option * loc
  | Perform of ident * expr list * loc
  | Set of lvalue * expr * loc
  | Let of decl list * expr * loc
  | While of expr * expr * loc
  | Break of loc
  | NoOp