type ident = string

type ty_ident = string

type ty_field = {
  id: ident;
  ty: ident
}

and binder =
  | Raw of ident
  | Typed of ident * ident

and var_dec = {
  binder: binder;
  exp: expr
}

and ty =
  | TySimple of ident
  | TyRecord of ty_field list
  | TyArray  of ident

and ty_dec = {
  ident: ident;
  body: ty;
}

and ef_field = {
  ef_ident: ty_ident;
  ef_args: ty_ident list;
  ef_body: ty_ident;
}

and ef_decl = {
  e_name: ident;
  e_fields: ef_field list;
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
  fn_body: expr
}

and lvalue =
  | Id of ident
  | Field of lvalue * ident
  | ArrayIdx of lvalue * expr

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
  efid: ident;
  efty: expr
}

and expr =
  | Nil
  | LVal of lvalue
  | Hole of ident
  | Seq of expr * expr
  | Int of int
  | Str of string
  | Bin of op * expr * expr
  | Neg of expr
  | Record of ident * expr_field list
  | Apply of ident * expr list
  | Array of expr list
  | If of expr * expr * expr option
  | Perform of ident * expr list
  | Set of lvalue * expr
  | Let of decl list * expr
  | While of expr * expr
  | Break
  | NoOp