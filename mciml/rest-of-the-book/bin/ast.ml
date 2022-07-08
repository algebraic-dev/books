
type loc = Lexing.position * Lexing.position

type ty_ident = string * loc

type ident = string * loc

type op =
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
  | Eq
  [@@deriving show]

type ty_field = {
  id: ident;
  ty: ident
}

and binder =
  | Raw of ident
  | Typed of ident * ident * loc

and var_dec = {
  var_binder: binder;
  var_exp: expr;
  var_loc: loc;
}

and ty =
  | TySimple of ident
  | TyRecord of ty_field list  * loc
  | TyArray  of ident

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
  | Array of ident * expr * expr * loc
  | If of expr * expr * expr option * loc
  | Perform of ident * expr list * loc
  | Set of lvalue * expr * loc
  | Let of decl list * expr * loc
  | For of ident * expr * expr * expr
  | While of expr * expr * loc
  | Break of loc
  | NoOp

type node =
  | Node of string * node list

let rec print_node (last: bool) (ident: string) (Node (label, ys)): string =
  let rec mapper = function
    | []        -> []
    | [x]       -> [print_node true (ident ^ (if last then "  " else "| ")) x]
    | (x :: xs) -> (print_node false (ident ^ (if last then "  " else "| ")) x) :: mapper xs
  in ident ^ (if last then "'-" else "|-") ^ label ^ "\n" ^ String.concat "" (mapper ys)

let node_to_string node : string = print_node true "" node

let r_col (pos : Lexing.position) = (pos.pos_cnum - pos.pos_bol + 1)
let range_to_text ((start, end') : loc) =
  string_of_int (r_col start) ^ "-" ^ string_of_int start.pos_lnum ^ ":" ^
  string_of_int (r_col end') ^ "-" ^ string_of_int end'.pos_lnum

let ident_to_str ((name, loc)) = "(" ^ name ^ " " ^ range_to_text loc ^ ")"

let ident_to_node ident = Node ("Ident: " ^ ident_to_str ident, [])

let loc_to_node loc = Node ("Range: " ^ range_to_text loc, [])

let opt_to_node (fn: 'a -> node) (opt: 'a option) : node =
  match opt with
  | Some res -> Node ("Some", [fn res])
  | None     -> Node ("None", [])

let rec lval_to_node = function
  | Id ident                   -> Node ("Id " ^ ident_to_str ident, [])
  | Field (val', ident, loc)   -> Node ("Field", [lval_to_node val'; (Node ("Ident: " ^ ident_to_str ident, [])); loc_to_node loc])
  | ArrayIdx (val', expr, loc) -> Node ("ArrayIdx", [lval_to_node val'; expr_to_node expr; loc_to_node loc ])

and expr_field_to_node expr =
  Node ("ExprField", [ident_to_node expr.eff_id; expr_to_node expr.eff_ty])

and ty_field_to_node field =
  Node ("TyField", [ident_to_node field.id; ident_to_node field.ty])

and ty_to_node = function
  | TySimple (ident) -> Node ("TySimple", [ident_to_node ident])
  | TyRecord (fields, _) -> Node ("TyRecord", List.map ty_field_to_node fields)
  | TyArray  (ident, _) -> Node ("TyArray of " ^ ident, [])

and binder_to_node = function
  | Raw (name, _)            -> Node (("Raw: " ^ name), [])
  | Typed ((name, _), ty, _) -> Node (("Typed: " ^ name ^ " " ^ ident_to_str ty), [])

and var_dec_to_node dec =
  Node ("VarDec", [binder_to_node dec.var_binder; expr_to_node dec.var_exp])

and func_dec fn =
  Node ("Fun", [ident_to_node fn.fn_name; Node ("List",[]); opt_to_node ident_to_node fn.fn_ret; expr_to_node fn.fn_body])

and expr_to_node = function
  | Nil _             -> Node ("Nil", [])
  | LVal lval         -> Node ("LVal", [lval_to_node lval])
  | Hole ident        -> Node ("Hole:" ^ ident_to_str ident, [])
  | Seq (a, b, loc)   -> Node ("Seq: " ^ range_to_text loc, [expr_to_node a; expr_to_node b])
  | Int (i, loc)      -> Node ("Int: " ^ string_of_int i ^ " " ^ range_to_text loc, [])
  | Str (i, loc)      -> Node ("Str: " ^ i ^ " " ^ range_to_text loc, [])
  | Bin (o, a, b, l)  -> Node ("Bin: " ^ show_op o ^ range_to_text l, [expr_to_node a; expr_to_node b])
  | Neg expr          -> Node ("Neg: ", [expr_to_node expr])
  | Record (n, f, _)  -> Node ("Record: " ^ ident_to_str n, List.map expr_field_to_node f)
  | Apply (i, a, _)   -> Node ("Apply: " ^ ident_to_str i, List.map expr_to_node a)
  | Array (a,b,c,_)   -> Node ("Array: ", [ident_to_node a;expr_to_node b;expr_to_node c])
  | If (a, b, c, _)   -> Node ("If: ", [expr_to_node a; expr_to_node b; opt_to_node expr_to_node c])
  | Perform (i, e, _) -> Node ("Perform", [ident_to_node i] @ (List.map expr_to_node e))
  | Set (l, e, _)     -> Node ("Set", [lval_to_node l; expr_to_node e])
  | Let (d, e, _)     -> Node ("Let", (List.map decl_to_node d) @ [expr_to_node e])
  | While (e, f, _)   -> Node ("While", [expr_to_node e; expr_to_node f])
  | Break _           -> Node ("Break", [])
  | NoOp              -> Node ("NoOp", [])
  | For ((e, _), f, g, _) -> Node ("For: " ^ e, [expr_to_node f; expr_to_node g])

and func_dec_to_node fndec =
  Node ("FnDec",
    [ ident_to_node fndec.fn_name
    ; Node ("List", List.map ty_field_to_node fndec.fn_args)
    ; opt_to_node ident_to_node fndec.fn_ret
    ; expr_to_node fndec.fn_body
    ])

and ty_dec_to_node tydec =
  Node ("TyDec",
    [ ident_to_node tydec.ident
    ; ty_to_node tydec.body
    ])

and ef_field_to_node effield =
  Node ("EfField",
    [ ident_to_node effield.ef_ident ]
    @ List.map ident_to_node effield.ef_args
    @ [ident_to_node effield.ef_body])

and ef_dec_to_node efdec =
  Node ("EfDec",
    [ ident_to_node efdec.e_name ]
    @ List.map ef_field_to_node efdec.e_fields
    )

and decl_to_node = function
  | VarDec dec -> var_dec_to_node dec
  | FunDec dec -> func_dec_to_node dec
  | TyDec dec  -> ty_dec_to_node dec
  | EfDec dec  -> ef_dec_to_node dec

and list_to_node fn decls =
  Node ("List", List.map fn decls)