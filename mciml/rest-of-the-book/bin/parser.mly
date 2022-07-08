%{
 open Ast
%}

%token <int>    TNum
%token <string> TId
%token <string> TStr

%token KwType KwArray KwIf KwThen KwElse KwWhile
%token KwDo KwLet KwIn KwEnd KwOf KwEffect KwPerform KwFor KwTo
%token KwBreak KwNil KwFunction KwVar KwImport KwPrimitive

%token Eq EqEq Comma Colon Semi LPar RPar LBracket RBracket
%token LBrace RBrace Dot Plus Minus Slash LessGreater Less
%token LessEq Greater GreaterEq And Or ColonEq Star AndAnd OrOr Hat

%token Eof

%start <expr> entry

%nonassoc ColonEq KwDo KwOf
%left And Or
%nonassoc Greater GreaterEq Less LessEq LessGreater Eq
%left AndAnd OrOr Hat
%left Plus Minus
%left Slash Star
%right Semi
%nonassoc UMinus

%nonassoc KwThen
%nonassoc KwElse

%%

entry:
    | expr Eof { $1 }

decl:
    | tydec   { TyDec $1  }
    | vardec  { VarDec $1 }
    | fundec  { FunDec $1 }
    | ef_decl { EfDec $1 }

ident:
    | TId { ($1, $loc) }


ty_field:
    | ident Colon ident { { id = $1; ty = $3 }}
ty:
    | ident { TySimple $1 }
    | LBracket separated_list(Comma, ty_field) RBracket  { TyRecord ($2, $loc) }
    | KwArray KwOf ident { TyArray $3 }

tydec:
    | KwType ident Eq ty { { ident = $2; body = $4; dec_loc = $loc } }


ef_field:
    | ident LPar separated_list(Comma, ident) RPar Colon ident { { ef_ident = $1; ef_args = $3; ef_body = $6; ef_loc = $loc }}

ef_decl:
    | KwEffect ident LBracket separated_list(Comma, ef_field) RBracket { {e_name = $2; e_fields = $4; e_loc = $loc} }

(* VarDec *)

binder:
    | ident Colon ident { Typed ($1, $3, $loc) }
    | ident { Raw $1 }

vardec:
    | KwVar binder ColonEq expr { { var_binder = $2; var_exp = $4; var_loc = $loc } }

(* FunDec *)

fundec:
    | KwFunction ident LPar separated_list(Comma, ty_field) RPar option(Colon ident {$2}) Eq expr
        { { fn_name = $2; fn_args = $4; fn_ret = $6; fn_body = $8; fn_loc = $loc } }

(* Expr *)

opt(rule):
    | option(rule) {
        match $1 with
        | Some x -> x
        | None   -> NoOp
     }

l_value:
    | ident                      { Id $1 }
    | l_value Dot ident          { Field ($1, $3, $loc) }
    | l_value LBrace expr RBrace { ArrayIdx ($1, $3, $loc) }


%inline op:
    | Plus        { Plus }
    | Minus       { Minus }
    | Slash       { Div }
    | Star        { Mul }
    | Greater     { Greater }
    | GreaterEq   { GreaterEq }
    | Less        { Less }
    | LessEq      { LessEq }
    | And         { And }
    | Or          { Or }
    | AndAnd      { BinAnd }
    | OrOr        { BinOr }
    | Hat         { BinXor }
    | Eq          { Eq }
    | LessGreater { Diff }

field:
    | ident Eq expr { { eff_id = $1; eff_ty = $3; eff_loc = $loc } }

entry_l:
    | decl { [$1] }
    | decl entry_l { $1 :: $2 }

expr:
    | ident LBrace expr RBrace KwOf expr { Array ($1, $3, $6, $loc) }
    | l_value                                               { LVal $1 }
    | l_value ColonEq expr                                  { Set ($1, $3, $loc) }
    | expr op expr                                          { Bin ($2,$1,$3, $loc) }
    | expr Semi expr                                        { Seq ($1,$3, $loc) }
    | ident LBracket separated_list(Comma, field) RBracket  { Record ($1, $3, $loc) }
    | LPar opt(expr) RPar                                   { $2 }
    | KwNil                                                 { Nil $loc }
    | TStr                                                  { Str ($1, $loc) }
    | TNum                                                  { Int ($1, $loc) }
    | Minus expr %prec UMinus                               { Neg $2 }
    | ident LPar separated_list(Comma, expr) RPar           { Apply ($1, $3, $loc) }
    | KwIf expr KwThen expr KwElse expr                     { If ($2, $4, Some $6, $loc) }
    | KwIf expr KwThen expr                                 { If ($2, $4, None, $loc) }
    | KwLet entry_l KwIn expr KwEnd                           { Let ($2, $4, $loc)}
    | KwWhile expr KwDo expr KwEnd                          { While ($2, $4, $loc) }
    | KwBreak                                               { Break $loc }
    | KwPerform ident LPar separated_list(Comma, expr) RPar { Perform ($2, $4, $loc) }
    | KwFor ident ColonEq expr KwTo expr KwDo expr          { For ($2, $4, $6, $8)}