%{
 open Ast
%}

%token <int>    TNum
%token <string> TId
%token <string> TStr

%token KwType KwArray KwIf KwThen KwElse KwWhile
%token KwDo KwLet KwIn KwEnd KwOf TwEffect KwPerform
%token KwBreak KwNil KwFunction KwVar KwImport KwPrimitive

%token Eq EqEq Comma Colon Semi LPar RPar LBracket RBracket
%token LBrace RBrace Dot Plus Minus Slash LessGreater Less
%token LessEq Greater GreaterEq And Or ColonEq Star AndAnd OrOr Hat

%token Eof

%start <decl list> entry

%nonassoc ColonEq
%left And Or
%nonassoc Greater GreaterEq Less LessEq LessGreater EqEq
%left AndAnd OrOr Hat
%left Plus Minus
%left Slash Star
%right Semi
%nonassoc UMinus

%nonassoc KwThen
%nonassoc KwElse

%%

entry:
    | decl entry { $1 :: $2 }
    | Eof { [] }

decl:
    | tydec   { TyDec $1  }
    | vardec  { VarDec $1 }
    | fundec  { FunDec $1 }
    | ef_decl { EfDec $1 }

ty_id:
    | TId { $1 }

ty_field:
    | TId Colon ty_id { { id = $1; ty = $3 }}
ty:
    | ty_id { TySimple $1 }
    | LBracket separated_list(Comma, ty_field) RBracket  { TyRecord $2 }
    | KwArray KwOf ty_id { TyArray $3 }

tydec:
    | KwType TId Eq ty { { ident = $2; body = $4 } }


ef_field:
    | TId LPar separated_list(Comma, ty_id) RPar Colon ty_id { { ef_ident = $1; ef_args = $3; ef_body = $6 }}

ef_decl: 
    | TwEffect TId LBracket separated_list(Comma, ef_field) RBracket { {e_name = $2; e_fields = $4} }

(* VarDec *)

binder:
    | TId Colon ty_id { Typed ($1, $3) }
    | TId { Raw $1 }

vardec:
    | KwVar binder ColonEq expr { { binder = $2; exp = Hole "?"} }

(* FunDec *)

fundec:
    | KwFunction TId LPar separated_list(Comma, ty_field) RPar option(Colon ty_id {$2}) Eq expr 
        { { fn_name = $2; fn_args = $4; fn_ret = $6; fn_body = $8 } }

(* Expr *)

opt(rule):
    | option(rule) {
        match $1 with
        | Some x -> x
        | None   -> NoOp
     }

l_value:
    | TId { Id $1 }
    | l_value Dot TId { Field ($1, $3) }
    | l_value LBrace expr RBrace { ArrayIdx ($1, $3) }


%inline op:
    | Plus { Plus }
    | Minus { Minus }
    | Slash { Div }
    | Star { Mul }
    | Greater { Greater }
    | GreaterEq { GreaterEq }
    | Less { Less }
    | LessEq { LessEq }
    | And { And }
    | Or { Or }
    | AndAnd { BinAnd }
    | OrOr { BinOr }
    | Hat { BinXor }
    | EqEq { EqEq }
    | LessGreater { Diff }

field:
    | TId Eq expr { { efid = $1; efty = $3 } }

expr:
    | LPar opt(expr) RPar { $2 }
    | l_value             { LVal $1 }
    | l_value ColonEq expr { Set ($1, $3) }
    | KwNil               { Nil }
    | TStr                { Str $1 }
    | TNum                { Int $1 }
    | Minus expr %prec UMinus { Neg $2 }
    | TId LPar separated_list(Comma, expr) RPar { Apply ($1, $3) }
    | expr op expr { Bin ($2,$1,$3) }
    | expr Semi expr { Seq ($1,$3) }
    | ty_id LBracket separated_list(Comma, field) RBracket { Record ($1, $3) }
    | LBrace separated_list(Comma, expr) RBrace { Array $2 }
    | KwIf expr KwThen expr KwElse expr { If ($2, $4, Some $6) }
    | KwIf expr KwThen expr { If ($2, $4, None) }
    | KwLet entry KwIn expr KwEnd { Let ($2, $4)}
    | KwWhile expr KwDo expr KwEnd { While ($2, $4) }
    | KwBreak { Break }
    | KwPerform TId LPar separated_list(Comma, expr) RPar { Perform ($2, $4) }