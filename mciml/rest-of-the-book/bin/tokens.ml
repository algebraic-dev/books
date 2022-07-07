type token =
  | TNum of int
  | TId of string
  | TStr of string

  | KwType | KwArray | KwIf  | KwThen  | KwElse | KwLet | KwPerform
  | KwIn | KwEnd | KwOf
  | KwNil | KwFunction | KwVar | KwImport | KwPrimitive
  | KwWhile | KwDo | KwEffect

  | Eq | Comma | Colon | Semi | LPar | RPar | LBracket | RBracket
  | LBrace | RBrace | Dot | Plus | Minus | LessGreater | Less
  | LessEq | Greater | GreaterEq | And | Or | ColonEq | Star | Slash
  | AndAnd | OrOr | Hat

  | Eof
  [@@deriving show {with_path = false}]