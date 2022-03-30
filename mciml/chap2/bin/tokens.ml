type token = 
  | Num of int
  | Id of string
  | Str of string

  | KwType | KwArray | KwIf  | KwThen  | KwElse | KwWhile
  | KwFor  | KwTo | KwDo | KwLet | KwIn | KwEnd | KwOf 
  | KwBreak | KwNil | KwFunction | KwVar | KwImport | KwPrimitive

  | Eq | Comma | Colon | Semi | LPar | RPar | LBracket | RBracket 
  | LBrace | RBrace | Dot | Plus | Minus | Div | LessGreater | Less 
  | LessEq | Greater | GreaterEq | And | Or | ColonEq

  | Eof 
  [@@deriving show {with_path = false}]