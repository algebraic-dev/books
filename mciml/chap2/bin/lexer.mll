(*

how you handle comments;
how you handle strings;
error handling;
end-of-file handling;
other interesting features of your lexer.


*)

{
    open Tokens
}

let digit = ['0'-'9']
let id = ['a'-'z'] ['a'-'z' '0'-'9' '_']*

rule lex = parse 
    | digit+ as num  { Num (int_of_string num) }
    | "="            { Eq }
    | ","            { Comma }
    | ":"            { Colon }
    | ";"            { Semi }
    | "("            { LPar }
    | ")"            { RPar }
    | "{"            { LBracket }
    | "}"            { RBracket }
    | "["            { LBrace }
    | "]"            { RBrace }
    | "."            { Dot }
    | "+"            { Plus }
    | "-"            { Minus }
    | "/"            { Div }
    | "<>"           { LessGreater }
    | "<"            { Less }
    | "<="           { LessEq }
    | ">"            { Greater }
    | ">="           { GreaterEq }
    | "&"            { And }
    | "|"            { Or }
    | ":="           { ColonEq }
    | id as id      { 
        match id with 
        | "function"  -> KwFunction
        | "import"    -> KwImport
        | "primitive" -> KwPrimitive
        | "type"    -> KwType
        | "array"   -> KwArray
        | "if"      -> KwIf
        | "then"    -> KwThen
        | "else"    -> KwElse
        | "while"   -> KwWhile
        | "for"     -> KwFor
        | "to"      -> KwTo
        | "do"      -> KwDo
        | "let"     -> KwLet
        | "in"      -> KwIn
        | "end"     -> KwEnd
        | "of"      -> KwOf
        | "break"   -> KwBreak
        | "nil"     -> KwNil
        | "var"     -> KwVar
        | id        -> Id id 
    }
    | "/*"          { comment 0 lexbuf } 
    | '"'           { str (Buffer.create 1) lexbuf }
    | " "+          { lex lexbuf }
    | ['\n' '\r']+  { lex lexbuf }
    | eof           { Eof } 


and str buf = parse 
    | '"'      { Str (Buffer.contents buf) }
    | "\\" (_ as chr)  { 
        let res = 
            match chr with 
            | 'a' ->  'a'
            | 'b' ->  'b'
            | 'f' ->  'f'
            | 'n' ->  '\n'
            | 'r' ->  '\r'
            | 't' ->  '\t'
            | 'v' ->  'v'
            | other -> other
        in 
        Buffer.add_char buf res; 
        str buf lexbuf
    }
    | eof      { failwith "End of string" }
    | _ as chr { Buffer.add_char buf chr; str buf lexbuf }

and comment lvl = parse 
    | "/*"          { comment (lvl + 1) lexbuf }
    | "*/"          { if lvl == 0 
                        then lex lexbuf
                        else comment (lvl - 1) lexbuf }
    | eof           { failwith "Oh no" }
    | _             { comment lvl lexbuf }