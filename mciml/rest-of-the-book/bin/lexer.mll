{
    open Tokens
    open Lexing

    let match_id id =
        match id with
        | "function"  -> KwFunction
        | "import"    -> KwImport
        | "primitive" -> KwPrimitive
        | "type"      -> KwType
        | "array"     -> KwArray
        | "if"        -> KwIf
        | "then"      -> KwThen
        | "else"      -> KwElse
        | "let"       -> KwLet
        | "for"       -> KwFor
        | "in"        -> KwIn
        | "effect"    -> KwEffect
        | "perform"   -> KwPerform
        | "end"       -> KwEnd
        | "of"        -> KwOf
        | "nil"       -> KwNil
        | "var"       -> KwVar
        | "do"        -> KwDo
        | "to"        -> KwTo
        | id          -> TId id

    let new_line lexbuf =
        let lcp = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <- { lcp with
            pos_lnum = lcp.pos_lnum + 1;
            pos_bol = lcp.pos_cnum;
        }
}

let digit = ['0'-'9']
let id = ['a'-'z'] ['a'-'z' '0'-'9' '_']*

rule lex = parse
    | '\n'           { new_line lexbuf; lex lexbuf }
    | '\r'           { lex lexbuf }
    | digit+ as num  { TNum (int_of_string num) }
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
    | "*"            { Star }
    | "/"            { Slash }
    | "<>"           { LessGreater }
    | "<"            { Less }
    | "<="           { LessEq }
    | ">"            { Greater }
    | ">="           { GreaterEq }
    | "&"            { And }
    | "|"            { Or }
    | ":="           { ColonEq }
    | id as id       { match_id id }
    | "/*"           { comment 0 lexbuf }
    | '"'            { str (Buffer.create 1) lexbuf }
    | " "+           { lex lexbuf }
    | eof            { Eof }


and str buf = parse
    | '"'      { TStr (Buffer.contents buf) }
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