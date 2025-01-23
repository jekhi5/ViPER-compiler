{
  open Lexing
  open Parser
  open Printf
}

let dec_digit = ['0'-'9']
let signed_int = dec_digit+ | ('-' dec_digit+)

let ident = ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*

let blank = [' ' '\t']+

rule token = parse
  | blank { token lexbuf }
  | '\n' { new_line lexbuf; token lexbuf }
  | signed_int as x { NUM (Int64.of_string x) }
  | "add1" { ADD1 }
  | "sub1" { SUB1 }
  | "if" { IF }
  | ":" { COLON }
  | "else:" { ELSECOLON }
  | "let" { LET }
  | "in" { IN }
  | "=" { EQUAL }
  | "," { COMMA }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { TIMES }
  | ident as x { ID x }
  | eof { EOF }
  | _ as c { failwith (sprintf "Unrecognized character: %c" c) }

