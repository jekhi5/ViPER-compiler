Concrete Syntax:

<expr>: 
  | NUMBER
  | IDENTIFIER
  | ( let ( <bindings> ) <expr> )
  | ( add1 <expr> )
  | ( sub1 <expr> )
<bindings>: 
  | ( IDENTIFIER <expr> )
  | ( IDENTIFIER <expr> ) <bindings>