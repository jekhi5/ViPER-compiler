Concrete Syntax:

<expr>: 
  | let <bindings> in <expr>
  | if <expr> : <expr> else: <expr>
  | <binop-expr>
<binop-expr>: 
  | NUMBER
  | IDENTIFIER
  | add1 ( <expr> )
  | sub1 ( <expr> )
  | <expr> + <expr>
  | <expr> - <expr>
  | <expr> * <expr>
  | ( <expr> )
<bindings>: 
  | IDENTIFIER = <expr>
  | IDENTIFIER = <expr> , <bindings>