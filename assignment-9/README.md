Concrete Syntax:

<program>: 
  | <decls> <expr>
  | <expr>
<binop-expr>: 
  | IDENTIFIER
  | NUMBER
  | true
  | false
  | <prim1> ( <expr> )
  | <expr> <prim2> <expr>
  | IDENTIFIER ( <exprs> )
  | IDENTIFIER ( )
  | true
  | false
  | ( <expr> )
<prim1>: 
  | add1 | sub1
  | !
  | print | printStack
  | isbool | isnum
<prim2>: 
  | + | - | *
  | < | > | <= | >=
  | ==
  | && | ||
<decls>: 
  | <decl>
  | <decl> <decls>
<decl>: 
  | def IDENTIFIER ( <ids> ) : <expr>
  | def IDENTIFIER ( ) : <expr>
<ids>: 
  | IDENTIFIER
  | IDENTIFIER , <ids>
<expr>: 
  | let <bindings> in <expr>
  | let rec <bindings> in expr
  | if <expr> : <expr> else: <expr>
  | <binop-expr>
<exprs>: 
  | <expr>
  | <expr> , <exprs>
<bindings>: 
  | IDENTIFIER = <expr>
  | IDENTIFIER = <expr> , <bindings>