Concrete Syntax:

<prim1>: ...
  | !
  | print
  | isbool
  | isnum
<expr>: ...
  | true
  | false
  | <expr> < <expr>
  | <expr> > <expr>
  | <expr> <= <expr>
  | <expr> >= <expr>
  | <expr> == <expr>
  | <expr> && <expr>
  | <expr> || <expr>