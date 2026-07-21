let
  a = (lambda(op, arg): op(arg))
in
  a((lambda(x): add1(x)), 5)