let
  (a, b, c) = (1, 2, (3, 4)),
  _ = print(a + b)
in
  c[1]