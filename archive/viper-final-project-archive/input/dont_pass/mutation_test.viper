def mutate(x, y):
  x[0] := y; x

1

check:
  let a = (1,2,3) in mutate(a, 4) spits mutate(a, 5)
end