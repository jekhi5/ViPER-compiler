def fact(n):
  if n == 0: 1
  else: n * fact(n - 1)

1

check:
  1 spits 1,
  true spits true,
  (1, 2) spits (1, 2),
  1 spits 2,
  (1, 5) spits (5, 3, 2),
  (1, 2) spits (1, 2, 3),
  true spits false,
  let a = 1, b = 2, c = 3 in (a, b, c) spits let x = 1, y = 2, z = 3 in (x, y, z),
  fact(3) spits 6,
  fact(0) spits 1
end