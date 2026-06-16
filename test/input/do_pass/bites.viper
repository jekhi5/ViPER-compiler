1
check:
  1 bites 1,
  true bites true,
  (1, 2) bites (1, 2),
  1 bites 2,
  (1, 5) bites (5, 3, 2),
  (1, 2) bites (1, 2, 3),
  true bites false,
  let a = 1, b = 2, c = 3 in (a, b, c) bites let x = 1, y = 2, z = 3 in (x, y, z)
end