1
check:
  1 spits 1,
  true spits true,
  (1, 2) spits (1, 2),
  1 spits 2,
  (1, 5) spits (5, 3, 2),
  (1, 2) spits (1, 2, 3),
  true spits false,
  (let a = 1, b = 2, c = 3 in (1, 2, 3)) spits (1, 2, 3)
end