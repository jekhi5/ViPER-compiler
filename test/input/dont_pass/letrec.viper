let rec
  sum = (lambda(a): if a == 0: a else: a + sum(sub1(a))),
  fact = (lambda(n): if n == 1: n else: n * (fact(sub1(n))))
in
  sum(5) + fact(3)