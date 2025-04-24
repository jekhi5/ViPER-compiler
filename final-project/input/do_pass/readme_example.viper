def fact(n):
  if (n < 0): raise(ValueException)
  else:
    (if n == 1: 1
    else: n * fact(n - 1))

def lessThanFive(x):
  if x < 5: true else: false

def tryAddFact(n1, n2):
  try
    fact(n1) + fact(n2)
  catch ValueException as e in
    0
      

fact(3)

check:
  fact(1) spits 1,
  fact(4) spits 24,
  24 bites fact(4)
end

check:
  9 spits true, # False!
  fact(-1) sheds ValueException,
  (lambda(x): add1(x) - 5)(2) spits -2,
  8 broods lessThanFive
end

check:
  tryAddFact(3, 2) spits 8,
  tryAddFact(-5, 100000) spits 0,
  tryAddFact(3, -4) spits 6 # False!
end