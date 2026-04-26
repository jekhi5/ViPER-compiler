def fact(n):
  if n == 0: 1
  else: n * fact(n - 1)

def throw():
  raise(RuntimeException)

def isTrue(b):
  isbool(b) && b

1 + 1

# Factorial checks
check:
  fact(3) spits 6,
  fact(5) bites 121
end

check:
  throw() sheds RuntimeException,
  5 sheds ValueException
end