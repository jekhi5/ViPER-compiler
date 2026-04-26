def throw(x):
  raise(RuntimeException)

let a = 5 in try throw(a) catch ValueException as e in 5