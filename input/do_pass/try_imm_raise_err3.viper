def throw(x):
  raise(RuntimeException)

let a = 5 in try throw(a) catch RuntimeException as e in 5