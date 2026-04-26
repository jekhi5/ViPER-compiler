let x = 1 in 
  x + (try let a = 1 in raise(RuntimeException) catch RuntimeException as b in 5)