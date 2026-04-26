let x = 1 in 
  x + (try let a = x in raise(RuntimeException) catch RuntimeException as b in 5)