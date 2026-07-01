let  
  sum = (lambda(x): if x <= 0: 0 else: sum(x - 1) + x)
in
  sum(5)