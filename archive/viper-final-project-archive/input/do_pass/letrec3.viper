let 
  a = 5
in
  let rec
    sum = (lambda(x):
      if x == 0:
          a 
      else:
          x + sum(x - 1))
  in
    sum(a)