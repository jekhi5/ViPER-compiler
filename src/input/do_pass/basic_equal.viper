let foo = (lambda(a, b): a + b) in
  let rec bar = (lambda(c, d): foo(c, d)) in
    bar(1, 2)