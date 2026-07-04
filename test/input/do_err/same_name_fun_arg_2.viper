let rec foo = (lambda(x):
    if x == 0:
        x
    else:
        let 
            shadow foo = x
        in
            foo(print(foo - 1)))
in
foo(5)