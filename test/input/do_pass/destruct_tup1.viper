let 
    a = (1, (2, (3, nil))),
    (v, (x, (y, z))) = a
in
    print(v);
    print(x);
    print(y);
    print(z);
    true