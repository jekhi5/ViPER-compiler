let 
    a = 5 + 6,
    b = 10 - (if a > 7: 7 else: 9),
    c = let shadow a = b in a == b,
    d = (if isbool(a) || isnum(b): c else: b)
in
    isnum(a) && isnum(d)