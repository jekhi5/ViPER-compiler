# This test shows that both errors inside function declarations,
# and in the main program body,
# are caught and reported together.
# Note that this happens in a consistent order, but we don't really care.

def foo(a):
    1 + x

let 
    x = 1,
    y = y
in
    foo(x, y)