def gtv(a): a > 5

def ltiii(b): b < 3

def f(x): !(ltiii(x)) && !(gtv(x))

1
check:
    6 broods gtv,
    1 ! broods gtv
end

check:
    4 ! broods ltiii,
    4 broods f,
    4 ! broods gtv
end