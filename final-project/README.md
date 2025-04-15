# Compilers 4410 Final Project
# Implementation of check-expect style functionality

## Submission by Jacob Kline and Emery Jacobowitz
### Professor Benjamin Lerner
#### 04/2025

TODO: IMPLEMENT SYNTAX HIGHLIGHTING AND USE IT IN THE MARKDOWN CODE CELLS

# Syntax

For this implementation, we begin with the syntax of the proposed changes. The syntax that will be
supported looks like the following:

```
def fact(n):
  if n == 1: 1
  else: n * fact(n - 1)


check fact(1) spits 1
check fact(4) spits 24
check 24 spits fact(4)
check 9 spits true # False!
check (lambda(x): add1(x) - 5)(2) spits -2

fact(2)

check true spits true
check 1 + 4 spits 5
```

The expected output of this program would look something like this, with the first line being
the result of the program:

```
2

6 checks passed
1 check failed on line 11:
  check 9 spits true
```

You'll notice that `check-spit` statements are allowed at the topmost level of the code, both
before and after the final value would be returned.

# Kinds of check-spits we support