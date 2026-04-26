# The ViPER Compiler

## Verifying Programs Execute Right

Welcome to our compiler! We've worked very hard to make your experience with our language a positive
one. ViPER is a functional language. The most current version of our language exists in the [`src/`](src/) directory
This project is the culmination of several iterations of this compiler, each building on the one prior.
You can find each iteration alphabetically sorted in the [archive/](archive/) directory. The
[README](archive/README.md) there further explains this.

### Running your own programs

To run your own programs:

1. Write program files in the `src/input/do_pass` directory with the extension `*.viper`
2. Run the [`./src/run`](./src/run) script to compile your program
3. Run the compiled `*.run` file at `output/do_pass/YOUR_PROG_NAME.run`

Thank you for using our language! We hope your programs execute right!

#### ~ Jacob Kline and Emery Jacobowitz, Northeastern University Khoury College of Computer Science class of '25

## Syntax for `try-catch` and `checks`

```viper
def fact(n):
  if (n < 0): raise(ValueException)
  else:
    (if n == 1: 1
    else: n * fact(n - 1))

def lessThanFive(x):
  if x < 5: true else: false

def tryAddFact(n1, n2):
  try
    fact(n1) + fact(n2)
  catch ValueException as e in
    0


fact(3)

check:
  fact(1) spits 1,
  fact(4) spits 24,
  24 bites fact(4)
end

check:
  9 spits true, # False!
  fact(-1) sheds ValueException,
  (lambda(x): add1(x) - 5)(2) spits -2,
  8 broods lessThanFive
end

check:
  tryAddFact(3, 2) spits 8,
  tryAddFact(-5, 100000) spits 0,
  tryAddFact(3, -4) spits 6 # False!
end
```

The expected output of this program would look something like this (The last line is the output
of the program):

```text
Ran 10 tessstsss...
Failuresss (3):
> Tesssst from (ln 26, col 2) to (ln 26, col 14) failed -- Expected:
>   true
> But received:
>   9

< Tesssst from (ln 29, col 2) to (ln 29, col 23) failed -- Expected:
<   true
< But received:
<   false

> Tesssst from (ln 35, col 2) to (ln 35, col 27) failed -- Expected:
>   6
> But received:
>   0

==================== Tests Complete ====================

6
```

`check` blocks are allowed only at the top level of the program and are run after the body of
the program is run.

### Kinds of check-spits we support

(`!` can be used to negate all tests except sheds)

- `spits` - deep equality
  - Syntax:
    - `<expr> spits <expr>`
  - Example:
    - `(1, 2, 3) spits (lambda(): (1, 2, 3))()`
- `bites` - shallow equality
  - Syntax:
    - `<expr> bites <expr>`
      Example:
    - `(1, 2, 3) bites (1, 2, 3)`
    - `(1, 2, 3) ! bites (lambda(): (1, 2, 3))()`
- `broods` - test against a predicate
  - Syntax:
    - `<expr> broods <Predicate>`
      Example:
    - `5 broods (lambda(x): x < 5)`

```viper
def lessThanFive(x):
  x < 5
.
.
.
3 broods lessThanFive
```

- `sheds` - test that something raises a specific exception
  - Syntax:
    - `<expr> sheds <NameOfException>`
      Example:
    - `raise(RuntimeException) sheds RuntimeException`
