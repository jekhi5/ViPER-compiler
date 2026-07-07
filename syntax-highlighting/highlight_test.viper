# Syntax highlighting test. This exercises every rule in viper.tmLanguage.json
# Some features (like floats or strings) are highlighted but will obviously
# not run until they're implements

# Also, you should be able to highlight text and press (, ", ', and [ to enclose
# that text in the given character

# ── storage.type.function: def, and def ──────────────────────────────────────
def isEven(n):
  if n == 0: true
  else: isOdd(n - 1)
and def isOdd(n):
  if n == 0: false
  else: isEven(n - 1)

# ── support.function.builtin + keyword.operator.* ────────────────────────────
def allOps(x, y):
  let
    a      = add1(x),
    b      = sub1(y),
    prod   = x * y,
    diff   = x - y,
    total  = a + b,
    cmp    = x < y && x <= y && x > 0 && x >= 0 && x == y,
    logic  = isnum(x) && !(isbool(x)) || istuple((x,))
  in
    print(total);
    prod

# ── support.type.exception + try/catch/raise ─────────────────────────────────
def mustBePos(n):
  if n <= 0: raise(ValueException)
  else: n

def safeRun(n):
  try
    mustBePos(n)
  catch ValueException as e in
    0

def raisesRuntime(n):
  try
    raise(RuntimeException)
  catch RuntimeException as e in
    n

# ── keyword.other: shadow  +  begin/end  +  ; sequencing ─────────────────────
def shadowAndSeq(x):
  let shadow x = x + 10
  in begin
    print(x);
    printStack(x);
    x
  end

# ── higher-order + tuple indexing + := mutation ───────────────────────────────
def applyTwice(f, x):
  f(f(x))

def tupleOps(t):
  let
    first = t[0],
    _     = t[0] := 99
  in
    print(first);
    t

# ── Main expression: let rec, lambda, λ, zero-arg lambda, nil ────────────────
let rec
  fact = (lambda(n):
    if n == 0: 1
    else: n * fact(n - 1))
in
let
  doubled = applyTwice((lambda(x): x * 2), 3),
  zero_arg = (lambda: nil),
  unicode = (λ(x): add1(x)),
  tup     = (10, 20, 30),
  flags   = true && !(false) || false
in let shadow flags = !(flags)
in
  print(fact(5));
  print(doubled);
  print(unicode(4));
  print(flags);
  safeRun(0);
  raisesRuntime(7);
  tupleOps(tup)

# ── Check blocks: spits, bites, sheds, broods (and negated forms) ─────────────
check:
  isEven(4)                          spits true,
  isEven(3)                          spits false,
  isOdd(5)                           spits true,
  isEven(4)                          bites true,
  (1, 2)                             ! bites (1, 3),
  safeRun(0)                         spits 0,
  mustBePos(-1)                      sheds ValueException,
  raisesRuntime(7)                   spits 7,
  4                                  broods isEven,
  3                                  ! broods isEven,
  isEven(3)                          ! spits true,
  applyTwice((lambda(x): x * 2), 3) spits 12
end

check:
  fact(5)         spits 120,
  fact(0)         spits 1,
  isnum(42)       spits true,
  isbool(true)    spits true,
  istuple((1, 2)) spits true
end
