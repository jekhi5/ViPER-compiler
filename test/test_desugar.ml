open OUnit2
open Test_funcs


let suite = [
  (* This test will error while mutual recursion is unimplemented. *)
  terr "Desugar_multiple_declgroups"
    "def foo1(): 1 and def foo2(): 2 def bar1(): 1 and def bar2(): 2 bar1()"
    ""
    "Mutual recursion";
  
  t "Desugar_lambda_binds"
    "let f = (lambda(a, (b, (c, d), e), f): a + b + c + d + e + f) in f(1, (2, (3, 4), 5), 6)"
    ""
    "21";
  
  t "Desugar_try_catch_1"
    "1 check: 4 ! spits 5 end"
    ""
    "Ran 1 tessst...\nEvery tessssst passsssed.\n1";
]

module Suite : TestSuite = struct
  let suite = suite
end
