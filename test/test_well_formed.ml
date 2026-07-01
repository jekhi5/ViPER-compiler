open OUnit2
open Test_funcs

open Well_formed

let tests = [
  terr 
    "WF_Overflow_literal_pos"
    "4611686018427387904"
    ""
    "number literal";
  terr
    "WF_Overflow_literal_neg"
    "-4611686018427387905"
    ""
    "number literal";

  terr
    "WF_Shadow_Bind"
    "let a = 1 in let a = 2 in a"
    ""
    "shadows one";
]


module Suite : TestSuite = struct
  let suite = tests
end