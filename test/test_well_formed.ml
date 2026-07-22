open OUnit2
open Test_funcs
open Well_formed

let tests =
  [ terr "WF_Overflow_literal_pos" "4611686018427387904" "" "number literal";
    terr "WF_Overflow_literal_neg" "-4611686018427387905" "" "number literal";
    terr "WF_Shadow_Bind" "let a = 1 in let a = 2 in a" "" "shadows one";
    terr "WF_lambda_dupe_arg_simple" "(lambda(x, x): x)(1, 2)" "" "duplicates one at";
    terr "WF_lambda_dupe_arg_nested" "(lambda(x, (_, x)): x)(1, (2, 3))" "" "duplicates one at";
    terr "WF_testop2_pred" "def positive(x): x > 0 1 check: 1 + 2 broods positive " "" "1" ]
;;

let try_catch_tests =
  [ t "WF_TC_blank" "try raise(RuntimeException) catch RuntimeException as _ in 1" "" "1";
    terr "WF_TC_tup" "try raise(RuntimeException) catch RuntimeException as (a, b) in 1" ""
      "Tuple binding in try-catch"
    (* terr "WF_TC_tup" "try 1 catch false as e in e" "" "Can only catch exceptions"; *) ]
;;

module Suite : TestSuite = struct
  let suite = tests @ try_catch_tests
end
