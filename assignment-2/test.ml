open Compile
open Runner
open Printf
open OUnit2
open Sexp
open ExtLib

(* Runs a program, given as a source string, and compares its output to expected *)
let t (name : string) (program : string) (expected : string) : OUnit2.test =
  name >:: test_run program name expected
;;

(* Runs a program, given as a source string, and compares its error to expected *)
let te (name : string) (program : string) (expected_err : string) : OUnit2.test =
  name >:: test_err program name expected_err
;;

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to expected *)
let ti (filename : string) (expected : string) = filename >:: test_run_input filename expected

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to expected *)
let tie (filename : string) (expected_err : string) =
  filename >:: test_err_input filename expected_err
;;

(* A helper for testing primitive values (won't print datatypes well) *)
let t_any name value expected = name >:: fun _ -> assert_equal expected value ~printer:dump

(* A helper for testing raised errors *)
let t_error name expr (expected : exn) = name >:: fun _ -> assert_raises expected expr

let expr_of_sexp_tests =
  [ t_any "number" (expr_of_sexp (parse "5")) (Number (5L, (0, 0, 0, 1)));
    t_any "false" (expr_of_sexp (parse "false")) (Id ("false", (0, 0, 0, 5)));
    t_any "true" (expr_of_sexp (parse "true")) (Id ("true", (0, 0, 0, 4)));
    t_error "add1-error"
      (fun _ -> expr_of_sexp (parse "add1"))
      (SyntaxError "Invalid syntax on `add1` at line 0, col 0") ]
;;

let suite : OUnit2.test =
  "suite"
  >::: [te "forty_one" "41" "not yet implemented"; te "nyi" "(let ((x 10)) x)" "not yet implemented"]
       @ expr_of_sexp_tests
;;

let () = run_test_tt_main suite
