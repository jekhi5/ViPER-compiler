open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs

(* Runs a program, given as a source string, and compares its output to expected *)
let t (name : string) (program : string) (expected : string) =
  name >:: test_run program name expected
;;

(* Runs a program, given as an ANFed expr, and compares its output to expected *)
let ta (name : string) (program : tag expr) (expected : string) =
  name >:: test_run_anf program name expected
;;

(* Runs a program, given as a source string, and compares its error to expected *)
let te (name : string) (program : string) (expected_err : string) =
  name >:: test_err program name expected_err
;;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf (name : string) (program : 'a expr) (expected : unit expr) =
  name >:: fun _ -> assert_equal expected (anf (tag program)) ~printer:string_of_expr
;;

(* Checks if two strings are equal *)
let teq (name : string) (actual : string) (expected : string) =
  name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)
;;

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to expected *)
let tprog (filename : string) (expected : string) = filename >:: test_run_input filename expected

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to expected *)
let teprog (filename : string) (expected : string) = filename >:: test_err_input filename expected


let suite = "unit_tests" >::: []

(* input_file_test_suite () will run all the tests in the subdirectories of input/ *)
let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
