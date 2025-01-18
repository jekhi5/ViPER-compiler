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
    t_error "add1-error-no-args"
      (fun _ -> expr_of_sexp (parse "add1"))
      (SyntaxError "Invalid syntax on `add1` at line 0, col 0");
    t_error "add1-error-many-args"
      (fun _ -> expr_of_sexp (parse "(add1 1 2)"))
      (SyntaxError "Invalid syntax at line 0, col 0--line 0, col 10");
    t_error "sub1-error-no-args"
      (fun _ -> expr_of_sexp (parse "sub1"))
      (SyntaxError "Invalid syntax on `sub1` at line 0, col 0");
    t_error "sub1-error-many-args"
      (fun _ -> expr_of_sexp (parse "(sub1 1 2)"))
      (SyntaxError "Invalid syntax at line 0, col 0--line 0, col 10");
    t_error "let-error-no-nest"
      (fun _ -> expr_of_sexp (parse "let"))
      (SyntaxError "Invalid syntax on `let` at line 0, col 0");
    t_error "let-error-no-bindings"
      (fun _ -> expr_of_sexp (parse "(let () 5)"))
      (SyntaxError "Invalid syntax: A `let` requires at least one binding at line 0, col 5");
    t_any "let-one-binding"
      (expr_of_sexp (parse "(let ((x 5)) x)"))
      (Let ([("x", Number (5L, (0, 9, 0, 10)))], Id ("x", (0, 13, 0, 14)), (0, 0, 0, 15)));
    t_any "let-many-bindings"
      (expr_of_sexp (parse "(let ((x 5) (y (sub1 10))) (add1 x))"))
      (Let
         ( [ ("x", Number (5L, (0, 9, 0, 10)));
             ("y", Prim1 (Sub1, Number (10L, (0, 21, 0, 23)), (0, 15, 0, 24))) ],
           Prim1 (Add1, Id ("x", (0, 33, 0, 34)), (0, 27, 0, 35)),
           (0, 0, 0, 36)));
    (* TODO: Add a test that shows it will syntax error when theres a syntax error in a let binding *)
    t_error "let_propagate_error_binding" 
      (fun _ -> expr_of_sexp (parse "(let ((a (add1(sub1)))) a)"))
      (SyntaxError ("Invalid syntax at line 0, col 14--line 0, col 20"));
    t_error "let_propagate_error_expr" 
      (fun _ -> expr_of_sexp (parse "(let ((a 1)) (sub1(add1)))"))
      (SyntaxError ("Invalid syntax at line 0, col 18--line 0, col 24"));
  ]
;;

let reg_to_asm_string_tests = [
  t_any "RAX_to_str" (reg_to_asm_string RAX) "RAX";
  t_any "RSP_to_str" (reg_to_asm_string RSP) "RSP";
];;


let arg_to_asm_string_tests = [
  t_any "const_to_str" (arg_to_asm_string (Const 1L)) "1";
  t_any "const_to_str_neg" (arg_to_asm_string (Const (-1L))) "-1";
  t_any "arg_RAX_to_str" (arg_to_asm_string (Reg RAX)) "RAX";
  t_any "arg_RSP_to_str" (arg_to_asm_string (Reg RSP)) "RSP";

  t_any "RSP_offset_to_str" (arg_to_asm_string (RegOffset (1, RSP))) "[RSP - 8*1]";
  t_any "RSP_offset_to_str" (arg_to_asm_string (RegOffset (10, RSP))) "[RSP - 8*10]";
  t_any "RSP_offset_to_str_neg" (arg_to_asm_string (RegOffset ((-1), RSP))) "[RSP - 8*-1]";
  t_error "RAX_offset" (fun _ -> (arg_to_asm_string (RegOffset (1, RAX))))
    (Failure "Internal compiler error: Offset of non-RAX register: RAX");
];;


let suite : OUnit2.test =
  "suite"
  >::: (*[te "forty_one" "41" "not yet implemented"; te "nyi" "(let ((x 10)) x)" "not yet implemented"]*)
       expr_of_sexp_tests
       @ reg_to_asm_string_tests
       @ arg_to_asm_string_tests
;;

let () = run_test_tt_main suite
