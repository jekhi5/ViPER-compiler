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

let forty_one = "41"

let forty_one_a = ENumber (41L, ())

let check_scope_tests = [ (* TODO... *) ]

let tag_tests = [ (* TODO... *) ]

let rename_tests = [ (* TODO... *) ]

let anf_tests =
  [ (* TODO: Call is_anf on all of these tests to ensure the function is meaningful *)
    tanf "constant" (ENumber (1L, ())) (ENumber (1L, ()));
    tanf "add1"
      (EPrim1 (Add1, ENumber (1L, ()), ()))
      (ELet ([("add1#1", EPrim1 (Add1, ENumber (1L, ()), ()), ())], EId ("add1#1", ()), ()));
    tanf "sub1"
      (EPrim1 (Sub1, ENumber (1L, ()), ()))
      (ELet ([("sub1#1", EPrim1 (Sub1, ENumber (1L, ()), ()), ())], EId ("sub1#1", ()), ()));
    tanf "if_basic"
      (EIf (ENumber (0L, ()), ENumber (5L, ()), ENumber (10L, ()), ()))
      (ELet
         ( [("if#1", EIf (ENumber (0L, ()), ENumber (5L, ()), ENumber (10L, ()), ()), ())],
           EId ("if#1", ()),
           () ) );
    tanf "let_basic"
      (ELet ([("x", ENumber (10L, ()), ())], EId ("x", ()), ()))
      (ELet ([("x", ENumber (10L, ()), ())], EId ("x", ()), ()));
    tanf "plus_basic"
      (EPrim2 (Plus, ENumber (5L, ()), ENumber (4L, ()), ()))
      (ELet
         ([("+#1", EPrim2 (Plus, ENumber (5L, ()), ENumber (4L, ()), ()), ())], EId ("+#1", ()), ())
      );

      (* TODO: Fill in this test *)
    tanf "let_from_lecture"
      (ELet
         ( [ ( "x",
               EIf
                 ( ENumber (0L, ()),
                   EPrim2 (Plus, ENumber (5L, ()), ENumber (5L, ()), ()),
                   EPrim2 (Times, ENumber (6L, ()), ENumber (2L, ()), ()),
                   () ),
               () ) ],
           BODY,
           () ) )
      () ]
;;

let suite =
  "suite"
  >:::
  (* [ 
    tanf "forty_one_anf" (ENumber (41L, ())) forty_one_a;
         (* For CS4410 students, with unnecessary let-bindings *)
         tanf "prim1_anf_4410"
           (EPrim1 (Sub1, ENumber (55L, ()), ()))
           (ELet ([("unary_1", EPrim1 (Sub1, ENumber (55L, ()), ()), ())], EId ("unary_1", ()), ()));
         (* For CS6410 students, with optimized let-bindings *)
         tanf "prim1_anf_6410"
           (EPrim1 (Sub1, ENumber (55L, ()), ()))
           (EPrim1 (Sub1, ENumber (55L, ()), ()));
         ta "tag_forty_one_run_anf" (tag forty_one_a) "41";
         t "int_literal_forty_one" forty_one "41";
         tprog "test1.boa" "3";
         (* Some useful if tests to start you off *)
         t "if_truthy_int" "if 5: 4 else: 2" "4";
         t "if_falsy_int" "if 0: 4 else: 2" "2"  *)
  check_scope_tests @ tag_tests @ rename_tests @ anf_tests
;;

let () = run_test_tt_main suite
