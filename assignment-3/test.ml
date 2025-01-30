open Compile
open Runner
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

(* A helper for testing raised errors *)
let t_error name expr (expected : exn) = name >:: fun _ -> assert_raises expected expr

(* Tests for a boolean condition *)
let tb name expr = name >:: fun _ -> assert_bool "nested_arith" expr

let forty_one = "41"

let forty_one_a = ENumber (41L, ())

let check_scope_tests =
  [ (* We use the entire compile pipeline here for convenience,
     * but the purpose of these tests is to demonstrate that we catch all scope errors.
     * (And don't catch false positives). 
     *)

    (* Free identifier Errors *)
    te "free_id" "x" "Binding Error: unbound identifier";
    te "free_id_nested" "(add1(x) + 5)" "Binding Error: unbound identifier";
    te "free_id_in_let_body" "(let x = 1 in y)" "Binding Error: unbound identifier `y`";
    te "free_id_in_binding" "(let x = y in x)" "Binding Error: unbound identifier `y`";
    te "free_id_in_binding2" "(let x = x in 1)" "Binding Error: unbound identifier `x`";
    te "free_id_in_nested_binding" "(let x = (let y = x in y) in 1)"
      "Binding Error: unbound identifier `x`";
    te "free_id_in_multi_bindings1" "(let x = 1, y = z, z = 2 in z + y + x)"
      "Binding Error: unbound identifier `z`";
    te "free_id_in_multi_bindings2" "(let x = (let a = 1 in a), y = a in y + x)"
      "Binding Error: unbound identifier `a`";
    (* Duplicate binding errors *)
    te "free_id_in_binding1" "(let x = 1, x = 2 in x)" "Binding Error: duplicate `let` binding";
    te "free_id_in_binding2" "(let x = 1, y = 2, x = 3 in y)"
      "Binding Error: duplicate `let` binding";
    (* OK cases 
     * Realistically these tests should be "assert not error",
     * since this function doesn't care that the outputs are correct.
     *)
    t "simple_let" "(let x = 1 in x)" "1";
    t "3nested_let" "(let x = 1 in let y = 2 in let z = 3 in x + y + z)" "6";
    t "shadowing_OK" "(let x = 1 in let x = 2 in x)" "2";
    t "multi_bindings_together" "(let x = 1, y = x, z = x, a = z in x + y + a + z)" "4" ]
;;

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
    tanf "let_from_lecture"
      (ELet
         ( [ ( "x",
               EIf
                 ( ENumber (0L, ()),
                   EPrim2 (Plus, ENumber (5L, ()), ENumber (5L, ()), ()),
                   EPrim2 (Times, ENumber (6L, ()), ENumber (2L, ()), ()),
                   () ),
               () ) ],
           ELet
             ( [ ( "y",
                   EIf
                     ( ENumber (1L, ()),
                       EPrim2 (Times, EId ("x", ()), ENumber (3L, ()), ()),
                       EPrim2 (Plus, EId ("x", ()), ENumber (5L, ()), ()),
                       () ),
                   () ) ],
               EId ("y", ()),
               () ),
           () ) )
      (ELet
         ( [ ( "x",
               ELet
                 ( [ ( "if#2",
                       EIf
                         ( ENumber (0L, ()),
                           ELet
                             ( [("+#4", EPrim2 (Plus, ENumber (5L, ()), ENumber (5L, ()), ()), ())],
                               EId ("+#4", ()),
                               () ),
                           ELet
                             ( [("*#7", EPrim2 (Times, ENumber (6L, ()), ENumber (2L, ()), ()), ())],
                               EId ("*#7", ()),
                               () ),
                           () ),
                       () ) ],
                   EId ("if#2", ()),
                   () ),
               () ) ],
           ELet
             ( [ ( "y",
                   ELet
                     ( [ ( "if#12",
                           EIf
                             ( ENumber (1L, ()),
                               ELet
                                 ( [ ( "*#14",
                                       EPrim2 (Times, EId ("x", ()), ENumber (3L, ()), ()),
                                       () ) ],
                                   EId ("*#14", ()),
                                   () ),
                               ELet
                                 ( [("+#17", EPrim2 (Plus, EId ("x", ()), ENumber (5L, ()), ()), ())],
                                   EId ("+#17", ()),
                                   () ),
                               () ),
                           () ) ],
                       EId ("if#12", ()),
                       () ),
                   () ) ],
               EId ("y", ()),
               () ),
           () ) );
    tb "round_trip"
      (is_anf
         (anf
            (tag
               (ELet
                  ( [ ( "x",
                        EIf
                          ( ENumber (0L, ()),
                            EPrim2 (Plus, ENumber (5L, ()), ENumber (5L, ()), ()),
                            EPrim2 (Times, ENumber (6L, ()), ENumber (2L, ()), ()),
                            () ),
                        () ) ],
                    ELet
                      ( [ ( "y",
                            EIf
                              ( ENumber (1L, ()),
                                EPrim2 (Times, EId ("x", ()), ENumber (3L, ()), ()),
                                EPrim2 (Plus, EId ("x", ()), ENumber (5L, ()), ()),
                                () ),
                            () ) ],
                        EId ("y", ()),
                        () ),
                    () ) ) ) ) );
    tb "nested_prim2"
      (is_anf
         (anf
            (tag
               (EPrim2
                  (Plus, EPrim2 (Plus, ENumber (1L, ()), ENumber (2L, ()), ()), ENumber (3L, ()), ())
               ) ) ) );
    tb "nested_prim2_2"
      (is_anf
         (anf
            (tag
               (EPrim2
                  ( Plus,
                    EPrim2 (Plus, ENumber (1L, ()), ENumber (2L, ()), ()),
                    EPrim2 (Plus, ENumber (3L, ()), ENumber (4L, ()), ()),
                    () ) ) ) ) ) ]
;;

let compile_tests =
  [ t "test1"
      "(let x = (if sub1(1): 5 + 5 else: 6 * 2) in\n\
      \  (let y = (if add1(4): x * 3 else: x + 5) in\n\
      \    (x + y)))"
      "48";
    t "constant" "1" "1";
    t "add1" "add1(0)" "1";
    t "sub1" "sub1(0)" "-1";
    t "plus1" "(1 + 2)" "3";
    t "plus2" "(2 + 1)" "3";
    t "minus1" "(2 - 1)" "1";
    t "minus2" "(1 - 2)" "-1";
    t "times1" "(8 * 3)" "24";
    t "times2" "(3 * 8)" "24";
    t "let_imm" "(let x = 1 in x)" "1";
    t "nested_binops1" "1 + 2 + 3" "6";
    t "nested_binops2" "(1 + 2) + 3" "6";
    t "nested_prim1" "add1(sub1(add1(sub1(add1(5)))))" "6";
    t "commutative_binops" "(1 - (3 + 7) * 12)" "-108";
    t "let_add1_body" "(let a = 2 in add1(a))" "3";
    t "let_sub1_body" "(let a = 2 in sub1(a))" "1";
    t "let_plus_body" "(let a = 2 in a + a)" "4";
    t "let_minus_body" "(let a = 2 in a - a)" "0";
    t "let_times_body" "(let a = 2 in a * a * a)" "8";
    t "let_add1_bound" "(let a = add1(4) in a)" "5";
    t "let_plus_bound" "(let a = 4 + 2 in a)" "6";
    t "let_times_bound" "(let a = 8 * 3 in a)" "24";
    t "let_minus_bound" "(let a = 2 - 7 in a)" "-5";
    t "let_complex_body" "(let a = 4, b = -3 in a + ((b * add1(a)) - sub1(b)) + 6)" "-1";
    (* Read the name of these tests as: "<CONDITIONAL-VALUE>_if_<INTERESTING-EXPR>_<LOCATION-OF-INTERESTING-EXPR-IN-IF>"*)
    t "true_case_if_basic" "(if 1: 1 else: 2)" "1";
    t "trues_case_if_basic_" "(if 0: 1 else: 2)" "2";
    t "true_case_if_add1_true" "(if 143: add1(7) else: 2)" "8";
    t "true_case_if_sub1_true" "(if 112: sub1(7) else: 2)" "6";
    t "true_case_if_plus_true" "(if 4: 1 + 4 else: 2)" "5";
    t "true_case_if_minus_true" "(if 4: 1 - 4 else: 2)" "-3";
    t "true_case_if_times_true" "(if 4: 8 * 2 else: 2)" "16";
    t "true_case_if_add1_false" "(if 900: 5 else: add1(7))" "5";
    t "true_case_if_sub1_false" "(if 900: 4 else: sub1(7))" "4";
    t "true_case_if_plus_false" "(if 900: 6 else: 1 + 4)" "6";
    t "true_case_if_minus_false" "(if 900: 2 else: 1 - 4)" "2";
    t "true_case_if_times_false" "(if 900: 1 else: 8 * 2)" "1";
    t "false_case_if_add1_true" "(if 0: add1(7) else: 2)" "2";
    t "false_case_if_sub1_true" "(if 0: sub1(7) else: 2)" "2";
    t "false_case_if_plus_true" "(if 0: 1 + 4 else: 2)" "2";
    t "false_case_if_minus_true" "(if 0: 1 - 4 else: 2)" "2";
    t "false_case_if_times_true" "(if 0: 8 * 2 else: 2)" "2";
    t "false_case_if_add1_false" "(if 0: 5 else: add1(7))" "8";
    t "false_case_if_sub1_false" "(if 0: 4 else: sub1(7))" "6";
    t "false_case_if_plus_false" "(if 0: 6 else: 1 + 4)" "5";
    t "false_case_if_minus_false" "(if 0: 2 else: 1 - 4)" "-3";
    t "false_case_if_times_false" "(if 0: 1 else: 8 * 2)" "16";
    t "true_case_if_add1_cond" "(if add1(0): 1 else: 4)" "1";
    t "true_case_if_sub1_cond" "(if sub1(8): 1 else: 4)" "1";
    t "true_case_if_plus_cond" "(if -4 + 7: 1 else: 4)" "1";
    t "true_case_if_minus_cond" "(if -4 - 7: 1 else: 4)" "1";
    t "true_case_if_times_cond" "(if 6 * 3: 1 else: 4)" "1";
    t "false_case_if_add1_cond" "(if add1(-1): 1 else: 4)" "4";
    t "false_case_if_sub1_cond" "(if sub1(1): 1 else: 4)" "4";
    t "false_case_if_plus_cond" "(if -4 + 4: 1 else: 4)" "4";
    t "false_case_if_minus_cond" "(if -4 - -4: 1 else: 4)" "4";
    t "false_case_if_times_cond" "(if 6 * 0: 1 else: 4)" "4";
    t "true_case_if_let_true" "(if 4: (let x = 6, y = add1(4), z = 9 in x * y + z) else: 9)" "39";
    t "false_case_if_let_true" "(if 0: (let x = 6, y = add1(4), z = 9 in x * y + z) else: 9)" "9";
    t "true_case_if_let_false" "(if 4: 9 else: (let x = 6, y = add1(4), z = 9 in x * y + z))" "9";
    t "false_case_if_let_false" "(if 0: 9 else: (let x = 6, y = add1(4), z = 9 in x * y + z))" "39";
    t "true_case_if_let_cond" "(if (let x = 6, y = add1(4), z = 9 in x * y + z): 9 else: 5)" "9";
    t "false_case_if_let_cond" "(if (let x = 6, y = add1(4), z = 9 in (x * y + z) - 39): 9 else: 5)"
      "5";
    t "complex_if" "(if 5 + (4 - 2) * (4 - 2): add1(6 - 3) else: sub1(5 * 5))" "4" ]
;;

let suite = "suite" >::: check_scope_tests @ tag_tests @ rename_tests @ anf_tests @ compile_tests

let () = run_test_tt_main suite
