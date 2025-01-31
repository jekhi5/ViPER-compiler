open Compile
open Runner
open OUnit2
open Pretty
open Exprs
open Printf

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

(* Printer for tag expr *)
let rec string_of_tag_expr (e : tag expr) : string =
  match e with
  | ENumber (n, t) -> sprintf "%s : %d" (Int64.to_string n) t
  | EId (x, t) -> sprintf "%s : %d" x t
  | EPrim1 (op, e, t) -> sprintf "%s(%s) : %d" (string_of_op1 op) (string_of_tag_expr e) t
  | EPrim2 (op, left, right, t) ->
      sprintf "(%s %s %s)  : %d" (string_of_tag_expr left) (string_of_op2 op)
        (string_of_tag_expr right) t
  | ELet (binds, body, t) ->
      let binds_strs =
        List.map (fun (x, e, ta) -> (sprintf "(%s = %s) : %d" x (string_of_tag_expr e)) ta) binds
      in
      let binds_str = List.fold_left ( ^ ) "" (intersperse binds_strs ", ") in
      sprintf "(let %s in %s) : %d" binds_str (string_of_tag_expr body) t
  | EIf (cond, thn, els, t) ->
      sprintf "(if %s: %s else: %s) : %d" (string_of_tag_expr cond) (string_of_tag_expr thn)
        (string_of_tag_expr els) t
;;

(* Checks if two exprs are equal *)
let texp (name : string) (actual : 'a expr) (expected : 'b expr) =
  name >:: fun _ -> assert_equal expected actual ~printer:string_of_tag_expr
;;

(* Printer for tag expr *)
let rec string_of_tag_expr (e : tag expr) : string =
  match e with
  | ENumber (n, t) -> sprintf "%s : %d" (Int64.to_string n) t
  | EId (x, t) -> sprintf "%s : %d" x t
  | EPrim1 (op, e, t) -> sprintf "%s(%s) : %d" (string_of_op1 op) (string_of_tag_expr e) t
  | EPrim2 (op, left, right, t) ->
      sprintf "(%s %s %s)  : %d" (string_of_tag_expr left) (string_of_op2 op)
        (string_of_tag_expr right) t
  | ELet (binds, body, t) ->
      let binds_strs =
        List.map (fun (x, e, ta) -> (sprintf "(%s = %s) : %d" x (string_of_tag_expr e)) ta) binds
      in
      let binds_str = List.fold_left ( ^ ) "" (intersperse binds_strs ", ") in
      sprintf "(let %s in %s) : %d" binds_str (string_of_tag_expr body) t
  | EIf (cond, thn, els, t) ->
      sprintf "(if %s: %s else: %s) : %d" (string_of_tag_expr cond) (string_of_tag_expr thn)
        (string_of_tag_expr els) t
;;


(* Runs a program, given as the name of a file in the input/ directory, and compares its output to expected *)
let tprog (filename : string) (expected : string) = filename >:: test_run_input filename expected

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to expected *)
let teprog (filename : string) (expected : string) = filename >:: test_err_input filename expected

(* A helper for testing raised errors *)
let t_error name expr (expected : exn) = name >:: fun _ -> assert_raises expected expr

(* Tests for a boolean condition *)
let tb name expr = name >:: fun _ -> assert_bool "nested_arith" expr

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
    t "multi_bindings_together" "(let x = 1, y = x, z = x, a = z in x + y + a + z)" "4";
    t "dupled_nested_lests" "(let x = (let y = 1 in y), z = (let y = 2 in y) in x + z)" "3" ]
;;

(* Helper values to make testing nicer. *)
let dummy = ENumber (0L, ())

let tagged t = ENumber (0L, t)

let tag_tests =
  [ (* Simple cases *)
    texp "tag_constant" (tag (ENumber (1L, ()))) (ENumber (1L, 1));
    texp "tag_id" (tag (EId ("x", ()))) (EId ("x", 1));
    texp "tag_prim1" (tag (EPrim1 (Add1, dummy, ()))) (tag (EPrim1 (Add1, tagged 2, 1)));
    texp "tag_prim2"
      (tag (EPrim2 (Plus, dummy, dummy, ())))
      (tag (EPrim2 (Plus, tagged 2, tagged 3, 1)));
    texp "tag_if"
      (tag (EIf (dummy, dummy, dummy, ())))
      (tag (EIf (tagged 1, tagged 2, tagged 3, 1)));
    texp "tag_let_one_binding"
      (tag (ELet ([("x", dummy, ())], dummy, ())))
      (ELet ([("x", tagged 2, 3)], tagged 4, 1));
    texp "tag_let_multi_bindings"
      (tag (ELet ([("x", dummy, ()); ("y", dummy, ()); ("z", dummy, ())], dummy, ())))
      (ELet ([("x", tagged 2, 3); ("y", tagged 4, 5); ("z", tagged 6, 7)], tagged 8, 1))
    (* Nested cases *) ]
;;

let rename_tests =
  [ texp "rename_num" (rename (tag dummy)) (tagged 1);
    texp "rename_let_one"
      (rename (tag (ELet ([("x", dummy, ())], dummy, ()))))
      (ELet ([("x#3", tagged 2, 3)], tagged 4, 1));
    texp "rename_let_multi"
      (rename
         (tag (ELet ([("x", dummy, ()); ("y", dummy, ()); ("z", dummy, ())], EId ("x", ()), ()))) )
      (ELet ([("x#3", tagged 2, 3); ("y#5", tagged 4, 5); ("z#7", tagged 6, 7)], EId ("x#3", 8), 1))
  ]
;;

let anf_full e = anf (rename (tag e))

let let_tester = ELet ([("x", dummy, ()); ("y", dummy, ()); ("z", dummy, ())], EId ("x", ()), ())

let anf_tests =
  [ tanf "constant" (ENumber (1L, ())) (ENumber (1L, ()));
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
      (ELet ([("x", ENumber (10L, ()), ()); ("let#1", EId ("x", ()), ())], EId ("let#1", ()), ()));
    tanf "plus_basic"
      (EPrim2 (Plus, ENumber (5L, ()), ENumber (4L, ()), ()))
      (ELet
         ([("+#1", EPrim2 (Plus, ENumber (5L, ()), ENumber (4L, ()), ()), ())], EId ("+#1", ()), ())
      );
    tb "let_from_lecture"
      (is_anf
         (anf
            (rename
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
                       () ) ) ) ) ) );
    tb "round_trip"
      (is_anf
         (anf_full
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
                 () ) ) ) );
    tb "nested_prim2"
      (is_anf
         (anf_full
            (EPrim2
               (Plus, EPrim2 (Plus, ENumber (1L, ()), ENumber (2L, ()), ()), ENumber (3L, ()), ())
            ) ) );
    tb "nested_prim2_2"
      (is_anf
         (anf_full
            (EPrim2
               ( Plus,
                 EPrim2 (Plus, ENumber (1L, ()), ENumber (2L, ()), ()),
                 EPrim2 (Plus, ENumber (3L, ()), ENumber (4L, ()), ()),
                 () ) ) ) );
    tanf "let_multi_bindings" let_tester
      (ELet
         ( [("x", dummy, ()); ("y", dummy, ()); ("z", dummy, ()); ("let#1", EId ("x", ()), ())],
           EId ("let#1", ()),
           () ) );
    tb "let_multi_bindings2" (is_anf (anf_full let_tester));
    tb "arbitraily_nested_lets"
      (is_anf
         (anf_full
            (ELet
               ( [("x", let_tester, ()); ("y", let_tester, ()); ("z", let_tester, ())],
                 EId ("x", ()),
                 () ) ) ) ) ]
;;

let compile_tests =
  [ t "test1"
      "(let x = (if sub1(1): 5 + 5 else: 6 * 2) in\n\
      \  (let y = (if add1(4): x * 3 else: x + 5) in\n\
      \    (x + y)))" "48";
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
    t "add1_let" "add1((let x = 1 in x))" "2";
    t "sub1_let" "sub1((let x = 1 in x))" "0";
    t "plus_let" "((let x = 1 in x) + (let x = 4 in x))" "5";
    t "minus_let" "((let x = 1 in x) - (let x = 4 in x))" "-3";
    t "times_let" "((let x = 2 in x) * (let x = 4 in x))" "8";
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
    t "complex_if" "(if 5 + (4 - 2) * (4 - 2): add1(6 - 3) else: sub1(5 * 5))" "4";
    t "multi_let_prims2" "let x = (4 + 6) - (2 + 1), y = (x - 5) * (6 + 3), z = x + y in z + x + y"
      "50";
    t "order_of_ops" "1 + 2 * 3" "9";
    t "order_of_ops2" "1 * 2 + 3" "5";
    (* Test that if only evaluates one side by threatening to throw an error due to overflow. *)
    (* Wait, actually this doesn't work. It just overflows, instead of throwing and error. *)
    t "if_not_evaluate_both" (sprintf "if 1: 1 else: (%d * %d)" Int.max_int Int.max_int) "1";
      
    (* Some more nested let tests to show how the scope works *)
    t "shadow1" "let x = 1 in let x = 5 in x + x" "10";
    t "shadow2" "(let x = 1 in x) + (let x = 5 in x)" "6";
    t "shadow3" "(let x = 1, y = x * 2 in x + y) + (let y = 6, x = y in x - 1 - y)" "2";
    t "shadow4" "let a=((5 - 4) * (11 - 10)),b=a,c=a,d=5 in let a = (5 * 4) in (b + c + a + d)" "27";
  ]
;;

let suite = "suite" >::: check_scope_tests @ tag_tests @ rename_tests @ anf_tests @ compile_tests

let () = run_test_tt_main suite
