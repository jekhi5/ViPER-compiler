open Compile
open Runner

(* open Printf *)
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
    (* t_error "add1-error-no-args"
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
         (SyntaxError "Invalid syntax on `let` at line 0, col 0"); *)
    t_any "let-one-binding"
      (expr_of_sexp (parse "(let ((x 5)) x)"))
      (Let ([("x", Number (5L, (0, 9, 0, 10)))], Id ("x", (0, 13, 0, 14)), (0, 0, 0, 15)));
    t_any "let-many-bindings"
      (expr_of_sexp (parse "(let ((x 5) (y (sub1 10))) (add1 x))"))
      (Let
         ( [ ("x", Number (5L, (0, 9, 0, 10)));
             ("y", Prim1 (Sub1, Number (10L, (0, 21, 0, 23)), (0, 15, 0, 24))) ],
           Prim1 (Add1, Id ("x", (0, 33, 0, 34)), (0, 27, 0, 35)),
           (0, 0, 0, 36) ) );
    t_any "let_shadowed_bindings"
      (expr_of_sexp (parse "(let ((x 5) (x (sub1 10))) (add1 x))"))
      (Let
         ( [ ("x", Number (5L, (0, 9, 0, 10)));
             ("x", Prim1 (Sub1, Number (10L, (0, 21, 0, 23)), (0, 15, 0, 24))) ],
           Prim1 (Add1, Id ("x", (0, 33, 0, 34)), (0, 27, 0, 35)),
           (0, 0, 0, 36) ) );
    t_any "nested_let"
      (expr_of_sexp (parse "(let ((a (let ((b 5)) b)))(let ((d a)) d))"))
      (Let
         ( [ ( "a",
               Let ([("b", Number (5L, (0, 18, 0, 19)))], Id ("b", (0, 22, 0, 23)), (0, 9, 0, 24))
             ) ],
           Let ([("d", Id ("a", (0, 35, 0, 36)))], Id ("d", (0, 39, 0, 40)), (0, 26, 0, 41)),
           (0, 0, 0, 42) ) );
    (* Various let syntax errors: *)
    t_error "let-binding_non_id"
      (fun _ -> expr_of_sexp (parse "(let ((5 4)) 5)"))
      (SyntaxError
         "Invalid binding syntax, can only bind to identifiers, at line 0, col 7--line 0, col 8" );
    t_error "let-error-no-bindings"
      (fun _ -> expr_of_sexp (parse "(let () 5)"))
      (SyntaxError "Invalid syntax: A `let` requires at least one binding at line 0, col 5");
    t_error "let_binding_no_inner_parens"
      (fun _ -> expr_of_sexp (parse "(let (a 1) a)"))
      (SyntaxError "Invalid binding syntax at line 0, col 6--line 0, col 7");
    t_error "let_binding_too_few_vals"
      (fun _ -> expr_of_sexp (parse "(let ((a)) a)"))
      (SyntaxError "Invalid binding syntax at line 0, col 6--line 0, col 9");
    t_error "let_binding_too_many_vals"
      (fun _ -> expr_of_sexp (parse "(let ((a 1 2)) a)"))
      (SyntaxError "Invalid binding syntax at line 0, col 6--line 0, col 13");
    t_error "let_propagate_error_binding"
      (fun _ -> expr_of_sexp (parse "(let ((a (let ((a 2 3)) a))) a)"))
      (SyntaxError "Invalid binding syntax at line 0, col 15--line 0, col 22");
    t_error "let_propagate_error_expr"
      (fun _ -> expr_of_sexp (parse "(let ((a 1)) (let ((a 1 2)) a) )"))
      (SyntaxError "Invalid binding syntax at line 0, col 19--line 0, col 26");
    t_any "let-bool-binding"
      (expr_of_sexp (parse "(let ((true 5)) true)"))
      (Let ([("true", Number (5L, (0, 12, 0, 13)))], Id ("true", (0, 16, 0, 20)), (0, 0, 0, 21)));
    t_any "let-add1-binding"
      (expr_of_sexp (parse "(let ((add1 5)) add1)"))
      (Let ([("add1", Number (5L, (0, 12, 0, 13)))], Id ("add1", (0, 16, 0, 20)), (0, 0, 0, 21)));
    t_any "let-let-binding"
      (expr_of_sexp (parse "(let ((let 5)) let)"))
      (Let ([("let", Number (5L, (0, 11, 0, 12)))], Id ("let", (0, 15, 0, 18)), (0, 0, 0, 19)));
    t_any "invalid_identifier" (parse "4a_b") (Sym ("4a_b", (0, 0, 0, 4)));
    t_any "add1"
      (expr_of_sexp (parse "(add1 5)"))
      (Prim1 (Add1, Number (5L, (0, 6, 0, 7)), (0, 0, 0, 8)));
    t_any "sub1"
      (expr_of_sexp (parse "(sub1 5)"))
      (Prim1 (Sub1, Number (5L, (0, 6, 0, 7)), (0, 0, 0, 8))) ]
;;

let reg_to_asm_string_tests =
  [ t_any "RAX_to_str" (reg_to_asm_string RAX) "RAX";
    t_any "RSP_to_str" (reg_to_asm_string RSP) "RSP" ]
;;

let arg_to_asm_string_tests =
  [ t_any "const_to_str" (arg_to_asm_string (Const 1L)) "1";
    t_any "const_to_str_neg" (arg_to_asm_string (Const (-1L))) "-1";
    t_any "arg_RAX_to_str" (arg_to_asm_string (Reg RAX)) "RAX";
    t_any "arg_RSP_to_str" (arg_to_asm_string (Reg RSP)) "RSP";
    t_any "RSP_offset_to_str" (arg_to_asm_string (RegOffset (1, RSP))) "[RSP - 8*1]";
    t_any "RSP_offset_to_str" (arg_to_asm_string (RegOffset (10, RSP))) "[RSP - 8*10]";
    t_any "RSP_offset_to_str_neg" (arg_to_asm_string (RegOffset (-1, RSP))) "[RSP - 8*-1]";
    t_error "RAX_offset"
      (fun _ -> arg_to_asm_string (RegOffset (1, RAX)))
      (Failure "ICE: Offset of non-RSP register: RAX") ]
;;

let instruction_to_asm_string_tests = [
  t_any "move_const_to_reg" (instruction_to_asm_string (IMov (Reg RAX, Const 1L))) "\tmov RAX, 1";
  t_any "move_const_to_rsp" (instruction_to_asm_string (IMov (Reg RSP, Const 1L))) "\tmov RSP, 1";

  (* Questionably legal cases *)
  t_any "move_reg_to_const" (instruction_to_asm_string (IMov (Const 1L, Reg RAX))) "\tmov 1, RAX";
  t_any "move_reg_to_reg" (instruction_to_asm_string (IMov (Reg RAX, Reg RSP))) "\tmov RAX, RSP";
  t_any "move_const_to_const" (instruction_to_asm_string (IMov (Const 1L, Const 2L))) "\tmov 1, 2";
  t_any "move_reg_reg_offset" (instruction_to_asm_string (IMov (Reg RAX, RegOffset (1, RSP)))) "\tmov RAX, [RSP - 8*1]";
  t_any "move_reg_offset, Reg" (instruction_to_asm_string (IMov (RegOffset (1, RSP), Reg RAX))) "\tmov [RSP - 8*1], RAX";
  t_any "move_const_reg_offset" (instruction_to_asm_string (IMov (Const 1L, RegOffset (1, RSP)))) "\tmov 1, [RSP - 8*1]";
  t_any "move_reg_offset_const" (instruction_to_asm_string (IMov (RegOffset (1, RSP), Const 1L))) "\tmov [RSP - 8*1], 1";
  
  t_any "add_const_to_reg" (instruction_to_asm_string (IMov (Reg RAX, Const 1L))) "\tmov RAX, 1";
  t_any "add_const_to_rsp" (instruction_to_asm_string (IMov (Reg RSP, Const 1L))) "\tmov RSP, 1";

  (* Questionably legal cases *)
  t_any "add_reg_to_const" (instruction_to_asm_string (IAdd (Const 1L, Reg RAX))) "\tadd 1, RAX";
  t_any "add_reg_to_reg" (instruction_to_asm_string (IAdd (Reg RAX, Reg RSP))) "\tadd RAX, RSP";
  t_any "add_const_to_const" (instruction_to_asm_string (IAdd (Const 1L, Const 2L))) "\tadd 1, 2";
  t_any "add_reg_reg_offset" (instruction_to_asm_string (IAdd (Reg RAX, RegOffset (1, RSP)))) "\tadd RAX, [RSP - 8*1]";
  t_any "add_reg_offset, Reg" (instruction_to_asm_string (IAdd (RegOffset (1, RSP), Reg RAX))) "\tadd [RSP - 8*1], RAX";
  t_any "add_const_reg_offset" (instruction_to_asm_string (IAdd (Const 1L, RegOffset (1, RSP)))) "\tadd 1, [RSP - 8*1]";
  t_any "add_reg_offset_const" (instruction_to_asm_string (IAdd (RegOffset (1, RSP), Const 1L))) "\tadd [RSP - 8*1], 1";
  
  t_any "ret" (instruction_to_asm_string IRet) "\tret";
];;

let integration_tests =
  [ t "one" "1" "1";
    t "add1" "(add1 0)" "1";
    t "sub1" "(sub1 0)" "-1";
    te "unbound_id1" "helloxDxD" "Unbound identifier";
    (* Simple `let` tests *)
    t "let1" "(let ((a 1)) a)" "1";
    t "let2" "(let ((a 1) (b 2)) b)" "2";
    t "let3" "(let ((a 1) (b (add1 a))) b)" "2";
    t "no_reserved_words1" "(let ((add1 1)) (add1 add1))" "2";
    t "no_reserved_words2" "(let ((true 1)) (add1 true))" "2";
    t "no_reserved_words3" "(let ((let 1)) (add1 (let ((a 1)) a)))" "2";
    (* Nested `let` tests *)
    t "let_nested_body1" "(let ((a 1) (b 5)) (let ((c (add1 b))) c))" "6";
    t "let_nested_binding1" "(let ((a 1) (b (let ((c (add1 a))) c))) (add1 b))" "3";
    t "simple_shadow" "(let ((a 1)) (let ((a 2)) a))" "2";
    (* `let` error tests *)
    te "duplicate_bindings_1" "(let ((a 1) (a 2)) a)" "Duplicate binding";

    (* Internal Compiler Errors - Notice that we can't run a program normally here. *)
    t_error "no_bindings_🤔" (fun _ -> compile (Let ([], Number (1L, (0,0,0,0)), (0,0,0,0)))) (BindingError "ICE: `let` has no bindings at compile time, atline 0, col 0--line 0, col 0") ;
]
;;

let suite : OUnit2.test =
  "suite"
  >:::
  (*[te "forty_one" "41" "not yet implemented"; te "nyi" "(let ((x 10)) x)" "not yet implemented"]*)
  expr_of_sexp_tests @ reg_to_asm_string_tests @ arg_to_asm_string_tests
  @ instruction_to_asm_string_tests (* TODO *) @ integration_tests
;;

let () = run_test_tt_main suite
