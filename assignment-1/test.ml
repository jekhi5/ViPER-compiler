open Sexp
open OUnit2
open Expr
open ExtLib

(* a helper for testing integers *)
let t_int name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:string_of_int);;

(* A helper for testing primitive values (won't print datatypes well) *)
let t_any name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:dump);;

(* Feel free to add any new testing functions you may need *)




(* It can be useful to aggregate tests into lists if they test separate
functions, and put them together at the end *)

let env1 = [("a", 5); ("b", 15)];;
  
let get_tests = [
  t_any "get1" (get env1 "a") (Some(5));
  t_any "get2" (get env1 "b") (Some(15));
  t_any "get3" (get env1 "c") None;
  (* More tests here *)
];;

let contains_tests = [
  t_any "contains1" (contains env1 "c") false;
  (* More tests here *)
];;

let evaluate_tests = [
  t_int "evaluate1" (evaluate (Times(Num(0), Num(5))) []) 0;
  t_int "evaluate2" (evaluate (Times(Num(1), Num(5))) []) 5;
  (* More tests here *)
]

let all_arith_tests =
  get_tests @
  contains_tests @
  evaluate_tests
  (* More tests here *)
;;

let arith_suite = "arithmetic_evaluation">:::all_arith_tests
;;

run_test_tt_main arith_suite
;;

let all_sexp_tests = [
    (* More tests here *)
  ]
;;

let sexp_suite = "sexp_parsing">:::all_sexp_tests
;;

run_test_tt_main sexp_suite
;;

