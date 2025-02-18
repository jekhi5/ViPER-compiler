open Compile
open Runner
open OUnit2
open Pretty
open Exprs
open ExtLib

let t name program expected = name >:: test_run program name expected

let ta name program_and_env expected = name >:: test_run_anf program_and_env name expected

let te name program expected_err = name >:: test_err program name expected_err

let tvg name program expected = name >:: test_run_valgrind program name expected

let tanf name program expected =
  name >:: fun _ -> assert_equal expected (anf (tag program)) ~printer:string_of_aprogram
;;

let teq name actual expected = name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)

(* A helper for testing primitive values (won't print datatypes well) *)
let t_any name value expected = name >:: fun _ -> assert_equal expected value ~printer:dump


let tests = []

let anf_tests = [
  tanf "prim2_anf" 
    (Program ([], EPrim2 (Times, (ENumber (8L, 0)), (ENumber (3L, 0)), 0), 0)) 
    (AProgram (
      [],
      ACExpr (CPrim2 (Times, ImmNum (8L, ()), ImmNum (3L, ()), ())),
      ()
    ));
]

let misc_tests = [
  t_any "split1" (split_at [1;2;3;4;5] 3) ([1;2;3], [4;5]);
  t_any "split2" (split_at [1;2;3;4;5] 0) ([], [1;2;3;4;5]);
  t_any "split3" (split_at [1;2;3;4;5] 7) ([1;2;3;4;5], []);
  t_any "split3" (split_at [1;] 6) ([1;], []);
  t_any "rd1" (remove_dups [(1,2); (1,2); (1,3); (4, 1); (2, 4)]) [(1,3); (4, 1); (2, 4)];
]

let suite = "suite" >::: tests @ misc_tests @ anf_tests

let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
