open Compile
open Runner
open OUnit2
open Pretty
open Exprs

let t name program expected = name >:: test_run program name expected

let ta name program_and_env expected = name >:: test_run_anf program_and_env name expected

let te name program expected_err = name >:: test_err program name expected_err

let tvg name program expected = name >:: test_run_valgrind program name expected

let tanf name program expected =
  name >:: fun _ -> assert_equal expected (anf (tag program)) ~printer:string_of_aprogram
;;

let teq name actual expected = name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)

let tests = []

let rename_tests = [
  
]

let suite = "suite" >::: tests @ rename_tests

let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
