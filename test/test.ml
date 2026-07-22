open Runner
open OUnit2
open Test_funcs

(** Collects a number of tests into one list, just by specifying the modules.*)
let gather_tests (modules : (module TestSuite) list) =
  List.concat_map (fun (module M : TestSuite) -> M.suite) modules
;;

let suite =
  "unit_tests"
  >::: gather_tests
         [ (module Test_builtins.Suite);
           (module Test_desugar.Suite);
           (module Test_errors.Suite);
           (module Test_parser.Suite);
           (module Test_util.Suite);
           (module Test_well_formed.Suite) ]
;;

let file_tests = "file_tests" >::: [input_file_test_suite ()]

let () = run_test_tt_main ("all_tests" >::: [suite; file_tests])
