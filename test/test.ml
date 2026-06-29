open Compile
open Runner
open OUnit2
open Pretty
open Exprs
open Phases
open Graph
open Assembly
open Util
open Constants
open Env
open Well_formed
open Desugar
open Rename
open Anf
open Free_vars
open Naive_alloc
open Liveness
open Register_alloc
open Codegen
open Test_funcs

let pair_tests =
  [ t "tup1"
      "let t = (4, (5, 6)) in\n\
      \            begin\n\
      \              t[0] := 7;\n\
      \              t\n\
      \            end"
      "" "(7, (5, 6))";
    t "tup2"
      "let t = (4, (5, nil)) in\n\
      \            begin\n\
      \              t[1] := nil;\n\
      \              t\n\
      \            end"
      "" "(4, nil)";
    t "tup3"
      "let t = (4, (5, nil)) in\n\
      \            begin\n\
      \              t[1] := t;\n\
      \              t\n\
      \            end"
      "" "(4, <cyclic tuple 1>)";
    t "tup4" "let t = (4, 6) in\n            (t, t)" "" "((4, 6), (4, 6))" ]
;;

let input = [t "input1" "let x = input() in x + 2" "123" "125"]

(** Collects a number of tests into one list, just by specifying the modules.*)
let gather_tests (modules : (module TestSuite) list) =
  List.concat_map (fun (module M : TestSuite) -> M.suite) modules
;;

let suite =
  "unit_tests"
  >::: gather_tests
         [
          (* (module Test_racer.Suite); *)
          (* (module Test_garter.Suite); *)
          (module Test_parser.Suite)
        ]
;;

(* @ fvc @ nsa @ ra @ coloring @ interf @ pair_tests @ run_with_ra @ live_out @ oom
       @ gc @ input *)

let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
