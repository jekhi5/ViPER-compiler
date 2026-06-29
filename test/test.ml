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
          (module Test_parser.Suite);
          (module Test_builtins.Suite)
        ]
;;

(* @ fvc @ nsa @ ra @ coloring @ interf @ pair_tests @ run_with_ra @ live_out @ oom
       @ gc @ input *)

let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
