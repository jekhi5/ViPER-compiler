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

let builtins_size =
  4 (* arity + 0 vars + codeptr + padding *)
  * 1 (* TODO FIXME (List.length Compile.native_fun_bindings) *)
;;

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

let oom =
  [ tgcerr "oomgc1" (7 + builtins_size) "(1, (3, 4))" "" "Out of memory";
    tgc "oomgc2" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
    tvgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
    tgc "oomgc4" (4 + builtins_size) "(3, 4)" "" "(3, 4)";
    tgcerr "oomgc5" (3 + builtins_size) "(1, 2, 3, 4, 5, 6, 7, 8, 9, 0)" "" "Allocation" ]
;;

let gc =
  [ tgc "gc_lam1" (10 + builtins_size)
      "let f = (lambda: (1, 2)) in\n\
      \       begin\n\
      \         f();\n\
      \         f();\n\
      \         f();\n\
      \         f()\n\
      \       end"
      "" "(1, 2)" ]
;;

let fvc =
  [ tfvsc "nested_lambda"
      "let \n\
      \    foo = (lambda(w, x, y, z):\n\
      \             (lambda(a): a + x + z))\n\
      \ in\n\
      \    foo(1, 2, 3, 4)(5)"
      (AProgram
         ( ALet
             ( "lam_5",
               CLambda
                 ( ["w"; "x"; "y"; "z"],
                   ALet
                     ( "lam_6",
                       CLambda
                         ( ["a"],
                           ALet
                             ( "binop_8",
                               CPrim2
                                 ( Plus,
                                   ImmId ("a", set ["a"]),
                                   ImmId ("x", set ["x"]),
                                   set ["x"; "a"] ),
                               ACExpr
                                 (CPrim2
                                    ( Plus,
                                      ImmId ("binop_8", set ["binop_8"]),
                                      ImmId ("z", set ["z"]),
                                      set ["z"; "binop_8"] ) ),
                               set ["a"; "x"; "z"] ),
                           set ["x"; "z"] ),
                       ACExpr (CImmExpr (ImmId ("lam_6", set ["lam_6"]))),
                       set ["x"; "z"] ),
                   empty ),
               ALet
                 ( "foo",
                   CImmExpr (ImmId ("lam_5", set ["lam_5"])),
                   ALet
                     ( "app_19",
                       CApp
                         ( ImmId ("?foo", set ["foo"]),
                           [ ImmNum (4L, empty);
                             ImmNum (3L, empty);
                             ImmNum (2L, empty);
                             ImmNum (1L, empty) ],
                           Snake,
                           set ["foo"] ),
                       ACExpr
                         (CApp
                            ( ImmId ("?app_19", set ["app_19"]),
                              [ImmNum (5L, empty)],
                              Snake,
                              set ["app_19"] ) ),
                       set ["foo"] ),
                   set ["lam_5"] ),
               empty ),
           empty ) );
    tfvsc "full_prog1" "let foo = true in foo"
      (AProgram
         ( ALet
             ( "foo",
               CImmExpr (ImmBool (true, empty)),
               ACExpr (CImmExpr (ImmId ("foo", set ["foo"]))),
               empty ),
           empty ) );
    tfvsc "full_prog2" "let foo = 1 in foo + bar"
      (AProgram
         ( ALet
             ( "foo",
               CImmExpr (ImmNum (1L, empty)),
               ACExpr
                 (CPrim2
                    ( Plus,
                      ImmId ("foo", set ["foo"]),
                      ImmId ("bar", set ["bar"]),
                      set ["foo"; "bar"] ) ),
               set ["bar"] ),
           set ["bar"] ) ) ]
;;

let input = [t "input1" "let x = input() in x + 2" "123" "125"]

let run_with_ra =
  [ tr "adder1" "add1(5)" "" "6";
    tr "adder2" "add1(add1(add1(add1(5))))" "" "9";
    tr "boa1" "1 + 2 + 3 + 4 + 5" "" "15";
    tr "boa2" "(((1 + 2) + 3) + (4 + 5))" "" "15";
    tr "nested_lambdas1" "let foo = (lambda(x): (lambda(y): y + x)) in 3" "" "3";
    tr "nested_lambdas2" "let foo = (lambda(x): (lambda(y): y - x)) in foo(3)(15)" "" "12" ]
;;

(** Collects a number of tests into one list, just by specifying the modules.*)
let gather_tests (modules : (module TestSuite) list) =
  List.concat_map (fun (module M : TestSuite) -> M.suite) modules
;;

let suite = "unit_tests" >::: gather_tests [
  (module Test_racer.Suite);
  (module Test_parser.Suite)]
(* @ fvc @ nsa @ ra @ coloring @ interf @ pair_tests @ run_with_ra @ live_out @ oom
       @ gc @ input *)

let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
