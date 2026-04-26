open Compile
open Runner
open OUnit2
open Pretty
open Exprs
open Errors
open ExtLib
open Printf

let t name program input expected =
  name >:: test_run ~args:[] ~std_input:input program name expected
;;

let ta name program input expected =
  name >:: test_run_anf ~args:[] ~std_input:input program name expected
;;

let tgc name heap_size program input expected =
  name >:: test_run ~args:[string_of_int heap_size] ~std_input:input program name expected
;;

let tvg name program input expected =
  name >:: test_run_valgrind ~args:[] ~std_input:input program name expected
;;

let tvgc name heap_size program input expected =
  name >:: test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input program name expected
;;

let terr name program input expected =
  name >:: test_err ~args:[] ~std_input:input program name expected
;;

let tgcerr name heap_size program input expected =
  name >:: test_err ~args:[string_of_int heap_size] ~std_input:input program name expected
;;

let tanf name program expected =
  name >:: fun _ -> assert_equal expected (anf (tag program)) ~printer:string_of_aprogram
;;

let tp name program expected =
  name >:: fun _ -> assert_equal expected program ~printer:string_of_program
;;

let teq name actual expected = name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)

let tnsa name actual (expected : Assembly.arg envt) =
  name
  >:: fun _ ->
  let prog, nsa = naive_stack_allocation actual in
  assert_equal prog actual ~printer:string_of_aprogram;
  assert_equal nsa expected ~printer:(fun lst ->
      List.fold_left ( ^ ) ""
        (List.map (fun (a, b) : string -> sprintf "(%s, %s)\n" a (Assembly.arg_to_asm b)) lst) )
;;

let pair_tests =
  [ t "tup1"
      "let t = (4, (5, 6)) in\n\
      \            begin\n\
      \              t[0] := 7;\n\
      \              t\n\
      \            end" "" "(7, (5, 6))";
    t "tup2"
      "let t = (4, (5, nil)) in\n\
      \            begin\n\
      \              t[1] := nil;\n\
      \              t\n\
      \            end" "" "(4, nil)"
    (* t "tup3"
         "let t = (4, (5, nil)) in\n\
         \            begin\n\
         \              t[1] := t;\n\
         \              t\n\
         \            end"
         "" "(4, <cyclic tuple 1>)";
       t "tup4" "let t = (4, 6) in\n            (t, t)" "" "((4, 6), (4, 6))" ] *) ]
;;

(* let oom = [
 *   tgcerr "oomgc1" (7) "(1, (3, 4))" "" "Out of memory";
 *   tgc "oomgc2" (8) "(1, (3, 4))" "" "(1, (3, 4))";
 *   tvgc "oomgc3" (8) "(1, (3, 4))" "" "(1, (3, 4))";
 *   tgc "oomgc4" (4) "(3, 4)" "" "(3, 4)";
 * ] *)

let input =
  [ t "input1" "let x = input() in x + 2" "123" "125";
    t "input_nil" "let x = input() in x" "nil" "nil";
    t "input_true" "let x = input() in x" "true" "true";
    t "input_false" "let x = input() in x" "false" "false";
    t "input_two" "input() + input()" "1\n2" "3";
    t "input_three" "(input(), (input(), input()))" "1\n2\n3" "(1, (2, 3))";
    t "input_invalid" "input()" "abc\n1" "Invalid input: must be a number, boolean, or `nil`.\n1";
    t "input_overflow" "input()" "4611686018427387905\n1" "Invalid input: integer overflow!\n1" ]
;;

let desugar_tests =
  [ tp "desugar_tuple"
      (desugar
         (Program
            ( [],
              ELet
                ( [ ( BTuple ([BName ("a", false, 0); BBlank 0; BName ("c", false, 0)], 0),
                      ETuple ([], 0),
                      0 ) ],
                  ENumber (5L, 0),
                  0 ),
              0 ) ) )
      (Program
         ( [],
           ELet
             ( [(BName ("temp_tuple_name#1", false, 0), ETuple ([], 0), 0)],
               ELet
                 ( [ ( BName ("a", false, 0),
                       EGetItem (EId ("temp_tuple_name#1", 0), ENumber (0L, 0), 0),
                       0 ) ],
                   ELet
                     ( [ ( BName ("blank#1", false, 0),
                           EGetItem (EId ("temp_tuple_name#1", 0), ENumber (1L, 0), 0),
                           0 ) ],
                       ELet
                         ( [ ( BName ("c", false, 0),
                               EGetItem (EId ("temp_tuple_name#1", 0), ENumber (2L, 0), 0),
                               0 ) ],
                           ENumber (5L, 0),
                           0 ),
                       0 ),
                   0 ),
               0 ),
           0 ) );
    tp "nested_tuple_bind"
      (desugar
         (Program
            ( [],
              ELet
                ( [ ( BTuple
                        ( [ BName ("a", false, 0);
                            BTuple ([BName ("b", false, 0); BName ("c", false, 0)], 0);
                            BName ("d", false, 0) ],
                          0 ),
                      ETuple ([], 0),
                      0 ) ],
                  ENumber (5L, 0),
                  0 ),
              0 ) ) )
      (Program
         ( [],
           ELet
             ( [(BName ("temp_tuple_name#1", false, 0), ETuple ([], 0), 0)],
               ELet
                 ( [ ( BName ("a", false, 0),
                       EGetItem (EId ("temp_tuple_name#1", 0), ENumber (0L, 0), 0),
                       0 ) ],
                   ELet
                     ( [ ( BName ("temp_tuple_name#2", false, 0),
                           EGetItem (EId ("temp_tuple_name#1", 0), ENumber (1L, 0), 0),
                           0 ) ],
                       ELet
                         ( [ ( BName ("b", false, 0),
                               EGetItem (EId ("temp_tuple_name#2", 0), ENumber (0L, 0), 0),
                               0 ) ],
                           ELet
                             ( [ ( BName ("c", false, 0),
                                   EGetItem (EId ("temp_tuple_name#2", 0), ENumber (1L, 0), 0),
                                   0 ) ],
                               ELet
                                 ( [ ( BName ("d", false, 0),
                                       EGetItem (EId ("temp_tuple_name#1", 0), ENumber (2L, 0), 0),
                                       0 ) ],
                                   ENumber (5L, 0),
                                   0 ),
                               0 ),
                           0 ),
                       0 ),
                   0 ),
               0 ),
           0 ) );
    tp "seq"
      (desugar (Program ([], ESeq (ENumber (1L, 0), ENumber (2L, 0), 0), 0)))
      (Program
         ([], ELet ([(BName ("blank#1", false, 0), ENumber (1L, 0), 0)], ENumber (2L, 0), 0), 0) );
    tp "fun_args"
      (desugar
         (Program
            ( [ DFun
                  ( "foo",
                    [ BName ("a", false, 0);
                      BTuple ([BName ("b", false, 0); BName ("c", false, 0)], 0);
                      BName ("d", false, 0) ],
                    ENumber (2L, 0),
                    0 ) ],
              ENumber (2L, 0),
              0 ) ) )
      (Program
         ( [ DFun
               ( "foo",
                 [BName ("a", false, 0); BName ("temp_arg#1", false, 0); BName ("d", false, 0)],
                 ELet
                   ( [(BName ("temp_tuple_name#2", false, 0), EId ("temp_arg#1", 0), 0)],
                     ELet
                       ( [ ( BName ("b", false, 0),
                             EGetItem (EId ("temp_tuple_name#2", 0), ENumber (0L, 0), 0),
                             0 ) ],
                         ELet
                           ( [ ( BName ("c", false, 0),
                                 EGetItem (EId ("temp_tuple_name#2", 0), ENumber (1L, 0), 0),
                                 0 ) ],
                             ENumber (2L, 0),
                             0 ),
                         0 ),
                     0 ),
                 0 ) ],
           ENumber (2L, 0),
           0 ) );
    ( "splitting"
    >:: fun _ -> assert_equal (split_at [1; 2; 3; 4; 5] 3) ([1; 2; 3], [4; 5]) ~printer:dump ) ]
;;

let anf_tests =
  [ tanf "prim2_anf"
      (Program ([], EPrim2 (Times, ENumber (8L, 0), ENumber (3L, 0), 0), 0))
      (AProgram ([], ACExpr (CPrim2 (Times, ImmNum (8L, ()), ImmNum (3L, ()), ())), ()));
    tanf "decl_first_degree"
      (Program
         ( [DFun ("foo", [BName ("x", true, 0)], EId ("x", 0), 0)],
           EApp ("foo", [ENumber (1L, 0)], Snake, 0),
           0 ) )
      (AProgram
         ( [ADFun ("foo", ["x"], ACExpr (CImmExpr (ImmId ("x", ()))), ())],
           ACExpr (CApp ("foo", [ImmNum (1L, ())], Snake, ())),
           () ) ) ]
;;

let stack_alloc = "def foo(x):
    let 
        a = 1,
        b = x + a
    in
        b

let a = 12
in foo(5)";;
let nsa_tests = [
  tnsa "nsa1" (AProgram
  ( [ADFun ("foo", ["x"], ACExpr (CImmExpr (ImmId ("x", 0))), 0)],
    ACExpr (CApp ("foo", [ImmNum (1L, 0)], Snake, 0)),
    0 ) ) 
    [];
]

let suite = "suite" >::: pair_tests @ input @ desugar_tests

let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
