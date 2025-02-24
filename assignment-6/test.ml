open Compile
open Runner
open OUnit2
open Pretty
open Exprs
open Errors

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
      \            end" "" "(4, nil)";
    t "tup3"
      "let t = (4, (5, nil)) in\n\
      \            begin\n\
      \              t[1] := t;\n\
      \              t\n\
      \            end" "" "(4, <cyclic tuple 1>)";
    t "tup4" "let t = (4, 6) in\n            (t, t)" "" "((4, 6), (4, 6))" ]
;;

(* let oom = [
 *   tgcerr "oomgc1" (7) "(1, (3, 4))" "" "Out of memory";
 *   tgc "oomgc2" (8) "(1, (3, 4))" "" "(1, (3, 4))";
 *   tvgc "oomgc3" (8) "(1, (3, 4))" "" "(1, (3, 4))";
 *   tgc "oomgc4" (4) "(3, 4)" "" "(3, 4)";
 * ] *)

let input = [t "input1" "let x = input() in x + 2" "123" "125"]

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
         ([], ELet ([(BName ("blank#1", false, 0), ENumber (1L, 0), 0)], ENumber (2L, 0), 0), 0) )
  ]
;;

let suite = "suite" >::: (*pair_tests @ input @*) desugar_tests

let () = run_test_tt_main ("all_tests" >::: [suite])
