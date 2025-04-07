open Compile
open Runner
open OUnit2
open Pretty
open Exprs
open Errors

let t name program input expected =
  name >:: test_run ~args:[] ~std_input:input Naive program name expected
;;

let tr name program input expected =
  name >:: test_run ~args:[] ~std_input:input Register program name expected
;;

let ta name program input expected =
  name >:: test_run_anf ~args:[] ~std_input:input program name expected
;;

let tgc name heap_size program input expected =
  name >:: test_run ~args:[string_of_int heap_size] ~std_input:input Naive program name expected
;;

let tvg name program input expected =
  name >:: test_run_valgrind ~args:[] ~std_input:input Naive program name expected
;;

let tvgc name heap_size program input expected =
  name
  >:: test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input Naive program name expected
;;

let terr name program input expected =
  name >:: test_err ~args:[] ~std_input:input Naive program name expected
;;

let tgcerr name heap_size program input expected =
  name >:: test_err ~args:[string_of_int heap_size] ~std_input:input Naive program name expected
;;

let tanf name program expected =
  name >:: fun _ -> assert_equal expected (anf (tag program)) ~printer:string_of_aprogram
;;

let tparse name program expected =
  name
  >:: fun _ ->
  assert_equal (untagP expected) (untagP (parse_string name program)) ~printer:string_of_program
;;

let teq name actual expected = name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)

(* let tfvs name program expected =
  name
  >:: fun _ ->
  let ast = parse_string name program in
  let anfed = anf (tag ast) in
  let vars = free_vars_cache anfed in
  let c = Stdlib.compare in
  let str_list_print strs = "[" ^ ExtString.String.join ", " strs ^ "]" in
  assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print
;; *)

let set = StringSet.of_list

let empty = StringSet.empty

let string_of_set s =
  if StringSet.cardinal s = 0 then
    "[]"
  else
    StringSet.fold (fun x acc -> acc ^ ";" ^ x) s "@"
;;

let tfvsc name program expected =
  name
  >:: fun _ ->
  let ast = parse_string name program in
  let anfed = anf (tag ast) in
  let cached = free_vars_cache anfed in
  let printer = (string_of_aprogram_with 100 string_of_set) in
  assert_equal (printer expected) (printer cached) ~printer:(fun x -> x)
;;

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
                           empty ),
                       ACExpr (CImmExpr (ImmId ("lam_6", set ["lam_6"]))),
                       empty ),
                   set ["w"; "x"; "y"; "z"] ),
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
               set ["w"; "x"; "y"; "z"] ),
           set ["w"; "x"; "y"; "z"] ) );
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

let suite = "unit_tests" >::: fvc
(* pair_tests @ oom @ gc @ input *)

let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
