open Compile
open Runner
open OUnit2
open Pretty
open Exprs
open Phases

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

let tparse name program expected =
  name
  >:: fun _ ->
  assert_equal (untagP expected) (untagP (parse_string name program)) ~printer:string_of_program
;;

let teq name actual expected =
  name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> "\n\n" ^ s)
;;

let envt_envt_of_list (e : (string * (string * 'a) list) list) : 'a name_envt name_envt =
  assoc_to_map (List.map (fun (key, inner) -> (key, assoc_to_map inner)) e)
;;

let tnsa name program expected =
  let _, locations = naive_stack_allocation (atag (anf (tag (parse_string name program)))) in
  name
  >:: fun _ ->
  assert_equal
    (string_of_name_envt_envt (envt_envt_of_list expected))
    (string_of_name_envt_envt locations)
    ~printer:(fun s -> s)
;;

let tfvs name program expected =
  name
  >:: fun _ ->
  let ast = parse_string name program in
  let (AProgram (anfed, _)) = anf (tag ast) in
  let vars = StringSet.elements @@ free_vars anfed in
  let c = Stdlib.compare in
  let str_list_print strs = "[" ^ ExtString.String.join ", " strs ^ "]" in
  assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print
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
    t "tup4" "let t = (4, 6) in\n            (t, t)" "" "((4, 6), (4, 6))";
    t "tup5" "let t = (1,2,3,4,5) in t" "" "(1, 2, 3, 4, 5)" ]
;;

let oom =
  [ tgcerr "oomgc1" (7 + builtins_size) "(1, (3, 4))" "" "Out of memory";
    tgc "oomgc2" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
    tvgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
    tgc "oomgc4" (4 + builtins_size) "(3, 4)" "" "(3, 4)";
    tgcerr "oomgc5" (3 + builtins_size) "(1, 2, 3, 4, 5, 6, 7, 8, 9, 0)" "" "Allocation" ]
;;

let gc =
  [ tgc "gc_lam1" (20 + builtins_size)
      "let f = (lambda: (1, 2)) in\n\
      \       begin\n\
      \         f();\n\
      \         f();\n\
      \         f();\n\
      \         f()\n\
      \       end"
      "" "(1, 2)";
    tgc "gc_tup2" (10 + builtins_size)
      "(1,2,3,4,5);\n(1,2,3,4,5);\n(1,2,3,4,5);\n(1,2,3,4,5);\n(1,2,3,4,5)" "" "(1, 2, 3, 4, 5)" ]
;;

let input = [t "input1" "let x = input() in x + 2" "123" "125"]

let nsa =
  [ tnsa "simple_nsa1" "let x = 1 in x + 5" [("ocsh_0", [("x", RegOffset (~-1, RBP))])];
    tnsa "simple_nsa2" "let x = 1, y = 3, z = 4 in 5"
      [ ( "ocsh_0",
          [("x", RegOffset (~-1, RBP)); ("y", RegOffset (~-2, RBP)); ("z", RegOffset (~-3, RBP))] )
      ];
    tnsa "simple_lambda" "let a = 1 in (lambda(x): x)(5)"
      [ ("ocsh_0", [("a", RegOffset (~-1, RBP)); ("lam_8", RegOffset (~-2, RBP))]);
        ("lam_8", [("x", RegOffset (3, RBP))]) ];
    (* Remember that all lambdas are indirected... *)
    tnsa "non_nested_lambdas"
      "let a=1, foo = (lambda(x): x), bar = (lambda(y, x): y + x), baz = (lambda: a) in 1"
      [ ( "ocsh_0",
          [ ("a", RegOffset (~-1, RBP));
            ("lam_8", RegOffset (~-2, RBP));
            ("foo", RegOffset (~-3, RBP));
            ("lam_13", RegOffset (~-4, RBP));
            ("bar", RegOffset (~-5, RBP));
            ("lam_21", RegOffset (~-6, RBP));
            ("baz", RegOffset (~-7, RBP)) ] );
        ("lam_8", [("x", RegOffset (3, RBP))]);
        ("lam_13", [("y", RegOffset (3, RBP)); ("x", RegOffset (4, RBP))]);
        ("lam_21", []) ];
    tnsa "nested_lambdas" "let foo = (lambda(x): (lambda(y): y + x)) in 1"
      [ ("ocsh_0", [("lam_5", RegOffset (~-1, RBP)); ("foo", RegOffset (~-2, RBP))]);
        ("lam_5", [("x", RegOffset (3, RBP)); ("lam_6", RegOffset (~-1, RBP))]);
        ("lam_6", [("y", RegOffset (3, RBP))]) ];
    (* Commented this test because we know LetRec is broken... *)
    (* tnsa "letrec1" "let rec foo = (lambda(x): x) in 1"
      [ ("ocsh_0", [("lam_5", RegOffset (~-1, RBP)); ("foo", RegOffset (~-2, RBP))]);
        ("lam_5", [("x", RegOffset (3, RBP)); ("lam_5", RegOffset (~-1, RBP))]) ]; *)
    tnsa "number" "1" [("ocsh_0", [])] ]
;;

let fv = [tfvs "fv1" "(lambda(a): a + x + z)(5)" ["x"; "z"]]

let suite =
  "unit_tests"
  >:::
  (* pair_tests @ oom @ gc @ input *)
  nsa @ pair_tests @ gc @ fv
;;

(* input_file_test_suite () *)
let () = run_test_tt_main ("all_tests" >::: [(*suite;*) input_file_test_suite ()])
