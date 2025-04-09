open Compile
open Runner
open OUnit2
open Pretty
open Exprs
open Errors
open Phases

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
  let printer = string_of_aprogram_with 100 string_of_set in
  assert_equal (printer expected) (printer cached) ~printer:(fun x -> x)
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

let tra name program expected =
  let _, locations = register_allocation (atag (anf (tag (parse_string name program)))) in
  name
  >:: fun _ ->
  assert_equal
    (string_of_name_envt_envt (envt_envt_of_list expected))
    (string_of_name_envt_envt locations)
    ~printer:(fun s -> s)
;;

let tli name program expected =
  let (AProgram (body, _)) = free_vars_cache (atag (anf (tag (parse_string name program)))) in
  let result = compute_live_in body in
  name >:: fun _ -> assert_equal (StringSet.of_list expected) result ~printer:string_of_set
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

let ra =
  [ tra "simple_ra1" "let x = 1 in x + 5" [("ocsh_0", [("x", RegOffset (~-1, RBP))])];
    tra "simple_ra2" "let x = 1, y = 3, z = 4 in 5"
      [ ( "ocsh_0",
          [("x", RegOffset (~-1, RBP)); ("y", RegOffset (~-2, RBP)); ("z", RegOffset (~-3, RBP))] )
      ];
    tra "simple_lambda" "let a = 1 in (lambda(x): x)(5)"
      [ ("ocsh_0", [("a", RegOffset (~-1, RBP)); ("lam_8", RegOffset (~-2, RBP))]);
        ("lam_8", [("x", RegOffset (3, RBP))]) ];
    (* Remember that all lambdas are indirected... *)
    tra "non_nested_lambdas"
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
    tra "nested_lambdas" "let foo = (lambda(x): (lambda(y): y + x)) in 1"
      [ ("ocsh_0", [("lam_5", RegOffset (~-1, RBP)); ("foo", RegOffset (~-2, RBP))]);
        ("lam_5", [("x", RegOffset (3, RBP)); ("lam_6", RegOffset (~-1, RBP))]);
        ("lam_6", [("y", RegOffset (3, RBP))]) ];
    (* Commented this test because we know LetRec is broken... *)
    (* tra "letrec1" "let rec foo = (lambda(x): x) in 1"
      [ ("ocsh_0", [("lam_5", RegOffset (~-1, RBP)); ("foo", RegOffset (~-2, RBP))]);
        ("lam_5", [("x", RegOffset (3, RBP)); ("lam_5", RegOffset (~-1, RBP))]) ]; *)
    tra "number" "1" [("ocsh_0", [])] ]
;;

let live_in =
  [ tli "given_ex"
      "let \n\
      \     x = true \n\
      \   in\n\
      \     let \n\
      \       y = if true: let \n\
      \                      b = 5 \n\
      \                    in \n\
      \                      b else: 6 \n\
      \     in\n\
      \      x"
      [];
    tli "let_sub_expr" "let y = (if true: (let b = 5 in b) else: 6) in y" [];
    tli "let" "let x = 5 in a + b" ["a"; "b"] ]
;;

let live_out = []

let tc name given expected =
  name >:: fun _ ->
    assert_equal
      (color_graph given [])
      (assoc_to_map expected)

let graph (nodes : (string * string list) list) =
  List.fold_left (fun g (node, neighbors) -> List.fold_left (g' n -> add_edge g' node n) g neighbors) Graph.empty nodes

let g1 = graph [
  ("a" -> ["b"; "c"; "d"; "e"; "f"])

let g2 = graph [
  ("a" -> ["b"; "c"; "d"; "e"; "f"; "g"; "h"]);
  ("b" -> ["a"; "c"; "d"; "e"; "f"; "g"; "h"]);
  ("c" -> ["b"; "a"; "d"; "e"; "f"; "g"; "h"]);
  ("d" -> ["b"; "c"; "a"; "e"; "f"; "g"; "h"]);
  ("e" -> ["b"; "c"; "d"; "a"; "f"; "g"; "h"]);
  ("f" -> ["b"; "c"; "d"; "e"; "a"; "g"; "h"]);
  ("g" -> ["b"; "c"; "d"; "e"; "f"; "a"; "h"]);
  ("h" -> ["b"; "c"; "d"; "e"; "f"; "g"; "a"]);
]


let color_graph = [
  tc "hubwheel" g1 [("a", Reg R10); ("b", Reg R11); ("c", Reg R11); ("d", Reg R11); ("e", Reg R11); ("f", Reg R11);
  tc "stack_spill" g1 [("a", Reg R10); ("b", Reg R11); ("c", Reg R12); ("d", Reg R13); ("e", Reg R14); ("f", Reg R15); ("g", RegOffset(~-8, RBP)); ("h", RegOffset(~-16, RBP));
  
  ]  
]

let input = [t "input1" "let x = input() in x + 2" "123" "125"]

let suite = "unit_tests" >::: fvc @ nsa @ ra @ live_in @ live_out
(* pair_tests @ oom @ gc @ input *)

let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
