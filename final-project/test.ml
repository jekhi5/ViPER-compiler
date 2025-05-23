open Compile
open Runner
open OUnit2
open Pretty
open Exprs
open Phases
open Graph
open Assembly

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
  assert_equal
    (string_of_program (untagP expected))
    (string_of_program (untagP (parse_string name program)))
;;

let teq name actual expected = name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)

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
  let result = compute_live_in body empty in
  name >:: fun _ -> assert_equal expected result ~printer:(string_of_aexpr_with 100 string_of_set)
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
  [ tra "simple_ra1" "let x = 1 in x + 5" [("ocsh_0", [("x", Reg R12)])];
    tra "simple_ra2" "let x = 1, y = 3, z = 4 in 5"
      [("ocsh_0", [("x", Reg R12); ("y", Reg R12); ("z", Reg R12)])];
    tra "simple_lambda" "let a = 1 in (lambda(x): x)(5)"
      [("ocsh_0", [("a", Reg R12); ("lam_8", Reg R12)]); ("lam_8", [("x", RegOffset (3, RBP))])];
    (* Remember that all lambdas are indirected... *)
    tra "non_nested_lambdas"
      "let a=1, foo = (lambda(x): x), bar = (lambda(y, x): y + x), baz = (lambda: a) in 1"
      [ ( "ocsh_0",
          [ ("a", Reg R14);
            ("lam_8", Reg R13);
            ("foo", Reg R12);
            ("lam_13", Reg R13);
            ("bar", Reg R12);
            ("lam_21", Reg R13);
            ("baz", Reg R12) ] );
        ("lam_8", [("x", RegOffset (3, RBP))]) ];
    tra "nested_lambdas" "let foo = (lambda(x): (lambda(y): y + x)) in 1"
      [ ("ocsh_0", []);
        ("lam_5", [("x", RegOffset (3, RBP))]);
        ("lam_6", [("y", RegOffset (3, RBP))]) ];
    tra "letrec1" "let rec foo = (lambda(x): x) in 1"
      [ ("ocsh_0", [("lam_5", RegOffset (~-1, RBP)); ("foo", RegOffset (~-2, RBP))]);
        ("lam_5", [("x", RegOffset (3, RBP)); ("lam_5", RegOffset (~-1, RBP))]) ];
    tra "number" "1" [("ocsh_0", [])];
    tra "nested_let_and_lambda"
      "\n\
      \    let \n\
      \      a = 5,\n\
      \      b = add1(a),\n\
      \      c = sub1(b),\n\
      \      e = 2,\n\
      \      f = let\n\
      \            x = 4,\n\
      \            y = (lambda(r, p): r + p),\n\
      \            z = add1(y(x, e))\n\
      \          in\n\
      \            z\n\
      \    in\n\
      \      f"
      [ ( "ocsh_0",
          [ ("a", Reg R12);
            ("app_34", Reg R12);
            ("b", Reg R13);
            ("c", Reg R12);
            ("e", Reg R13);
            ("f", Reg R12);
            ("lam_25", Reg R12);
            ("x", Reg R14);
            ("y", Reg RBX);
            ("z", Reg R13) ] );
        ("lam_25", [("p", RegOffset (4, RBP)); ("r", RegOffset (3, RBP))]) ] ]
;;

let live_out = []

let tc ?(colors = colors) name given expected =
  name
  >:: fun _ ->
  assert_equal
    (string_of_name_envt (assoc_to_map expected))
    (string_of_name_envt (color_graph ~colors given StringMap.empty))
    ~printer:(fun s -> s)
;;

let graph (nodes : (string * string list) list) =
  List.fold_left
    (fun g (node, neighbors) -> List.fold_left (fun g' n -> add_edge g' node n) g neighbors)
    Graph.empty nodes
;;

let g1 = graph [("a", ["b"; "c"; "d"; "e"; "f"])]

let g2 =
  graph
    [ ("a", ["b"; "c"; "d"; "e"; "f"; "g"; "h"]);
      ("b", ["a"; "c"; "d"; "e"; "f"; "g"; "h"]);
      ("c", ["b"; "a"; "d"; "e"; "f"; "g"; "h"]);
      ("d", ["b"; "c"; "a"; "e"; "f"; "g"; "h"]);
      ("e", ["b"; "c"; "d"; "a"; "f"; "g"; "h"]);
      ("f", ["b"; "c"; "d"; "e"; "a"; "g"; "h"]);
      ("g", ["b"; "c"; "d"; "e"; "f"; "a"; "h"]);
      ("h", ["b"; "c"; "d"; "e"; "f"; "g"; "a"]) ]
;;

let g3 =
  graph
    [ ("a", ["b"; "c"; "d"; "e"]);
      ("b", ["a"; "c"]);
      ("c", ["a"; "b"]);
      ("d", ["a"; "e"]);
      ("e", ["a"; "d"]) ]
;;

let coloring =
  [ tc "hubwheel" g1
      [ ("a", Reg R13);
        ("b", Reg R12);
        ("c", Reg R12);
        ("d", Reg R12);
        ("e", Reg R12);
        ("f", Reg R12) ];
    tc "stack_spill" g2
      [ ("a", Reg R12);
        ("b", Reg R13);
        ("c", Reg R14);
        ("d", Reg RBX);
        ("e", RegOffset (~-1, RBP));
        ("f", RegOffset (~-2, RBP));
        ("g", RegOffset (~-3, RBP));
        ("h", RegOffset (~-4, RBP)) ];
    tc "stack_spill2" ~colors:[Reg R12] g1
      [ ("a", RegOffset (~-1, RBP));
        ("b", Reg R12);
        ("c", Reg R12);
        ("d", Reg R12);
        ("e", Reg R12);
        ("f", Reg R12) ];
    tc "cliques" g3 [("a", Reg R14); ("b", Reg R12); ("c", Reg R13); ("d", Reg R12); ("e", Reg R13)]
  ]
;;

let tig name program expected =
  let (AProgram (body, _)) =
    live_in_program (free_vars_cache (atag (anf (tag (parse_string name program)))))
  in
  let g = interfere body in
  name
  >:: fun _ -> assert_equal (string_of_graph expected) (string_of_graph g) ~printer:(fun s -> s)
;;

let tigc name program expected =
  let (AProgram (body, _)) =
    live_in_program (free_vars_cache (atag (anf (tag (parse_string name program)))))
  in
  let g = color_graph (interfere body) StringMap.empty in
  name
  >:: fun _ ->
  assert_equal (string_of_name_envt expected) (string_of_name_envt g) ~printer:(fun s -> s)
;;

let empty = StringMap.empty

let interf =
  [ tigc "simple" "let a = 1 in b" (assoc_to_map [("a", Reg R12); ("b", Reg R13)]);
    tigc "if1" "if true: let x = 1 in x else: let y = 2 in y"
      (assoc_to_map [("x", Reg R12); ("y", Reg R12)]);
    tigc "let1" "let a = 1, b = 2, c = 3 in 4"
      (assoc_to_map [("a", Reg R12); ("b", Reg R12); ("c", Reg R12)]);
    tigc "let2" "let a = 1, b = 2, c = 3 in b"
      (assoc_to_map [("a", Reg R12); ("b", Reg R12); ("c", Reg R13)]);
    tigc "let3" "let a = 1, b = a, c = a in c"
      (assoc_to_map [("a", Reg R13); ("b", Reg R12); ("c", Reg R12)]);
    tigc "let4" "let a = 1, b = a, c = b in c"
      (assoc_to_map [("a", Reg R12); ("b", Reg R13); ("c", Reg R12)]);
    (* Only uses 1 register *)
    tigc "adder1" "add1(5)" empty;
    (* Uses 2 registers *)
    tigc "adder2" "add1(add1(add1(add1(5))))"
      (assoc_to_map [("unary_3", Reg R12); ("unary_4", Reg R13); ("unary_5", Reg R12)]);
    tigc "boa1" "1 + 2 + 3 + 4 + 5"
      (assoc_to_map [("binop_3", Reg R12); ("binop_4", Reg R13); ("binop_5", Reg R12)]);
    tigc "boa2" "(((1 + 2) + 3) + (4 + 5))"
      (assoc_to_map [("binop_3", Reg R13); ("binop_4", Reg R12); ("binop_8", Reg R12)]) ]
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

let parse_checks =
  [ tparse "single_check_spits" "1 check: 1 spits (lambda(x): 1) end"
      (Program
         ( [],
           ENumber (1L, ()),
           [ ECheck
               ( [ ETestOp2
                     ( ENumber (1L, ()),
                       ELambda ([BName ("x", false, ())], ENumber (1L, ()), ()),
                       DeepEq,
                       false,
                       () ) ],
                 () ) ],
           () ) );
    tparse "complex_check"
      "\n\
      \      true \n\
      \      \n\
      \      check: \n\
      \        let \n\
      \          a = 1, \n\
      \          b = 2 \n\
      \        in (a, b) \n\
      \        spits \n\
      \        (1, 2),\n\
      \        4 + true sheds RuntimeException,\n\
      \        let foo = (lambda(x, y): (x, y)) in foo(1, 2) !bites (1, 2),\n\
      \        \n\
      \        1 !spits 5\n\
      \      end\n\n\
      \      check: 1 broods (lambda(x): 1) end"
      (Program
         ( [],
           EBool (true, ()),
           [ ECheck
               ( [ ETestOp2
                     ( ELet
                         ( [ (BName ("a", false, ()), ENumber (1L, ()), ());
                             (BName ("b", false, ()), ENumber (2L, ()), ()) ],
                           ETuple ([EId ("a", ()); EId ("b", ())], ()),
                           () ),
                       ETuple ([ENumber (1L, ()); ENumber (2L, ())], ()),
                       DeepEq,
                       false,
                       () );
                   ETestOp2
                     ( EPrim2 (Plus, ENumber (4L, ()), EBool (true, ()), ()),
                       EException (Runtime, ()),
                       Raises,
                       false,
                       () );
                   ETestOp2
                     ( ELet
                         ( [ ( BName ("foo", false, ()),
                               ELambda
                                 ( [BName ("x", false, ()); BName ("y", false, ())],
                                   ETuple ([EId ("x", ()); EId ("y", ())], ()),
                                   () ),
                               () ) ],
                           EApp (EId ("?foo", ()), [ENumber (1L, ()); ENumber (2L, ())], Snake, ()),
                           () ),
                       ETuple ([ENumber (1L, ()); ENumber (2L, ())], ()),
                       ShallowEq,
                       true,
                       () );
                   ETestOp2 (ENumber (1L, ()), ENumber (5L, ()), DeepEq, true, ()) ],
                 () );
             ECheck
               ( [ ETestOp1
                     ( ENumber (1L, ()),
                       ELambda ([BName ("x", false, ())], ENumber (1L, ()), ()),
                       false,
                       () ) ],
                 () ) ],
           () ) );
    tparse "basic_try_catch" "try 1 catch RuntimeException as r in 1"
      (Program
         ( [],
           ETryCatch
             ( ENumber (1L, ()),
               BName ("r", false, ()),
               EException (Runtime, ()),
               ENumber (1L, ()),
               () ),
           [],
           () ) ) ]
;;

let suite = "unit_tests" >::: parse_checks
(* @ fvc @ nsa @ ra @ coloring @ interf @ pair_tests @ run_with_ra @ live_out @ oom
       @ gc @ input *)

let () = run_test_tt_main ("all_tests" >::: [suite; input_file_test_suite ()])
