open OUnit2
open Test_funcs
open Compile
open Runner
open OUnit2
open Pretty
open Exprs
open Phases
open Assembly
open Util
open Constants
open Env
open Graph
open Well_formed
open Desugar
open Rename
open Anf
open Free_vars
open Naive_alloc
open Liveness
open Register_alloc
open Codegen

(** Tests for "Racer", Viper's register-allocation system. *)

(** Test naive stack allocation. *)
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

(** Tests for register allocation *)
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

(** Test for equality over color mappings.*)
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

(** Test interference graph. *)
let tig name program expected =
  let (AProgram (body, _)) =
    live_in_program (free_vars_cache (atag (anf (tag (parse_string name program)))))
  in
  let g = interfere body in
  name
  >:: fun _ -> assert_equal (string_of_graph expected) (string_of_graph g) ~printer:(fun s -> s)
;;

(** Test colored interference graph. *)
let tigc name program expected =
  let (AProgram (body, _)) =
    live_in_program (free_vars_cache (atag (anf (tag (parse_string name program)))))
  in
  let g = color_graph (interfere body) StringMap.empty in
  name
  >:: fun _ ->
  assert_equal (string_of_name_envt expected) (string_of_name_envt g) ~printer:(fun s -> s)
;;

let empty_map = StringMap.empty

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
    tigc "adder1" "add1(5)" empty_map;
    (* Uses 2 registers *)
    tigc "adder2" "add1(add1(add1(add1(5))))"
      (assoc_to_map [("unary_3", Reg R12); ("unary_4", Reg R13); ("unary_5", Reg R12)]);
    tigc "boa1" "1 + 2 + 3 + 4 + 5"
      (assoc_to_map [("binop_3", Reg R12); ("binop_4", Reg R13); ("binop_5", Reg R12)]);
    tigc "boa2" "(((1 + 2) + 3) + (4 + 5))"
      (assoc_to_map [("binop_3", Reg R13); ("binop_4", Reg R12); ("binop_8", Reg R12)]) ]
;;

let run_with_ra =
  [ tr "adder1" "add1(5)" "" "6";
    tr "adder2" "add1(add1(add1(add1(5))))" "" "9";
    tr "boa1" "1 + 2 + 3 + 4 + 5" "" "15";
    tr "boa2" "(((1 + 2) + 3) + (4 + 5))" "" "15";
    tr "nested_lambdas1" "let foo = (lambda(x): (lambda(y): y + x)) in 3" "" "3";
    tr "nested_lambdas2" "let foo = (lambda(x): (lambda(y): y - x)) in foo(3)(15)" "" "12" ]
;;

module Suite : TestSuite = struct
  let suite = nsa @ ra @ coloring @ interf @ run_with_ra
end
