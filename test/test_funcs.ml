open Runner
open OUnit2
open Pretty
open Exprs
open Phases
open Graph
open Env
open Anf
open Free_vars
open Naive_alloc
open Liveness
open Register_alloc

type test_suite = test list

module type TestSuite = sig
  val suite : test_suite
end

(** [t name program input expected] uses the [Naive] allocation strategy to run a [program], given
    as a source string, and compares its output to [expected]. A test [name] must be given as well
    as any [input]. If no input is needed, [""] should be passed. *)
let t name program input expected =
  name >:: test_run ~args:[] ~std_input:input Naive program name expected
;;

(** [tr name program input expected] uses the [Register] allocation strategy to run a [program],
    given as a source string, and compares its output to [expected]. A test [name] must be given as
    well as any [input]. If no input is needed, [""] should be passed. *)
let tr name program input expected =
  name >:: test_run ~args:[] ~std_input:input Register program name expected
;;

(** [ta name program input expected] runs a [program], given as an ANFed expr, and compares its
    output to [expected]. A test [name] must be given as well as any [input]. If no input is needed,
    [""] should be passed. *)
let ta name program input expected =
  name >:: test_run_anf ~args:[] ~std_input:input program name expected
;;

(** [tgc name heap_size program input expected] tests the garbage collection functionality by
    running a [program], given as a source string, with a user-set [heap_size] and compares its
    output to [expected]. The program is run using the [Naive] allocation strategy. A test [name]
    must be given as well as any [input]. If no input is needed, [""] should be passed. *)
let tgc name heap_size program input expected =
  name >:: test_run ~args:[string_of_int heap_size] ~std_input:input Naive program name expected
;;

(** [tvg name program input expected] allows for valgrind inspection during a program run. It uses
    the [Naive] allocation strategy to run a [program], given as a source string, and compares its
    output to [expected]. A test [name] must be given as well as any [input]. If no input is needed,
    [""] should be passed. *)
let tvg name program input expected =
  name >:: test_run_valgrind ~args:[] ~std_input:input Naive program name expected
;;

(** [tvgc name heap_size program input expected] allows for valgrind inspection during a program run
    while also testing garbage collection. It uses the [Naive] allocation strategy to run a
    [program], given as a source string, with a user-set [heap_size] and compares its output to
    [expected]. A test [name] must be given as well as any [input]. If no input is needed, [""]
    should be passed. *)
let tvgc name heap_size program input expected =
  name
  >:: test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input Naive program name expected
;;

(** [terr name program input expected] tests that a program outputs an error message with a
    substring of [expected]. The [program] is run using the [Naive] allocation strategy, given as a
    source string. A test [name] must be given as well as any [input]. If no input is needed, [""]
    should be passed. *)
let terr name program input expected =
  name >:: test_err ~args:[] ~std_input:input Naive program name expected
;;

(** [tgcerr name heap_size program input expected] tests that a program outputs an error message
    with a substring of [expected] while also allowing the user to set a [heap_size] to test garbage
    collection. The [program] is run using the [Naive] allocation strategy, given as a source
    string. A test [name] must be given as well as any [input]. If no input is needed, [""] should
    be passed. *)
let tgcerr name heap_size program input expected =
  name >:: test_err ~args:[string_of_int heap_size] ~std_input:input Naive program name expected
;;

(** [tanf name program expected] tests that the result of ANFing the given [program], given as a
    source string, matches the [expected] ANF expr. A test [name] must be given. *)
let tanf name program expected =
  name >:: fun _ -> assert_equal expected (anf (tag program)) ~printer:string_of_aprogram
;;

(** [tparse name program expected ] tests that the result of parsing the given [program], given as a
    source string, matches the [expected] parsed Program expr. A test [name] must be given. *)
let tparse name program expected =
  name
  >:: fun _ ->
  assert_equal
    (string_of_program (untagP expected))
    (string_of_program (untagP (parse_string name program)))
;;

(** [teq name actual expected] asserts that two strings are equal *)
let teq name actual expected = name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)

let set = StringSet.of_list

let empty_set = StringSet.empty

let string_of_set s =
  if StringSet.cardinal s = 0 then
    "[]"
  else
    StringSet.fold (fun x acc -> acc ^ ";" ^ x) s "@"
;;

(** [tfvsc name program expected] tests that running [free_vars_cache] on the given [program], given
    as a source string, matches the [expected] parsed [AProgram] expr. A test [name] must be given.
*)
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

(** [tnsa name program expected] tests that the _locations_ for the identifiers output from
    [naive_stack_allocation] for the given [program], given as a source string, matches the
    [expected] locations for the identifiers. An example [expected] list of locations could be:

    [[ ("ocsh_0", [("a", RegOffset (~-1, RBP)); ("lam_8", RegOffset (~-2, RBP))]); ("lam_8", [("x",
     RegOffset (3, RBP))]) ]]

    A test [name] must be given. *)
let tnsa name program expected =
  let _, locations = naive_stack_allocation (atag (anf (tag (parse_string name program)))) in
  name
  >:: fun _ ->
  assert_equal
    (string_of_name_envt_envt (envt_envt_of_list expected))
    (string_of_name_envt_envt locations)
    ~printer:(fun s -> s)
;;

(** [tra name program expected] tests that the _locations_ for the identifiers output from
    [register_allocation] for the given [program], given as a source string, matches the [expected]
    locations for the identifiers. An example [expected] list of locations could be:

    [("ocsh_0", [("a", Reg R12); ("lam_8", Reg R12)]); ("lam_8", [("x", RegOffset (3, RBP))])]

    A test [name] must be given. *)
let tra name program expected =
  let _, locations = register_allocation (atag (anf (tag (parse_string name program)))) in
  name
  >:: fun _ ->
  assert_equal
    (string_of_name_envt_envt (envt_envt_of_list expected))
    (string_of_name_envt_envt locations)
    ~printer:(fun s -> s)
;;

(** [tli name program expected] tests that the [compute_live_in] result on the body of the given
    [program], given as a source string, matches the [expected] AExpr. A test [name] must be given.
*)
let tli name program expected =
  let (AProgram (body, _)) = free_vars_cache (atag (anf (tag (parse_string name program)))) in
  let result = compute_live_in body empty_set in
  name >:: fun _ -> assert_equal expected result ~printer:(string_of_aexpr_with 100 string_of_set)
;;
