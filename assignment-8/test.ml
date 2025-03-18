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

let tparse name program expected =
  name
  >:: fun _ ->
  assert_equal (untagP expected) (untagP (parse_string name program)) ~printer:string_of_program
;;

let teq name actual expected = name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)

let tfvs name program expected =
  name
  >:: fun _ ->
  let ast = parse_string name program in
  let anfed = anf (tag ast) in
  match anfed with
  | AProgram (body, _) ->
      let vars = free_vars body in
      let c = Stdlib.compare in
      let str_list_print strs = "[" ^ ExtString.String.join ", " strs ^ "]" in
      assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print
;;

let forty_one = "41"

let forty_one_a = AProgram (ACExpr (CImmExpr (ImmNum (41L, ()))), ())

let test_prog =
  "let x = if sub1(55) < 54: (if 1 > 0: add1(2) else: add1(3)) else: (if 0 == 0: sub1(4) else: \
   sub1(5)) in x"
;;

let anf1 = anf (tag (parse_string "test" test_prog))

let suite =
  "suite"
  >::: [ t "test_is_bool1" "isbool(true)" "" "true";
         t "test_is_bool2" "isbool(false)" "" "true";
         t "test_is_bool3" "isbool(0)" "" "false";
         t "test_is_bool4" "isbool(123)" "" "false";
         t "test_is_bool5" "isbool((0,123))" "" "false";
         t "test_is_bool6" "isbool((true,123))" "" "false";
         t "test_is_bool7" "isbool((123,123))" "" "false";
         t "test_is_bool8" "isbool((false,123))" "" "false";
         t "test_is_tuple1" "istuple(true)" "" "false";
         t "test_is_tuple2" "istuple(false)" "" "false";
         t "test_is_tuple3" "istuple(0)" "" "false";
         t "test_is_tuple4" "istuple(123)" "" "false";
         t "test_is_tuple5" "istuple((0,123))" "" "true";
         t "test_is_tuple6" "istuple((true,123))" "" "true";
         t "test_is_tuple7" "istuple((123,123))" "" "true";
         t "test_is_tuple8" "istuple((false,123))" "" "true";
         t "test_is_num1" "isnum(true)" "" "false";
         t "test_is_num2" "isnum(false)" "" "false";
         t "test_is_num3" "isnum(0)" "" "true";
         t "test_is_num4" "isnum(123)" "" "true";
         t "test_is_num5" "isnum((0,123))" "" "false";
         t "test_is_num6" "isnum((true,123))" "" "false";
         t "test_is_num7" "isnum((123,123))" "" "false";
         t "test_is_num8" "isnum((false,123))" "" "false";
         tanf "forty_one_anf" (Program ([], ENumber (41L, ()), ())) forty_one_a;
         terr "scope_err1" "let x = true in (let y = (let x = false in x) in y)" ""
           "shadows one defined";
         ta "forty_one_run_anf" (atag forty_one_a, []) "" "41";
         t "forty_one" forty_one "" "41";
         t "test" test_prog "" "3";
         (* Some useful if tests to start you off *)
         t "if1" "if 7 < 8: 5 else: 3" "" "5";
         t "if2" "if 0 > 1: 4 else: 2" "" "2";
         terr "overflow" "add1(5073741823000000000)" "" "overflow"
         (* tvg "funcalls" "def fact(n): if n < 2: 1 else: n * fact(n - 1)\n\nfact(5)" "" "120" *)
       ]
;;

let () = run_test_tt_main ("all_tests" >::: [(* suite; *) input_file_test_suite ()])
