open Sexp
open OUnit2
open Expr
open ExtLib

(* a helper for testing integers *)
let t_int name value expected = name >:: fun _ -> assert_equal expected value ~printer:string_of_int

(* A helper for testing primitive values (won't print datatypes well) *)
let t_any name value expected = name >:: fun _ -> assert_equal expected value ~printer:dump

let t_string name value expected =
  name >:: fun _ -> assert_equal expected value ~printer:(fun str -> str)
;;

(* Feel free to add any new testing functions you may need *)

(* It can be useful to aggregate tests into lists if they test separate
   functions, and put them together at the end *)

let env1 = [("a", 5); ("b", 15)]

let env2 = []

let get_tests =
  [ t_any "get1" (get env1 "a") (Some 5);
    t_any "get2" (get env1 "b") (Some 15);
    t_any "get3" (get env1 "c") None;
    t_any "get4" (get env2 "a") None ]
;;

let contains_tests =
  [ t_any "contains1" (contains env1 "c") false;
    t_any "contains2" (contains env1 "a") true;
    t_any "contains3" (contains env2 "a") false;
    t_any "contains4" (contains env1 "b") true ]
;;

let add_tests =
  [ t_any "add1" (add env1 "c" 25) [("a", 5); ("b", 15); ("c", 25)];
    t_any "add2" (add env2 "a" ~-3) [("a", ~-3)];
    t_any "add3" (add env1 "b" 1) [("a", 5); ("b", 1)];
    t_any "add4" (add env1 "a" ~-6) [("a", ~-6); ("b", 15)] ]
;;

let evaluate_tests =
  [ t_int "evaluate1" (evaluate (Num 1) []) 1;
    t_int "evaluate2" (evaluate (Num ~-7) []) ~-7;
    t_int "evaluate3" (evaluate (Plus (Num 8, Num 3)) []) 11;
    t_int "evaluate4" (evaluate (Plus (Num 3, Num 8)) []) 11;
    t_int "evaluate5" (evaluate (Plus (Num ~-7, Num ~-3)) []) ~-10;
    t_int "evaluate6" (evaluate (Plus (Num 8, Num ~-3)) []) 5;
    t_int "evaluate7" (evaluate (Plus (Num ~-3, Num 8)) []) 5;
    t_int "evaluate8" (evaluate (Times (Num 0, Num 5)) []) 0;
    t_int "evaluate9" (evaluate (Times (Num 1, Num 5)) []) 5;
    t_int "evaluate10" (evaluate (Times (Num 7, Num 9)) []) 63;
    t_int "evaluate11" (evaluate (Times (Num 9, Num 7)) []) 63;
    t_int "evaluate12" (evaluate (Times (Num ~-14, Num ~-2)) []) 28;
    t_int "evaluate13" (evaluate (Times (Num ~-14, Num 2)) []) ~-28;
    t_int "evaluate14" (evaluate (Times (Num 2, Num ~-14)) []) ~-28;
    t_int "evaluate15" (evaluate (Plus (Num 6, Plus (Num ~-14, Num 2))) []) ~-6;
    t_int "evaluate16" (evaluate (Plus (Plus (Num ~-14, Num 2), Num 6)) []) ~-6;
    t_int "evaluate17" (evaluate (Plus (Num ~-6, Times (Num ~-14, Num 2))) []) ~-34;
    t_int "evaluate18" (evaluate (Plus (Times (Num ~-14, Num 2), Num ~-6)) []) ~-34;
    t_int "evaluate19" (evaluate (Plus (Times (Num ~-14, Num 2), Plus (Num 3, Num 8))) []) ~-17;
    t_int "evaluate20" (evaluate (Plus (Plus (Num 3, Num 8), Times (Num ~-14, Num 2))) []) ~-17;
    t_int "evaluate21" (evaluate (Plus (Times (Num 3, Num 8), Times (Num ~-14, Num 2))) []) ~-4;
    t_int "evaluate22" (evaluate (Times (Plus (Num 4, Num 8), Num 3)) []) 36;
    t_int "evaluate23" (evaluate (Times (Num 3, Plus (Num 4, Num 8))) []) 36;
    t_int "evaluate24" (evaluate (Times (Times (Num 4, Num 8), Num 3)) []) 96;
    t_int "evaluate25" (evaluate (Times (Num 3, Times (Num 4, Num 8))) []) 96;
    t_int "evaluate26" (evaluate (Times (Plus (Num 2, Num 8), Times (Num 4, Num 8))) []) 320;
    t_int "evaluate27" (evaluate (Times (Times (Num 4, Num 8), Plus (Num 2, Num 8))) []) 320;
    t_int "evaluate28" (evaluate (Times (Times (Num 4, Num 8), Times (Num 4, Num 8))) []) 1024;
    t_int "evaluate29"
      (evaluate (Times (Times (Num 4, Plus (Num 8, Num 1)), Plus (Num 4, Num 8))) [])
      432;
    t_int "evaluate30" (evaluate (Variable "x") [("x", 1)]) 1;
    t_int "evaluate31" (evaluate (Variable "x") [("x", ~-7)]) ~-7;
    t_int "evaluate32" (evaluate (Plus (Num ~-7, Variable "x")) [("x", ~-3)]) ~-10;
    t_int "evaluate33" (evaluate (Plus (Variable "a", Num 3)) [("a", 8)]) 11;
    t_int "evaluate34" (evaluate (Times (Num 0, Variable ")")) [(")", 5)]) 0;
    t_int "evaluate35" (evaluate (Times (Num 1, Variable "!")) [("!", 9)]) 9;
    t_int "evaluate36"
      (evaluate (Plus (Variable "variable", Times (Num ~-14, Num 2))) [("variable", -6)])
      ~-34;
    t_int "evaluate37" (evaluate (Plus (Num ~-6, Times (Num ~-14, Variable "hi"))) [("hi", 2)]) ~-34;
    t_int "evaluate38"
      (evaluate
         (Plus (Variable "bye", Times (Num ~-14, Variable "hi")))
         [("hi", 2); ("bye", ~-6); ("UNUSED", 4)] )
      ~-34;
    t_int "evaluate39"
      (evaluate
         (Times (Times (Variable "a", Plus (Variable "b", Variable "c")), Plus (Num 4, Variable "b"))
         )
         [("a", 4); ("UNUSED", 6); ("b", 8); ("c", 1)] )
      432;
    t_int "evaluate40"
      (evaluate
         (Plus (Plus (Variable "a", Variable "a"), Times (Variable "b", Variable "b")))
         [("a", 4); ("UNUSED", 6); ("b", 8); ("c", 1)] )
      72;
    ( "evaluate41"
    >:: fun _ ->
    assert_raises (Failure "Identifier `x` not found!") (fun () -> evaluate (Variable "x") []) );
    ( "evaluate41"
    >:: fun _ ->
    assert_raises (Failure "Identifier `a` not found!") (fun () -> evaluate (Variable "a") []) );
    ( "evaluate41"
    >:: fun _ ->
    assert_raises (Failure "Identifier `x` not found!") (fun () ->
        evaluate (Plus (Num ~-7, Variable "x")) [("p", ~-3)] ) );
    ( "evaluate41"
    >:: fun _ ->
    assert_raises (Failure "Identifier `uh-oh` not found!") (fun () ->
        evaluate (Plus (Variable "uh-oh", Num 3)) [("hmmm", ~-3)] ) );
    ( "evaluate41"
    >:: fun _ ->
    assert_raises (Failure "Identifier `brb` not found!") (fun () ->
        evaluate (Times (Variable "brb", Num 3)) [("idk", ~-3); ("DJ", 5)] ) );
    ( "evaluate41"
    >:: fun _ ->
    assert_raises (Failure "Identifier `jk` not found!") (fun () ->
        evaluate (Times (Num 3, Variable "jk")) [("lol", ~-3)] ) );
    ( "evaluate41"
    >:: fun _ ->
    assert_raises (Failure "Identifier `c` not found!") (fun () ->
        evaluate
          (Times
             (Times (Variable "a", Plus (Variable "b", Variable "c")), Plus (Num 4, Variable "b"))
          )
          [("a", ~-3); ("b", 5); ("OTHER", 10)] ) ) ]
;;

let pretty_tests =
  [ t_string "pretty1" (pretty (Num 1)) "1";
    t_string "pretty2" (pretty (Num ~-1)) "-1";
    t_string "pretty3" (pretty (Variable "abc")) "abc";
    t_string "pretty4" (pretty (Plus (Num 1, Num 5))) "1 + 5";
    t_string "pretty5" (pretty (Plus (Num 5, Num 1))) "5 + 1";
    t_string "pretty6" (pretty (Plus (Num 5, Plus (Num 8, Num 55)))) "5 + 8 + 55";
    t_string "pretty7" (pretty (Plus (Plus (Num 8, Num 55), Num 5))) "8 + 55 + 5";
    t_string "pretty8"
      (pretty (Plus (Plus (Num 8, Num 55), Plus (Num 12, Num ~-2))))
      "8 + 55 + 12 + -2";
    t_string "pretty9" (pretty (Plus (Num 5, Times (Num 4, Num 9)))) "5 + 4 * 9";
    t_string "pretty10" (pretty (Plus (Times (Num 4, Num 9), Num 5))) "4 * 9 + 5";
    t_string "pretty11"
      (pretty (Plus (Times (Num ~-9, Num 9), Times (Num 12, Num 54))))
      "-9 * 9 + 12 * 54";
    t_string "pretty12"
      (pretty (Plus (Times (Num ~-9, Num 9), Plus (Num 12, Num 54))))
      "-9 * 9 + 12 + 54";
    t_string "pretty13"
      (pretty (Plus (Plus (Num 12, Num 54), Times (Num ~-9, Num 9))))
      "12 + 54 + -9 * 9";
    t_string "pretty14" (pretty (Times (Num 1, Num 5))) "1 * 5";
    t_string "pretty15" (pretty (Times (Num 5, Num 1))) "5 * 1";
    t_string "pretty16" (pretty (Times (Num 5, Plus (Num 8, Num 55)))) "5 * (8 + 55)";
    t_string "pretty17" (pretty (Times (Plus (Num 8, Num 55), Num 5))) "(8 + 55) * 5";
    t_string "pretty18"
      (pretty (Times (Plus (Num 8, Num 55), Plus (Num 12, Num ~-2))))
      "(8 + 55) * (12 + -2)";
    t_string "pretty19" (pretty (Times (Num 5, Times (Num 4, Num 9)))) "5 * 4 * 9";
    t_string "pretty20" (pretty (Times (Times (Num 4, Num 9), Num 5))) "4 * 9 * 5";
    t_string "pretty21"
      (pretty (Times (Times (Num ~-9, Num 9), Times (Num 12, Num 54))))
      "-9 * 9 * 12 * 54";
    t_string "pretty22"
      (pretty (Times (Times (Num ~-9, Num 9), Plus (Num 12, Num 54))))
      "-9 * 9 * (12 + 54)";
    t_string "pretty23"
      (pretty (Times (Plus (Num 12, Num 54), Times (Num ~-9, Num 9))))
      "(12 + 54) * -9 * 9";
    t_string "pretty23" (pretty (Plus (Num 4, Variable "a"))) "4 + a";
    t_string "pretty23" (pretty (Plus (Variable "a", Num 4))) "a + 4";
    t_string "pretty23" (pretty (Plus (Variable "a", Plus (Num 2, Variable "b")))) "a + 2 + b";
    t_string "pretty23" (pretty (Plus (Plus (Num 2, Variable "b"), Variable "a"))) "2 + b + a";
    t_string "pretty23" (pretty (Plus (Times (Num 2, Variable "b"), Variable "a"))) "(2)b + a";
    t_string "pretty23" (pretty (Times (Num 2, Variable "b"))) "(2)b";
    t_string "pretty23" (pretty (Times (Variable "b", Num 2))) "b(2)";
    t_string "pretty23" (pretty (Times (Plus (Num 4, Num 5), Num 8))) "(4 + 5) * 8";
    t_string "pretty23"
      (pretty (Times (Plus (Num 4, Times (Plus (Num 12, Variable "c"), Num 8)), Variable "b")))
      "(4 + (12 + c) * 8)b";
    t_string "pretty23"
      (pretty (Times (Times (Plus (Num 4, Plus (Num 12, Variable "c")), Num 8), Variable "b")))
      "((4 + 12 + c) * 8)b" ]
;;

let all_arith_tests = get_tests @ contains_tests @ evaluate_tests @ pretty_tests
(* More tests here *)

let arith_suite = "arithmetic_evaluation" >::: all_arith_tests;;

run_test_tt_main arith_suite

let all_sexp_tests = [ (* More tests here *) ]

let sexp_suite = "sexp_parsing" >::: all_sexp_tests;;

run_test_tt_main sexp_suite
