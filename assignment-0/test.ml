open OUnit2
open Functions

(* This file contains some example tests.  Feel free to delete and reorganize
the unnecessary parts of this file; it is provided to match up with the given
writeup initially. *)

let check_fun _ = (* a function of one argument containing a successful test *)
  assert_equal (2 + 2) 4;;

let check_fun2 _ = (* a failing test *)
  assert_equal (2 + 2) 5;;

(* a helper for testing integers *)
let t_int name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:string_of_int);;

(* Feel free to add any new testing functions you may need *)


let my_first_test = "my_first_test">::check_fun;;
let my_second_test = "my_second_test">::check_fun2;;
let my_third_test = t_int "my_third_test" (2 + 2) 7;;
let my_fourth_test = t_int "my_fourth_test" (2 + 2) 4;;

let suite = "suite">:::[
  my_first_test;
  (* my_second_test; *)
  (* my_third_test; *)
  (* my_fourth_test; *)
  (* add more tests here *)
  ];;

run_test_tt_main suite
