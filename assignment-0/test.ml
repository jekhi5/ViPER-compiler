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

let t_string name value expected = name>::
    (fun _ -> assert_equal expected value ~printer:(fun str -> str));;

(* Feel free to add any new testing functions you may need *)


let my_first_test = "my_first_test">::check_fun;;
let my_second_test = "my_second_test">::check_fun2;;
let my_third_test = t_int "my_third_test" (2 + 2) 7;;
let my_fourth_test = t_int "my_fourth_test" (2 + 2) 4;;

let max_test_1 = t_int "max_test_1" (max 5 4) 5;;
let max_test_2 = t_int "max_test_2" (max ~-4 2) 2;;
let max_test_3 = t_int "max_test_3" (max ~-12 ~-4) ~-4;;
let max_test_4 = t_int "max_test_4" (max 5 5) 5;;

let fib_test_1 = t_int "fib_test_1" (fibonacci 1) 1;;
let fib_test_2 = t_int "fib_test_2" (fibonacci 2) 1;;
let fib_test_3 = t_int "fib_test_3" (fibonacci 10) 55;;

let a = Node("a", Leaf, Leaf);;
let hi_left = Node("i", Node("h", Leaf, Leaf), Leaf);;
let hi_right = Node("h", Leaf, Node("i", Leaf, Leaf));;
let character = 
  Node("r", 
    Node("h", 
      Node("c", Leaf, Leaf), 
      Node("a", Leaf, Leaf)), 
    Node("c", 
      Node("a", Leaf, Leaf), 
      Node("e", 
        Node("t", Leaf, Leaf), 
        Node("r", Leaf, Leaf))));;

let inorder_test_1 = t_string "inorder_test_1" (inorder_str Leaf) "";;
let inorder_test_2 = t_string "inorder_test_2" (inorder_str a) "a";;
let inorder_test_3 = t_string "inorder_test_3" (inorder_str hi_left) "hi";;
let inorder_test_4 = t_string "inorder_test_4" (inorder_str hi_right) "hi";;
let inorder_test_5 = t_string "inorder_test_5" (inorder_str character) "character";;

let size_test_1 = t_int "size_test_1" (size Leaf) 0;;
let size_test_2 = t_int "size_test_2" (size a) 1;;
let size_test_3 = t_int "size_test_3" (size hi_left) 2;;
let size_test_4 = t_int "size_test_4" (size hi_right) 2;;
let size_test_5 = t_int "size_test_5" (size character) 9;;

let long_left = Node("", Node("", Node("", Node("", Leaf, Leaf), Leaf), Leaf), Node("", Leaf, Leaf)) (* The left has height 4, right side only has height 2*)
let long_right = Node("", Node("", Leaf, Leaf), Node("", Node("", Node("", Leaf, Leaf), Leaf), Leaf)) (* inverse of above *)

let height_test_1 = t_int "height_test_1" (height Leaf) 0;;
let height_test_2 = t_int "height_test_2" (height a) 1;;
let height_test_3 = t_int "height_test_3" (height long_left) 4;;
let height_test_4 = t_int "height_test_4" (height long_right) 4;;
let height_test_5 = t_int "height_test_5" (height character) 4;;

let suite = "suite">:::[
  my_first_test;
  (* my_second_test; *)
  (* my_third_test; *)
  my_fourth_test;
  max_test_1;
  max_test_2;
  max_test_3;
  max_test_4;
  fib_test_1;
  fib_test_2;
  fib_test_3;
  inorder_test_1;
  inorder_test_2;
  inorder_test_3;
  inorder_test_4;
  inorder_test_5;
  size_test_1;
  size_test_2;
  size_test_3;
  size_test_4;
  size_test_5;
  height_test_1;
  height_test_2;
  height_test_3;
  height_test_4;
  height_test_5;
  ];;

run_test_tt_main suite
