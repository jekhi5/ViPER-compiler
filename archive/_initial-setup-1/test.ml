open OUnit2
open Functions

(* This file contains some example tests.  Feel free to delete and reorganize
   the unnecessary parts of this file; it is provided to match up with the given
   writeup initially. *)

let check_fun _ =
  (* a function of one argument containing a successful test *)
  assert_equal (2 + 2) 4
;;

let check_fun2 _ =
  (* a failing test *)
  assert_equal (2 + 2) 5
;;

(* a helper for testing integers *)
let t_int name value expected = name >:: fun _ -> assert_equal expected value ~printer:string_of_int

let t_string name value expected =
  name >:: fun _ -> assert_equal expected value ~printer:(fun str -> str)
;;

let t_int_list name value expected =
  name
  >:: fun _ ->
  assert_equal expected value ~printer:(fun (lst : int list) ->
      "[" ^ String.concat "; " (List.map string_of_int lst) ^ "]" )
;;

let t_string_list name value expected =
  name
  >:: fun _ ->
  assert_equal expected value ~printer:(fun (lst : string list) ->
      "[" ^ String.concat "; " lst ^ "]" )
;;

let t_int_list_list name value expected = name >:: fun _ -> assert_equal expected value

(* Feel free to add any new testing functions you may need *)

let my_first_test = "my_first_test" >:: check_fun

let my_second_test = "my_second_test" >:: check_fun2

let my_third_test = t_int "my_third_test" (2 + 2) 7

let my_fourth_test = t_int "my_fourth_test" (2 + 2) 4

let max_test_1 = t_int "max_test_1" (max 5 4) 5

let max_test_2 = t_int "max_test_2" (max ~-4 2) 2

let max_test_3 = t_int "max_test_3" (max ~-12 ~-4) ~-4

let max_test_4 = t_int "max_test_4" (max 5 5) 5

let fib_test_1 = t_int "fib_test_1" (fibonacci 1) 1

let fib_test_2 = t_int "fib_test_2" (fibonacci 2) 1

let fib_test_3 = t_int "fib_test_3" (fibonacci 10) 55

let a = Node ("a", Leaf, Leaf)

let hi_left = Node ("i", Node ("h", Leaf, Leaf), Leaf)

let hi_right = Node ("h", Leaf, Node ("i", Leaf, Leaf))

let character =
  Node
    ( "r",
      Node ("h", Node ("c", Leaf, Leaf), Node ("a", Leaf, Leaf)),
      Node ("c", Node ("a", Leaf, Leaf), Node ("e", Node ("t", Leaf, Leaf), Node ("r", Leaf, Leaf)))
    )
;;

let inorder_test_1 = t_string "inorder_test_1" (inorder_str Leaf) ""

let inorder_test_2 = t_string "inorder_test_2" (inorder_str a) "a"

let inorder_test_3 = t_string "inorder_test_3" (inorder_str hi_left) "hi"

let inorder_test_4 = t_string "inorder_test_4" (inorder_str hi_right) "hi"

let inorder_test_5 = t_string "inorder_test_5" (inorder_str character) "character"

let size_test_1 = t_int "size_test_1" (size Leaf) 0

let size_test_2 = t_int "size_test_2" (size a) 1

let size_test_3 = t_int "size_test_3" (size hi_left) 2

let size_test_4 = t_int "size_test_4" (size hi_right) 2

let size_test_5 = t_int "size_test_5" (size character) 9

(* The left has height 4, right side only has height 2 *)
let long_left =
  Node ("", Node ("", Node ("", Node ("", Leaf, Leaf), Leaf), Leaf), Node ("", Leaf, Leaf))
;;

(* inverse of above *)
let long_right =
  Node ("", Node ("", Leaf, Leaf), Node ("", Node ("", Node ("", Leaf, Leaf), Leaf), Leaf))
;;

let height_test_1 = t_int "height_test_1" (height Leaf) 0

let height_test_2 = t_int "height_test_2" (height a) 1

let height_test_3 = t_int "height_test_3" (height long_left) 4

let height_test_4 = t_int "height_test_4" (height long_right) 4

let height_test_5 = t_int "height_test_5" (height character) 4

let empty = []

let single_int = [1]

let positive_only = [1; 2; 3]

let negative_only = [~-6; ~-3; ~-12]

let mixed_sign = [4; ~-32; ~-5; ~-1; 6]

let increment_all_test_1 = t_int_list "increment_all_test_1" (increment_all empty) []

let increment_all_test_2 = t_int_list "increment_all_test_2" (increment_all single_int) [2]

let increment_all_test_3 = t_int_list "increment_all_test_3" (increment_all positive_only) [2; 3; 4]

let increment_all_test_4 =
  t_int_list "increment_all_test_4" (increment_all negative_only) [~-5; ~-2; ~-11]
;;

let increment_all_test_5 =
  t_int_list "increment_all_test_5" (increment_all mixed_sign) [5; ~-31; ~-4; 0; 7]
;;

let empty_string = [""]

let single_str = ["hello"]

let many_str = ["hello"; "Charlie/Zack"; "how"; "is"; "grading"; "going"]

let long_strings_test_1 = t_string_list "long_string_test_1" (long_strings empty 0) []

let long_strings_test_2 = t_string_list "long_string_test_2" (long_strings empty 5000) []

let long_strings_test_3 = t_string_list "long_string_test_3" (long_strings empty_string 0) []

let long_strings_test_4 = t_string_list "long_string_test_4" (long_strings empty_string ~-1) [""]

let long_strings_test_5 = t_string_list "long_string_test_5" (long_strings single_str 4) ["hello"]

let long_strings_test_6 = t_string_list "long_string_test_6" (long_strings single_str 5) []

let long_strings_test_7 = t_string_list "long_string_test_7" (long_strings single_str 18) []

let long_strings_test_8 =
  t_string_list "long_string_test_8" (long_strings many_str 5) ["Charlie/Zack"; "grading"]
;;

let long_strings_test_9 =
  t_string_list "long_string_test_9" (long_strings many_str ~-1)
    ["hello"; "Charlie/Zack"; "how"; "is"; "grading"; "going"]
;;

let every_other_test_1 = t_int_list "every_other_test_1" (every_other empty) []

(* Odd initial list *)
let every_other_test_2 = t_int_list "every_other_test_2" (every_other single_int) [1]

(* Odd initial list *)
let every_other_test_3 = t_string_list "every_other_test_3" (every_other single_str) ["hello"]

(* Odd initial list *)
let every_other_test_4 = t_int_list "every_other_test_4" (every_other mixed_sign) [4; ~-5; 6]

(* Even initial list *)
let every_other_test_5 =
  t_string_list "every_other_test_5" (every_other many_str) ["hello"; "how"; "grading"]
;;

let all_empty_sub_lists = [[]; []; []]

let all_single_sub_lists = [[1]; [2]; [5]]

let mixed_size_sub_lists = [[1; 2; 3]; [4; ~-3]; []; [~-14]]

let sum_all_test_1 = t_int_list_list "sum_all_test_1" (sum_all empty) []

let sum_all_test_2 = t_int_list_list "sum_all_test_2" (sum_all all_empty_sub_lists) [0; 0; 0]

let sum_all_test_3 = t_int_list_list "sum_all_test_3" (sum_all all_single_sub_lists) [1; 2; 5]

let sum_all_test_4 = t_int_list_list "sum_all_test_4" (sum_all mixed_size_sub_lists) [6; 1; 0; ~-14]

let suite =
  "suite"
  >::: [ my_first_test;
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
         increment_all_test_1;
         increment_all_test_2;
         increment_all_test_3;
         increment_all_test_4;
         increment_all_test_5;
         long_strings_test_1;
         long_strings_test_2;
         long_strings_test_3;
         long_strings_test_4;
         long_strings_test_5;
         long_strings_test_6;
         long_strings_test_7;
         long_strings_test_8;
         long_strings_test_9;
         every_other_test_1;
         every_other_test_2;
         every_other_test_3;
         every_other_test_4;
         every_other_test_5;
         sum_all_test_1;
         sum_all_test_2;
         sum_all_test_3;
         sum_all_test_4 ]
;;

run_test_tt_main suite
