open Printf
(* Fill in the functions you need to write here *)

(* 1. *)

(* Get the nth fibonacci number *)
let rec fibonacci (n : int) =
  if n == 1 || n == 2 then
    1
  else
    fibonacci (n - 1) + fibonacci (n - 2)
;;

(* 
 * (fibonacci 3)

 * => if 3 == 1 || 3 == 2 then 1 else (fibonacci (3 - 1)) + (fibonacci (3 - 2))
 * => if false || 3 == 2 then 1 else (fibonacci (3 - 1)) + (fibonacci (3 - 2))
 * => if false || false then 1 else (fibonacci (3 - 1)) + (fibonacci (3 - 2))
 * => if false then 1 else (fibonacci (3 - 1)) + (fibonacci (3 - 2))
 * => (fibonacci (3 - 1)) + (fibonacci (3 - 2))
 * => (fibonacci 2) + (fibonacci (3 - 2))
 * => (if 2 == 1 || 2 == 2 then 1 else (fibonacci (2 - 1)) + (fibonacci (2 - 2))) + (fibonacci (3 - 2))
 * => (if false || 2 == 2 then 1 else (fibonacci (2 - 1)) + (fibonacci (2 - 2))) + (fibonacci (3 - 2))
 * => (if false || true then 1 else (fibonacci (2 - 1)) + (fibonacci (2 - 2))) + (fibonacci (3 - 2))
 * => (if true then 1 else (fibonacci (2 - 1)) + (fibonacci (2 - 2))) + (fibonacci (3 - 2))
 * => 1 + (fibonacci (3 - 2))
 * => 1 + (fibonacci 1)
 * => 1 + (if 1 == 1 || 1 == 2 then 1 else (fibonacci (1 - 1)) + (fibonacci (1 - 2)))
 * => 1 + (if true || 1 == 2 then 1 else (fibonacci (1 - 1)) + (fibonacci (1 - 2)))
 * => 1 + (if true then 1 else (fibonacci (1 - 1)) + (fibonacci (1 - 2)))
 * => 1 + 1
 * => 2
 *)

(* 3. *)

(* This type definition and the `inorder_str` def is from the assignment instructions *)
type btnode =
  | Leaf
  | Node of string * btnode * btnode

(*
 * Get the concatenated string of the values stored in the nodes, 
 * printed in order from left to right
 *)
let rec inorder_str (bt : btnode) : string =
  match bt with
  | Leaf -> ""
  | Node (s, left, right) -> inorder_str left ^ s ^ inorder_str right
;;

(*
 * "car"
 * (inorder_str Node("a", Node("c", Leaf, Leaf), Node("r", Leaf, Leaf)))
 *
 * => match Node("a", Node("c", Leaf, Leaf), Node("r", Leaf, Leaf)) with
 *      | Leaf -> ""
 *      | Node(s, left, right) -> 
 *        (inorder_str left) ^ s ^ (inorder_str right)
 *
 * => match Node("a", Node("c", Leaf, Leaf), Node("r", Leaf, Leaf)) with
 *      | Leaf -> ""
 *      | Node("a", Node("c", Leaf, Leaf), Node("r", Leaf, Leaf)) -> 
 *        (inorder_str left) ^ s ^ (inorder_str right)
 * 
 * => match Node("a", Node("c", Leaf, Leaf), Node("r", Leaf, Leaf)) with
 *      | Leaf -> ""
 *      | Node("a", Node("c", Leaf, Leaf), Node("r", Leaf, Leaf)) -> 
 *        (inorder_str Node("c", Leaf, Leaf)) ^ "a" ^ (inorder_str Node("r", Leaf, Leaf))
 * 
 * => (inorder_str Node("c", Leaf, Leaf)) ^ "a" ^ (inorder_str Node("r", Leaf, Leaf))
 *
 * => (match Node("c", Leaf, Leaf) with
 *      | Leaf -> ""
 *      | Node(s, left, right) -> 
 *        (inorder_str left) ^ s ^ (inorder_str right)) ^ "a" ^ (inorder_str Node("r", Leaf, Leaf))
 *
 * => (match Node("c", Leaf, Leaf) with
 *      | Leaf -> ""
 *      | Node("c", Leaf, Leaf) -> 
 *        (inorder_str left) ^ s ^ (inorder_str right)) ^ "a" ^ (inorder_str Node("r", Leaf, Leaf))
 *
 * => (match Node("c", Leaf, Leaf) with
 *      | Leaf -> ""
 *      | Node("c", Leaf, Leaf) -> 
 *        (inorder_str Leaf) ^ "c" ^ (inorder_str Leaf)) ^ "a" ^ (inorder_str Node("r", Leaf, Leaf))
 *
 * => ((inorder_str Leaf) ^ "c" ^ (inorder_str Leaf)) ^ "a" ^ (inorder_str Node("r", Leaf, Leaf))
 *
 * => ((match Leaf with
 *      | Leaf -> ""
 *      | Node(s, left, right) -> 
 *        (inorder_str left) ^ s ^ (inorder_str right)) ^ "c" ^ (inorder_str Leaf)) ^ "a" ^ (inorder_str Node("r", Leaf, Leaf))
 *
 * => ("" ^ "c" ^ (inorder_str Leaf)) ^ "a" ^ (inorder_str Node("r", Leaf, Leaf))
 *
 * => ("" ^ "c" ^ (match Leaf with
 *      | Leaf -> ""
 *      | Node(s, left, right) -> 
 *        (inorder_str left) ^ s ^ (inorder_str right))) ^ "a" ^ (inorder_str Node("r", Leaf, Leaf))
 *
 * => ("" ^ "c" ^ "") ^ "a" ^ (inorder_str Node("r", Leaf, Leaf))
 *
 * => ("" ^ "c" ^ "") ^ "a" ^ (match Node("r", Leaf, Leaf) with
 *                               | Leaf -> ""
 *                               | Node(s, left, right) -> 
 *                                 (inorder_str left) ^ s ^ (inorder_str right))
 *
 * => ("" ^ "c" ^ "") ^ "a" ^ (match Node("r", Leaf, Leaf) with
 *                               | Leaf -> ""
 *                               | Node("r", Leaf, Leaf) -> 
 *                                 (inorder_str left) ^ s ^ (inorder_str right))
 *
 * => ("" ^ "c" ^ "") ^ "a" ^ (match Node("r", Leaf, Leaf) with
 *                               | Leaf -> ""
 *                               | Node("r", Leaf, Leaf) -> 
 *                                 (inorder_str Leaf) ^ "r" ^ (inorder_str Leaf))
 *
 * => ("" ^ "c" ^ "") ^ "a" ^ ((inorder_str Leaf) ^ "r" ^ (inorder_str Leaf))
 *
 * => ("" ^ "c" ^ "") ^ "a" ^ ((match Leaf with
 *                               | Leaf -> ""
 *                               | Node(s, left, right) -> 
 *                                 (inorder_str left) ^ s ^ (inorder_str right)) ^ "r" ^ (inorder_str Leaf))
 *
 * => ("" ^ "c" ^ "") ^ "a" ^ ("" ^ "r" ^ (inorder_str Leaf))
 *
 * => ("" ^ "c" ^ "") ^ "a" ^ ("" ^ "r" ^ (match Leaf with
 *                                            | Leaf -> ""
 *                                            | Node(s, left, right) -> 
 *                                              (inorder_str left) ^ s ^ (inorder_str right)))
 *
 * => ("" ^ "c" ^ "") ^ "a" ^ ("" ^ "r" ^ "")
 *
 * => "" ^ "c" ^ "" ^ "a" ^ "" ^ "r" ^ ""
 *
 * => "car"                      
 *)

(* Get the size of a given tree *)
let rec size (bt : btnode) : int =
  match bt with
  | Leaf -> 0
  | Node (s, left, right) -> 1 + size left + size right
;;

(* Get the height of a given tree *)
let rec height (bt : btnode) : int =
  match bt with
  | Leaf -> 0
  | Node (s, left, right) -> 1 + max (height left) (height right)
;;

(* 4. *)

(* Increment all values in the list by 1 *)
let rec increment_all (lst : int list) : int list =
  match lst with
  | [] -> []
  | first :: rest -> (first + 1) :: increment_all rest
;;

(*
 * Filter strings in the list so that only those with a length longer than 
 * the provided target remain
 *)
let rec long_strings (lst : string list) (target_length : int) : string list =
  match lst with
  | [] -> []
  | first :: rest ->
      if String.length first > target_length then
        first :: long_strings rest target_length
      else
        long_strings rest target_length
;;

(* Filter a generic list so that only the elements at odd indices remain *)
let rec every_other (lst : 'a list) =
  match lst with
  | [] -> []
  | first :: rest ->
      (* Keep the first item *)
      first
      ::
      ( match rest with
      (*
       * If the next item is just the empty list, then concat it
       * otherwise, skip over it to ensure only every other element is in the final list
       *)
      | [] -> []
      | next :: rest_rest -> every_other rest_rest )
;;

(* `sum` was taken from the assignment page where it was named `sum2`*)
(* Get the sum of an integer based list*)
let rec sum (l : int list) : int =
  match l with
  | [] -> 0
  | first :: rest -> first + sum rest
;;

(* Get the sum of all sub-lists *)
let rec sum_all (lst : int list list) =
  match lst with
  | [] -> []
  | first :: rest -> sum first :: sum_all rest
;;
