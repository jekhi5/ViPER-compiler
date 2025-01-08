(* Fill in the functions you need to write here *)


(* 1. *)

let rec fibonacci (n: int) =
    if n == 1 || n == 2 then 1 else (fibonacci (n - 1)) + (fibonacci (n - 2))

(* 
 (fibonacci 3)
 
 => if 3 == 1 || 3 == 2 then 1 else (fibonacci (3 - 1)) + (fibonacci (3 - 2))
 => if false then 1 else (fibonacci (3 - 1)) + (fibonacci (3 - 2))
 => (fibonacci 2) + (fibonacci (3 - 2))
 => (if 2 == 1 || 2 == 2 then 1 else (fibonacci (2 - 1)) + (fibonacci (2 - 2))) + (fibonacci (3 - 2))
 => (if true then 1 else (fibonacci (2 - 1)) + (fibonacci (2 - 2))) + (fibonacci (3 - 2))
 => (1) + (fibonacci (3 - 2))
 => 1 + (fibonacci 1)
 => 1 + (if 1 == 1 || 1 == 2 then 1 else (fibonacci (1 - 1)) + (fibonacci (1 - 2)))
 => 1 + (if true then 1 else (fibonacci (1 - 1)) + (fibonacci (1 - 2)))
 => 1 + (1)
 => 2
 *)

(* 3. *)

type btnode =
  | Leaf
  | Node of string * btnode * btnode

let rec inorder_str (bt : btnode) : string =
  match bt with
    | Leaf -> ""
    | Node(s, left, right) ->
      (inorder_str left) ^ s ^ (inorder_str right)
