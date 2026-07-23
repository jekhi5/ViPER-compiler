open Printf
open Errors

(* Generic, domain-free helpers: nothing here should mention a compiler type
   (arg, aexpr, tags, ...). Anything that knows about the language belongs in a
   domain module (constants, env, ...) instead. *)

let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y, v) :: rest ->
      if y = x then
        v
      else
        find rest x
;;

let rec take xs n =
  match (xs, n) with
  | _, 0 -> []
  | [], _ -> []
  | car :: cdr, v -> car :: take cdr (v - 1)
;;

let rec drop xs n =
  match (xs, n) with
  | l, 0 -> l
  | [], _ -> []
  | _ :: cdr, n -> drop cdr (n - 1)
;;
