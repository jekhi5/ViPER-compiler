open Printf
open Sexp

(* Abstract syntax of (a small subset of) x86 assembly instructions *)

let word_size = 8

type reg =
  | RAX
  | RSP

type arg =
  | Const of int64
  | Reg of reg
  | RegOffset of int * reg (* int is # words of offset *)

type instruction =
  | IMov of arg * arg
  | IAdd of arg * arg
  | IRet

(* Concrete syntax of the Adder language:

   ‹expr›:
     | NUMBER
     | IDENTIFIER
     | ( let ( ‹bindings› ) ‹expr› )
     | ( add1 ‹expr› )
     | ( sub1 ‹expr› )
   ‹bindings›:
     | ( IDENTIFIER ‹expr› )
     | ( IDENTIFIER ‹expr› ) ‹bindings›
*)

(* Abstract syntax of the Adder language *)

type prim1 =
  | Add1
  | Sub1

type 'a expr =
  | Number of int64 * 'a
  | Id of string * 'a
  | Let of (string * 'a expr) list * 'a expr * 'a
  | Prim1 of prim1 * 'a expr * 'a

(* Function to convert from unknown s-expressions to Adder exprs
   Throws a SyntaxError message if there's a problem
*)
exception SyntaxError of string

let rec expr_of_sexp (s : pos sexp) : pos expr =
  let parse_binding (b : 'a sexp) : string * 'a expr =
    match b with
    | Nest ([Sym (id, _); bound], _) -> (id, expr_of_sexp bound)
    | _ -> raise (SyntaxError ("Invalid binding syntax at " ^ pos_to_string (sexp_info b) true))
  in
  match s with
  | Int (n, pos) -> Number (n, pos)
  (* This language has no concept of booleans. If the user wrote this string, it should be parsed as a symbol*)
  | Bool (true, pos) -> Id ("true", pos)
  | Bool (false, pos) -> Id ("false", pos)
  | Sym ("add1", pos) ->
      raise (SyntaxError ("Invalid syntax on `add1` at " ^ pos_to_string pos false))
  | Sym ("sub1", pos) ->
      raise (SyntaxError ("Invalid syntax on `sub1` at " ^ pos_to_string pos false))
  | Sym ("let", pos) -> raise (SyntaxError ("Invalid syntax on `let` at " ^ pos_to_string pos false))
  | Nest ([Sym ("add1", _); operand], nest_pos) -> Prim1 (Add1, expr_of_sexp operand, nest_pos)
  | Nest ([Sym ("sub1", _); operand], nest_pos) -> Prim1 (Sub1, expr_of_sexp operand, nest_pos)
  | Nest ([Sym ("let", _); Nest (bindings, bindings_pos); let_body], nest_pos) ->
      let binding_exprs = List.map parse_binding bindings in
      if List.is_empty binding_exprs then
        raise
          (SyntaxError
             ( "Invalid syntax: A `let` requires at least one binding at "
             ^ pos_to_string bindings_pos false ) )
      else
        Let (binding_exprs, expr_of_sexp let_body, nest_pos)
  | Sym (id, pos) -> Id (id, pos)
  | _ -> raise (SyntaxError ("Invalid syntax at " ^ pos_to_string (sexp_info s) false))
;;

(* Functions that implement the compiler *)

(* The next four functions convert assembly instructions into strings,
   one datatype at a time.  Only one function has been fully implemented
   for you. *)
let reg_to_asm_string (r : reg) : string =
  (* COMPLETE THIS FUNCTION *)
  failwith "Not yet implemented"
;;

let arg_to_asm_string (a : arg) : string =
  match a with
  | Const n -> sprintf "%Ld" n
  (* COMPLETE THIS FUNCTION *)
  | _ -> failwith "Other args not yet implemented"
;;

let instruction_to_asm_string (i : instruction) : string =
  match i with
  | IMov (dest, value) -> sprintf "\tmov %s, %s" (arg_to_asm_string dest) (arg_to_asm_string value)
  (* COMPLETE THIS FUNCTION *)
  | _ -> failwith "Other instructions not yet implemented"
;;

let to_asm_string (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (instruction_to_asm_string i)) "" is
;;

(* A helper function for looking up a name in a "dictionary" and
   returning the associated value if possible.  This is definitely
   not the most efficient data structure for this, but it is nice and simple... *)
let rec find (ls : (string * 'a) list) (x : string) : 'a option =
  match ls with
  | [] -> None
  | (y, v) :: rest ->
      if y = x then
        Some v
      else
        find rest x
;;

(* The exception to be thrown when some sort of problem is found with names *)
exception BindingError of string

(* The actual compilation process.  The `compile` function is the primary function,
   and uses `compile_env` as its helper.  In a more idiomatic OCaml program, this
   helper would likely be a local definition within `compile`, but separating it out
   makes it easier for you to test it. *)
let rec compile_env
    (p : pos expr) (* the program, currently annotated with source location info *)
    (stack_index : int) (* the next available stack index *)
    (env : (string * int) list) : instruction list =
  (* the current binding environment of names to stack slots *)

  (* the instructions that would execute this program *)
  match p with
  | Number (n, _) -> [IMov (Reg RAX, Const n)]
  | _ -> failwith "Other exprs not yet implemented"
;;

let compile (p : pos expr) : instruction list =
  compile_env p 1 [] (* Start at the first stack slot, with an empty environment *)
;;

(* The entry point for the compiler: a function that takes a expr and
   creates an assembly-program string representing the compiled version *)
let compile_to_string (prog : pos expr) : string =
  let prelude = "\nsection .text\nglobal our_code_starts_here\nour_code_starts_here:" in
  let asm_string = to_asm_string (compile prog @ [IRet]) in
  let asm_program = sprintf "%s%s\n" prelude asm_string in
  asm_program
;;
