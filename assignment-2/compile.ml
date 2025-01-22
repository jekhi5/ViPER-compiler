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
    | Nest ([binding; bound], _) -> (
      match expr_of_sexp binding with
      | Id (id, _) -> (id, expr_of_sexp bound)
      | _ ->
          raise
            (SyntaxError
               ( "Invalid binding syntax, can only bind to identifiers, at "
               ^ pos_to_string (sexp_info binding) true ) ) )
    | _ -> raise (SyntaxError ("Invalid binding syntax at " ^ pos_to_string (sexp_info b) true))
  in
  match s with
  | Int (n, pos) -> Number (n, pos)
  (* This language has no concept of booleans. If the user wrote this string, it should be parsed as a symbol *)
  | Bool (true, pos) -> Id ("true", pos)
  | Bool (false, pos) -> Id ("false", pos)
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
  (* We do not reserve words like `add1`. 
   * If we see them outside of the usual syntax, we assume they're an identifier *)
  | Sym (id, pos) -> Id (id, pos)
  | _ -> raise (SyntaxError ("Invalid syntax at " ^ pos_to_string (sexp_info s) true))
;;

(* Functions that implement the compiler *)

(* The next four functions convert assembly instructions into strings,
   one datatype at a time.  Only one function has been fully implemented
   for you. *)
let reg_to_asm_string (r : reg) : string =
  match r with
  | RAX -> "RAX"
  | RSP -> "RSP"
;;

let arg_to_asm_string (a : arg) : string =
  match a with
  | Const n -> sprintf "%Ld" n
  | Reg r -> reg_to_asm_string r
  (* It feels kind of weird to allow an offset of other registers, such as RAX. *)
  (* However, this concern would be better addressed in a more structural way, *)
  (* as opposed to in the print function. *)
  | RegOffset (o, r) -> "[" ^ reg_to_asm_string r ^ " - 8*" ^ sprintf "%Ld" (Int64.of_int o) ^ "]"
;;

let instruction_to_asm_string (i : instruction) : string =
  match i with
  | IMov (dest, value) -> sprintf "\tmov %s, %s" (arg_to_asm_string dest) (arg_to_asm_string value)
  | IAdd (reg, value) -> sprintf "\tadd %s, %s" (arg_to_asm_string reg) (arg_to_asm_string value)
  | IRet -> "\tret"
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

(* Are there any duplicates in the list? If there are, returns the duplicate id
 * This is not the most efficient way of writing this function,
 * since the worst case involves looking back over the list a bunch of times.
 *)
let rec duplicate_bindings (ls : (string * pos expr) list) : string option =
  match ls with
  | [] -> None
  | (id, _) :: rest -> (
    match duplicate_bindings rest with
    | Some x -> Some x
    | None -> (
      match find rest id with
      | None -> None
      | Some _ -> Some id ) )
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
  | Prim1 (Add1, e, _) -> compile_env e stack_index env @ [IAdd (Reg RAX, Const 1L)]
  | Prim1 (Sub1, e, _) -> compile_env e stack_index env @ [IAdd (Reg RAX, Const (-1L))]
  | Id (id, pos) -> (
    match find env id with
    | Some n -> [IMov (Reg RAX, RegOffset (n, RSP))]
    | None -> raise (BindingError ("Unbound identifier: `" ^ id ^ "` at " ^ pos_to_string pos true))
    )
  | Let ((id, bound) :: [], body, _) ->
      compile_env bound stack_index env
      @ [IMov (RegOffset (stack_index, RSP), Reg RAX)]
      @ compile_env body (stack_index + 1) ((id, stack_index) :: env)
  | Let (first :: rest, body, pos) -> (
    (* Check for duplicate bindings, since we are reducing this to syntactic sugar. 
     * Our understanding is that `(let ((a 1) (a 2)) 1)` is disallowed,
     * but that `(let ((a 1)) (let ((a 1)) 1))` is allowed.
     * I.e. we can have shadowed IDs, just not inside of the let clauses.
     * Therefore, we compile multiple binding `let`s in two steps:
     * 1) Check for duplicate IDs
     * 2) If OK, rewrite in terms of one-binding `let`s. 
     *)
    match duplicate_bindings (first :: rest) with
    | Some id ->
        raise
          (BindingError ("Duplicate binding: `" ^ id ^ "` within `let` at " ^ pos_to_string pos true)
          )
    | None -> compile_env (Let ([first], Let (rest, body, pos), pos)) stack_index env )
  | Let ([], _, pos) ->
      raise
        (BindingError ("ICE: `let` has no bindings at compile time, at " ^ pos_to_string pos true))
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
