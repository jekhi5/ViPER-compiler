open Printf
open Exprs
open Pretty

let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1 (_, e, _) -> is_imm e
  | EPrim2 (_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet (binds, body, _) -> List.for_all (fun (_, e, _) -> is_anf e) binds && is_anf body
  | EIf (cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | _ -> is_imm e

and is_imm e =
  match e with
  | ENumber _ -> true
  | EId _ -> true
  | _ -> false
;;

(* PROBLEM 1 *)
(* This function should encapsulate the binding-error checking from Boa *)
exception BindingError of string

let rec check_scope (e : (Lexing.position * Lexing.position) expr) : unit =
  failwith "check_scope: Implement this"
;;

type tag = int

(* PROBLEM 2 *)
(* This function assigns a unique tag to every subexpression and let binding *)
let tag (e : 'a expr) : tag expr = failwith "tag: Implement this"

(* This function removes all tags, and replaces them with the unit value.
   This might be convenient for testing, when you don't care about the tag info. *)
let rec untag (e : 'a expr) : unit expr =
  match e with
  | EId (x, _) -> EId (x, ())
  | ENumber (n, _) -> ENumber (n, ())
  | EPrim1 (op, e, _) -> EPrim1 (op, untag e, ())
  | EPrim2 (op, e1, e2, _) -> EPrim2 (op, untag e1, untag e2, ())
  | ELet (binds, body, _) ->
      ELet (List.map (fun (x, b, _) -> (x, untag b, ())) binds, untag body, ())
  | EIf (cond, thn, els, _) -> EIf (untag cond, untag thn, untag els, ())
;;

(* PROBLEM 3 *)
let rename (e : tag expr) : tag expr =
  let rec help (env : (string * string) list) (e : tag expr) =
    match e with
    | EId (x, tag) -> EId (failwith "implement this", tag)
    | ELet (binds, body, tag) ->
        failwith
          "Extend env by renaming each binding in binds, then rename the expressions and body"
    | _ -> failwith "finish the other cases recursively"
  in
  help [] e
;;

(* PROBLEM 4 & 5 *)
(* This function converts a tagged expression into an untagged expression in A-normal form *)
let anf (e : tag expr) : unit expr = failwith "anf: Implement this"

(* Helper functions *)
let r_to_asm (r : reg) : string =
  match r with
  | RAX -> "rax"
  | RSP -> "rsp"
;;

let arg_to_asm (a : arg) : string =
  match a with
  | Const n -> sprintf "QWORD %Ld" n
  | Reg r -> r_to_asm r
  | RegOffset (n, r) ->
      if n >= 0 then
        sprintf "[%s+%d]" (r_to_asm r) (word_size * n)
      else
        sprintf "[%s-%d]" (r_to_asm r) (-1 * word_size * n)
;;

let i_to_asm (i : instruction) : string =
  match i with
  | IMov (dest, value) -> sprintf "  mov %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IAdd (dest, to_add) -> sprintf "  add %s, %s" (arg_to_asm dest) (arg_to_asm to_add)
  | IRet -> "  ret"
  | _ -> failwith "i_to_asm: Implement this"
;;

let to_asm (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (i_to_asm i)) "" is
;;

let rec find ls x =
  match ls with
  | [] -> failwith (sprintf "Name %s not found" x)
  | (y, v) :: rest ->
      if y = x then
        v
      else
        find rest x
;;

(* PROBLEM 5 *)
(* This function actually compiles the tagged ANF expression into assembly *)
(* The si parameter should be used to indicate the next available stack index for use by Lets *)
(* The env parameter associates identifier names to stack indices *)
let rec compile_expr (e : tag expr) (si : int) (env : (string * int) list) : instruction list =
  match e with
  | ENumber _ -> [IMov (Reg RAX, compile_imm e env)]
  | EId _ -> [IMov (Reg RAX, compile_imm e env)]
  | EPrim1 (op, e, _) -> (
      let e_reg = compile_imm e env in
      match op with
      | Add1 -> [IMov (Reg RAX, e_reg); IAdd (Reg RAX, Const 1L)]
      | Sub1 -> [IMov (Reg RAX, e_reg); IAdd (Reg RAX, Const Int64.minus_one)] )
  | EPrim2 (op, left, right, _) -> failwith "compile_expr:eprim2: Implement this"
  | EIf (cond, thn, els, tag) -> failwith "compile_expr:eif: Implement this"
  | ELet ([(id, e, _)], body, _) -> failwith "compile_expr:elet: Implement this"
  | _ -> failwith "Impossible: Not in ANF"

and compile_imm e env =
  match e with
  | ENumber (n, _) -> Const n
  | EId (x, _) -> RegOffset (~-(find env x), RSP)
  | _ -> failwith "Impossible: not an immediate"
;;

let compile_anf_to_string anfed =
  let prelude = "section .text\nglobal our_code_starts_here\nour_code_starts_here:" in
  let compiled = compile_expr anfed 1 [] in
  let as_assembly_string = to_asm (compiled @ [IRet]) in
  sprintf "%s%s\n" prelude as_assembly_string
;;

let compile_to_string prog =
  check_scope prog;
  let tagged : tag expr = tag prog in
  let renamed : tag expr = rename tagged in
  let anfed : tag expr = tag (anf renamed) in
  (* printf "Prog:\n%s\n" (ast_of_expr prog); *)
  (* printf "Tagged:\n%s\n" (format_expr tagged string_of_int); *)
  (* printf "ANFed/tagged:\n%s\n" (format_expr anfed string_of_int); *)
  compile_anf_to_string anfed
;;
