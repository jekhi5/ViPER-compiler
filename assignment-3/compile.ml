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

(* Convenience function to raise a Binding error of a given identifier and position. 
 * `desc` is the description of the error and should lead into the id.
 * E.g. "bad id" "x" <pos> -> "Binding Error: bad id `x` at <pos>"
 *)
let raise_BE (desc : string) (id : string) (p : Lexing.position * Lexing.position) =
  raise (BindingError ("Binding Error: " ^ desc ^ " `" ^ id ^ "` at " ^ string_of_pos p))
;;

let check_scope (e : (Lexing.position * Lexing.position) expr) : unit =
  (* Helper to keep track of  bound identifiers.*)
  let rec check_scope_env (e : (Lexing.position * Lexing.position) expr) (env : string list) : unit
      =
    match e with
    (* For each non-binding id, ensure it is in the environment already.*)
    | EId (id, p) ->
        if List.mem id env then
          ()
        else
          raise_BE "unbound identifier" id p
    | ELet (bindings, body, _) ->
        (* Our accumulator stores two environments:
         * 1) The bindings in this particular let
         * 2) The global environment.
         * For each binding, make sure the id is not in the local env.
         * Make sure the bound expression is OK.
         * Then, add the id to both envs.
         *)
        let _, let_env =
          List.fold_left
            (fun (local_env, global_env) (id, exp, p) ->
              if List.mem id env then
                raise_BE "duplicate `let` binding in" id p
              else
                ignore (check_scope_env exp global_env);
              (id :: local_env, id :: global_env) )
            ([], env) bindings
        in
        check_scope_env body let_env
    (* The rest of the cases are uninteresting. *)
    | ENumber _ -> ()
    | EPrim1 (_, child, _) -> check_scope_env child env
    | EPrim2 (_, child1, child2, _) -> check_scope_env child1 env; check_scope_env child2 env
    | EIf (c, t, f, _) -> check_scope_env c env; check_scope_env t env; check_scope_env f env
  in
  check_scope_env e []
;;

type tag = int

(* PROBLEM 2 *)
(* This function assigns a unique tag to every subexpression and let binding *)
let tag (e : 'a expr) : tag expr =
  (* Helper for tagging a list of bindings. *)
  (* TODO: Scrutinize this with tests... not not sure if foldl or foldr. *)
  let rec tag_bindings (lst : 'a bind list) (start_tag : tag) : tag bind list * tag =
    List.fold_left
      (fun (tagged, next_tag) (id, bound, _) ->
        let tagged_bound, next_tag = help bound next_tag in
        ((id, tagged_bound, next_tag) :: tagged, next_tag + 1) )
      ([], start_tag) lst
  and help (e : 'a expr) (cur : tag) : tag expr * tag =
    match e with
    | EId (id, _) -> (EId (id, cur), cur + 1)
    | ENumber (n, _) -> (ENumber (n, cur), cur + 1)
    | EPrim1 (op, e, _) ->
        let tag_e, next_tag = help e (cur + 1) in
        (EPrim1 (op, tag_e, cur), next_tag)
    | EPrim2 (op, e1, e2, _) ->
        (* Tag starting with the the leftmost innermost. *)
        let tag_e1, next_tag = help e1 (cur + 1) in
        let tag_e2, next_tag = help e2 next_tag in
        (EPrim2 (op, tag_e1, tag_e2, cur), next_tag)
    | EIf (c, t, f, _) ->
        (* Tag the condition, then the true case, then the false case. *)
        let tag_c, next_tag = help c (cur + 1) in
        let tag_t, next_tag = help t next_tag in
        let tag_f, next_tag = help f next_tag in
        (EIf (tag_c, tag_t, tag_f, cur), next_tag)
    | ELet (bindings, body, _) ->
        let tagged_bindings, next_tag = tag_bindings bindings (cur + 1) in
        let tagged_body, next_tag = help body next_tag in
        (ELet (tagged_bindings, tagged_body, cur), next_tag)
  in
  let tagged, _ = help e 1 in
  tagged
;;

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
  let rec rename_bindings (env : (string * string) list) (bindings : tag bind list) :
      (string * string) list * tag bind list =
    List.fold_left
      (fun (env, renamed_bindings) (id, bound, tag) ->
        let renamed_bound = help env bound in
        (* rename e consistently *)
        let renamed_id = sprintf "%s#%d" id tag in
        (* create new unique name for x *)
        let renamed_binding = (renamed_id, renamed_bound, tag) in
        ((id, renamed_id) :: env, renamed_binding :: renamed_bindings) )
      (env, []) bindings
  and help (env : (string * string) list) (e : tag expr) =
    match e with
    | EId (x, tag) ->
        (* Lookup x in the environment and replace it with the environment's renamed version.
         * Since we only call `rename` *after* scope checking, x is guaranteed to be in env.
         *)
        EId (List.assoc x env, tag)
    | ELet (bindings, body, tag) ->
        (* "Extend env by renaming each binding in binds, then rename the expressions and body" *)
        let new_env, renamed_bindings = rename_bindings env bindings in
        let renamed_body = help new_env body in
        ELet (renamed_bindings, renamed_body, tag)
    (* Less interesting cases... *)
    | ENumber (a, t) -> ENumber (a, t)
    | EPrim1 (op, a, t) -> EPrim1 (op, help env a, t)
    | EPrim2 (op, a, b, t) -> EPrim2 (op, help env a, help env b, t)
    | EIf (c, t, f, ta) -> EIf (help env c, help env t, help env f, ta)
  in
  help [] e
;;

(* PROBLEM 4 & 5 *)
(* This function converts a tagged expression into an untagged expression in A-normal form *)
(* Renaming convention: <id> <tag> => "<id>#<tag>" *)
let rec anf (e : tag expr) : unit expr =
  let rec anf_help (e : tag expr) : unit expr * (string * unit expr) list =
    match e with
    | ENumber (n, _) -> (ENumber (n, ()), [])
    | EId (x, _) -> (EId (x, ()), [])
    | EPrim1 (op, body, tag) ->
        let body_ans, body_context = anf_help body in
        let temp = sprintf "%s#%d" (string_of_op1 op) tag in
        (EId (temp, ()), body_context @ [(temp, EPrim1 (op, body_ans, ()))])
    | EPrim2 (op, left, right, tag) ->
        let left_ans, left_context = anf_help left in
        let right_ans, right_context = anf_help right in
        let temp = sprintf "%s#%d" (string_of_op2 op) tag in
        ( EId (temp, ()),
          left_context @ right_context @ [(temp, EPrim2 (op, left_ans, right_ans, ()))] )
    | ELet (bindings, body, _) ->
        let anf_bindings = List.map (fun (id, bound, _) -> (id, anf bound, ())) bindings in
        let anf_body = anf body in
        (ELet (anf_bindings, anf_body, ()), [])
    | EIf (c, t, f, tag) ->
        let c_ans, c_context = anf_help c in
        let anf_t = anf t in
        let anf_f = anf f in
        let temp = sprintf "if#%d" tag in
        (EId (temp, ()), c_context @ [(temp, EIf (c_ans, anf_t, anf_f, ()))])
  in
  let incorporate_context (e : unit expr * (string * unit expr) list) : unit expr =
    match e with
    | ENumber (number, _), _ -> ENumber (number, ())
    | EId (name, _), [] -> EId (name, ())
    | EId (name, _), context ->
        ELet (List.map (fun (id, bound) -> (id, bound, ())) context, EId (name, ()), ())
    | ELet (bindings, body, _), _ -> ELet (bindings, body, ())
    | _ -> failwith ("ICE: Given expression failed to become ANF: " ^ string_of_expr (fst e))
  in
  incorporate_context (anf_help e)
;;

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
  | ISub (dest, to_add) -> sprintf "  sub %s, %s" (arg_to_asm dest) (arg_to_asm to_add)
  | IMul (dest, to_add) -> sprintf "  imul %s, %s" (arg_to_asm dest) (arg_to_asm to_add)
  | ILabel s -> s ^ ":"
  | ICmp (l, r) -> sprintf "  cmp %s, %s" (arg_to_asm l) (arg_to_asm r)
  | IJne s -> "  jne " ^ s
  | IJe s -> "  je " ^ s
  | IJmp s -> "  jmp " ^ s
  | IComment s -> "; " ^ s
  | IRet -> "  ret"
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
  | EPrim2 (op, left, right, _) -> (
      let left_reg = compile_imm left env in
      let right_reg = compile_imm right env in
      match op with
      | Plus -> [IMov (Reg RAX, left_reg); IAdd (Reg RAX, right_reg)]
      | Times -> [IMov (Reg RAX, left_reg); IMul (Reg RAX, right_reg)]
      | Minus -> [IMov (Reg RAX, left_reg); ISub (Reg RAX, right_reg)] )
  | EIf (cond, thn, els, tag) ->
      let else_label = sprintf "if_false#%d" tag in
      let done_label = sprintf "done#%d" tag in
      let cond_reg = compile_imm cond env in
      [ IComment (sprintf "Begin conditional %d" tag);
        IComment "  condition:";
        (* We don't call compile_expr on the cond because it is immediate... *)
        IMov (Reg RAX, cond_reg);
        ICmp (Reg RAX, Const 0L);
        IJe else_label;
        IComment "  if true:" ]
      (* We DO use compile_expr for thn and else, because they are not immediate, but are in ANF. *)
      @ compile_expr thn si env
      @ [IJmp done_label; IComment "  if false:"; ILabel else_label]
      @ compile_expr els si env
      @ [ILabel done_label; IComment (sprintf "End conditional %d" tag)]
  | ELet (bindings, body, _) ->
      (* Implement the fold that Ben discussed in class. *)
      let binding_instrs, next_si, new_env =
        List.fold_right
          (fun (id, bound, _) (instrs, si, env) ->
            ( compile_expr bound si env @ [IMov (RegOffset (si, RSP), Reg RAX)] @ instrs,
              si + 1,
              (id, si) :: env ) )
          bindings ([], si, env)
      in
      binding_instrs
      @ (compile_expr body next_si new_env)

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
