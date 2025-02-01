open Printf
open Errors
open Exprs
open Pretty
open Phases
open Assembly

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
  | EBool _ -> true
  | EId _ -> true
  | _ -> false
;;

let const_true = HexConst 0xFFFFFFFFFFFFFFFFL

let const_false = HexConst 0x7FFFFFFFFFFFFFFFL

let bool_mask = HexConst 0x8000000000000000L

let bool_tag = 0x0000000000000007L

let bool_tag_mask = 0x0000000000000007L

let num_tag = 0x0000000000000000L

let num_tag_mask = 0x0000000000000001L

let err_COMP_NOT_NUM = 1L

let err_ARITH_NOT_NUM = 2L

let err_LOGIC_NOT_BOOL = 3L

let err_IF_NOT_BOOL = 4L

let err_OVERFLOW = 5L

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

let check_scope (e : sourcespan expr) : sourcespan expr =
  let rec help e env =
    match e with
    | EBool _ -> ()
    | ENumber _ -> ()
    | EId (x, loc) -> (
      try ignore (List.assoc x env)
      with Not_found ->
        raise
          (BindingError
             (sprintf "The identifier %s, used at <%s>, is not in scope" x
                (string_of_sourcespan loc) ) ) )
    | EPrim1 (_, e, _) -> help e env
    | EPrim2 (_, l, r, _) -> help l env; help r env
    | EIf (c, t, f, _) -> help c env; help t env; help f env
    | ELet (binds, body, _) ->
        let env2, _ =
          List.fold_left
            (fun (scope_env, shadow_env) (x, e, loc) ->
              try
                let existing = List.assoc x shadow_env in
                raise
                  (BindingError
                     (sprintf "The identifier %s, defined at <%s>, shadows one defined at <%s>" x
                        (string_of_sourcespan loc) (string_of_sourcespan existing) ) )
              with Not_found ->
                help e scope_env;
                ((x, loc) :: scope_env, (x, loc) :: shadow_env) )
            (env, []) binds
        in
        help body env2
  in
  help e []; e
;;

let rename (e : tag expr) : tag expr =
  raise (NotYetImplemented "Copy this from your Boa implementation")
;;

let tag (e : 'a expr) : tag expr =
  let rec help (e : 'a expr) (num : int) : tag expr * tag =
    match e with
    | EId (x, _) -> (EId (x, num), num + 1)
    | ENumber (n, _) -> (ENumber (n, num), num + 1)
    | EBool (b, _) -> (EBool (b, num), num + 1)
    | EPrim1 (op, e, _) ->
        let tag_e, new_n = help e (num + 1) in
        (EPrim1 (op, tag_e, num), new_n)
    | EPrim2 (op, e1, e2, _) ->
        let tag_e1, num_e1 = help e1 (num + 1) in
        let tag_e2, num_e2 = help e2 num_e1 in
        (EPrim2 (op, tag_e1, tag_e2, num), num_e2)
    | ELet (binds, body, _) ->
        let new_binds, num_binds =
          List.fold_left
            (fun (rev_binds, next_num) (x, b, _) ->
              let tag_b, num_b = help b (next_num + 1) in
              ((x, tag_b, next_num) :: rev_binds, num_b) )
            ([], num + 1)
            binds
        in
        let tag_body, num_body = help body num_binds in
        (ELet (List.rev new_binds, tag_body, num), num_body)
    | EIf (cond, thn, els, _) ->
        let tag_cond, num_cond = help cond (num + 1) in
        let tag_thn, num_thn = help thn num_cond in
        let tag_els, num_els = help els num_thn in
        (EIf (tag_cond, tag_thn, tag_els, num), num_els)
  in
  let ans, _ = help e 1 in
  ans
;;

let rec untag (e : 'a expr) : unit expr =
  match e with
  | EId (x, _) -> EId (x, ())
  | ENumber (n, _) -> ENumber (n, ())
  | EBool (b, _) -> EBool (b, ())
  | EPrim1 (op, e, _) -> EPrim1 (op, untag e, ())
  | EPrim2 (op, e1, e2, _) -> EPrim2 (op, untag e1, untag e2, ())
  | ELet (binds, body, _) ->
      ELet (List.map (fun (x, b, _) -> (x, untag b, ())) binds, untag body, ())
  | EIf (cond, thn, els, _) -> EIf (untag cond, untag thn, untag els, ())
;;

let anf (e : tag expr) : unit expr =
  let rec helpC (e : tag expr) : unit expr * (string * unit expr) list =
    match e with
    | EPrim1 (op, arg, _) ->
        let arg_imm, arg_setup = helpI arg in
        (EPrim1 (op, arg_imm, ()), arg_setup)
    | EPrim2 (op, left, right, _) ->
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (EPrim2 (op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf (cond, _then, _else, _) ->
        let cond_imm, cond_setup = helpI cond in
        (EIf (cond_imm, anf _then, anf _else, ()), cond_setup)
    | ENumber (n, _) -> (ENumber (n, ()), [])
    | EBool (b, _) -> (EBool (b, ()), [])
    | ELet ([], body, _) -> helpC body
    | ELet ((bind, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    | EId (name, _) -> (EId (name, ()), [])
  and helpI (e : tag expr) : unit expr * (string * unit expr) list =
    match e with
    | EPrim1 (op, arg, tag) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (EId (tmp, ()), arg_setup @ [(tmp, EPrim1 (op, arg_imm, ()))])
    | EPrim2 (op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (EId (tmp, ()), left_setup @ right_setup @ [(tmp, EPrim2 (op, left_imm, right_imm, ()))])
    | EIf (cond, _then, _else, tag) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        (EId (tmp, ()), cond_setup @ [(tmp, EIf (cond_imm, anf _then, anf _else, ()))])
    | ENumber (n, _) -> (ENumber (n, ()), [])
    | EBool (b, _) -> (EBool (b, ()), [])
    | ELet ([], body, _) -> helpI body
    | ELet ((bind, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    | EId (name, _) -> (EId (name, ()), [])
  and anf e =
    let ans, ans_setup = helpI e in
    List.fold_right (fun (bind, exp) body -> ELet ([(bind, exp, ())], body, ())) ans_setup ans
  in
  anf e
;;

let rec find (ls : (string * 'a) list) (x : string) : 'a =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y, v) :: rest ->
      if y = x then
        v
      else
        find rest x
;;

(* NOTE: Assumes that e is in ANF *)
let rec count_vars (e : 'a expr) =
  match e with
  | EIf (_, t, f, _) -> max (count_vars t) (count_vars f)
  | ELet ([(_, b, _)], body, _) -> 1 + max (count_vars b) (count_vars body)
  | _ -> 0
;;

let rec replicate (x : 'a) (i : int) : 'a list =
  if i = 0 then
    []
  else
    x :: replicate x (i - 1)
;;

let rec compile_expr (e : tag expr) (si : int) (env : (string * int) list) : instruction list =
  match e with
  | ELet ([(id, e, _)], body, _) ->
      let prelude = compile_expr e (si + 1) env in
      let body = compile_expr body (si + 1) ((id, si) :: env) in
      prelude @ [IMov (RegOffset (~-si, RBP), Reg RAX)] @ body
  | EPrim1 _ -> raise (NotYetImplemented "Fill in here")
  | EPrim2 _ -> raise (NotYetImplemented "Fill in here")
  | EIf _ -> raise (NotYetImplemented "Fill in here")
  | ENumber _ -> [IMov (Reg RAX, compile_imm e env)]
  | EBool _ -> [IMov (Reg RAX, compile_imm e env)]
  | EId _ -> [IMov (Reg RAX, compile_imm e env)]
  | _ -> raise (InternalCompilerError "Impossible: Not in ANF")

and compile_imm (e : tag expr) (env : (string * int) list) : arg =
  match e with
  | ENumber (n, _) ->
      if n > Int64.div Int64.max_int 2L || n < Int64.div Int64.min_int 2L then
        (* TODO: raise a better error of your choosing here *)
        failwith ("Integer overflow: " ^ Int64.to_string n)
      else
        raise (NotYetImplemented "Fill in here")
  | EBool (true, _) -> raise (NotYetImplemented "Fill in here")
  | EBool (false, _) -> raise (NotYetImplemented "Fill in here")
  | EId (x, _) -> RegOffset (~-(find env x), RBP)
  | _ -> raise (InternalCompilerError "Impossible: not an immediate")
;;

let compile_prog (anfed : tag expr) : string =
  let prelude = "section .text\nextern error\nextern print\nglobal our_code_starts_here" in
  let stack_setup = [ (* FILL: insert instructions for setting up stack here *) ] in
  let postlude =
    [ IRet
      (* FILL: insert instructions for cleaning up stack, and maybe
         some labels for jumping to errors, here *) ]
  in
  let body = compile_expr anfed 1 [] in
  let as_assembly_string = to_asm (stack_setup @ body @ postlude) in
  sprintf "%s%s\n" prelude as_assembly_string
;;

let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog |> add_phase well_formed check_scope |> add_phase tagged tag |> add_phase renamed rename
  |> add_phase anfed (fun p -> tag (anf p))
  |> add_phase result compile_prog
;;
