open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
open Wellformed
open Desugar

(* Documentation can be found at https://v2.ocaml.org/api/Set.S.html *)
module StringSet = Set.Make (String)

(* Documentation can be found at https://v2.ocaml.org/api/Map.S.html *)
module StringMap = Map.Make (String)

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

let closure_tag = 0x0000000000000005L

let closure_tag_mask = 0x0000000000000007L

let tuple_tag = 0x0000000000000001L

let tuple_tag_mask = 0x0000000000000007L

let const_nil = HexConst tuple_tag

let err_COMP_NOT_NUM = 1L

let err_ARITH_NOT_NUM = 2L

let err_LOGIC_NOT_BOOL = 3L

let err_IF_NOT_BOOL = 4L

let err_OVERFLOW = 5L

let err_GET_NOT_TUPLE = 6L

let err_GET_LOW_INDEX = 7L

let err_GET_HIGH_INDEX = 8L

let err_GET_NOT_NUM = 9L

let err_NIL_DEREF = 10L

let err_OUT_OF_MEMORY = 11L

let err_SET_NOT_TUPLE = 12L

let err_SET_LOW_INDEX = 13L

let err_SET_NOT_NUM = 14L

let err_SET_HIGH_INDEX = 15L

let err_CALL_NOT_CLOSURE = 16L

let err_CALL_ARITY_ERR = 17L

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

let heap_reg = R15

let scratch_reg = R11

let scratch_reg2 = R10

(* You may find some of these helpers useful *)

let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y, v) :: rest ->
      if y = x then
        v
      else
        find rest x
;;

let count_vars e =
  let rec helpA e =
    match e with
    | ASeq (e1, e2, _) -> max (helpC e1) (helpA e2)
    | ALet (_, bind, body, _) -> 1 + max (helpC bind) (helpA body)
    | ALetRec (binds, body, _) ->
        List.length binds
        + List.fold_left max (helpA body) (List.map (fun (_, rhs) -> helpC rhs) binds)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in
  helpA e
;;

let rec replicate x i =
  if i = 0 then
    []
  else
    x :: replicate x (i - 1)
;;

let rename_and_tag (p : tag program) : tag program =
  let rec rename env p =
    match p with
    | Program (decls, body, tag) ->
        Program (List.map (fun group -> List.map (helpD env) group) decls, helpE env body, tag)
  and helpD env decl =
    match decl with
    | DFun (name, args, body, tag) ->
        let newArgs, env' = helpBS env args in
        DFun (name, newArgs, helpE env' body, tag)
  and helpB env b =
    match b with
    | BBlank _ -> (b, env)
    | BName (name, allow_shadow, tag) ->
        let name' = sprintf "%s_%d" name tag in
        (BName (name', allow_shadow, tag), (name, name') :: env)
    | BTuple (binds, tag) ->
        let binds', env' = helpBS env binds in
        (BTuple (binds', tag), env')
  and helpBS env (bs : tag bind list) =
    match bs with
    | [] -> ([], env)
    | b :: bs ->
        let b', env' = helpB env b in
        let bs', env'' = helpBS env' bs in
        (b' :: bs', env'')
  and helpBG env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a) :: bindings ->
        let b', env' = helpB env b in
        let e' = helpE env e in
        let bindings', env'' = helpBG env' bindings in
        ((b', e', a) :: bindings', env'')
  and helpE env e =
    match e with
    | ESeq (e1, e2, tag) -> ESeq (helpE env e1, helpE env e2, tag)
    | ETuple (es, tag) -> ETuple (List.map (helpE env) es, tag)
    | EGetItem (e, idx, tag) -> EGetItem (helpE env e, helpE env idx, tag)
    | ESetItem (e, idx, newval, tag) -> ESetItem (helpE env e, helpE env idx, helpE env newval, tag)
    | EPrim1 (op, arg, tag) -> EPrim1 (op, helpE env arg, tag)
    | EPrim2 (op, left, right, tag) -> EPrim2 (op, helpE env left, helpE env right, tag)
    | EIf (c, t, f, tag) -> EIf (helpE env c, helpE env t, helpE env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId (name, tag) -> ( try EId (find env name, tag) with InternalCompilerError _ -> e )
    | EApp (func, args, native, tag) ->
        let func = helpE env func in
        let call_type =
          (* TODO: If you want, try to determine whether func is a known function name, and if so,
             whether it's a Snake function or a Native function *)
          Snake
        in
        EApp (func, List.map (helpE env) args, call_type, tag)
    | ELet (binds, body, tag) ->
        let binds', env' = helpBG env binds in
        let body' = helpE env' body in
        ELet (binds', body', tag)
    | ELetRec (bindings, body, tag) ->
        let revbinds, env =
          List.fold_left
            (fun (revbinds, env) (b, e, t) ->
              let b, env = helpB env b in
              ((b, e, t) :: revbinds, env) )
            ([], env) bindings
        in
        let bindings' =
          List.fold_left (fun bindings (b, e, tag) -> (b, helpE env e, tag) :: bindings) [] revbinds
        in
        let body' = helpE env body in
        ELetRec (bindings', body', tag)
    | ELambda (binds, body, tag) ->
        let binds', env' = helpBS env binds in
        let body' = helpE env' body in
        ELambda (binds', body', tag)
  in
  rename [] p
;;

(* Returns the stack-index (in words) of the deepest stack index used for any
   of the variables in this expression *)
let rec deepest_stack e env =
  let rec helpA e =
    match e with
    | ALet (name, bind, body, _) ->
        List.fold_left max 0 [name_to_offset name; helpC bind; helpA body]
    | ALetRec (binds, body, _) ->
        List.fold_left max (helpA body) (List.map (fun (name, _) -> name_to_offset name) binds)
    | ASeq (first, rest, _) -> max (helpC first) (helpA rest)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (c, t, f, _) -> List.fold_left max 0 [helpI c; helpA t; helpA f]
    | CPrim1 (_, i, _) -> helpI i
    | CPrim2 (_, i1, i2, _) -> max (helpI i1) (helpI i2)
    | CApp (func, args, _, _) -> max (helpI func) (List.fold_left max 0 (List.map helpI args))
    | CTuple (vals, _) -> List.fold_left max 0 (List.map helpI vals)
    | CGetItem (t, _, _) -> helpI t
    | CSetItem (t, _, v, _) -> max (helpI t) (helpI v)
    | CLambda (args, body, _) ->
        let new_env = List.mapi (fun i a -> (a, RegOffset (i + 3, RBP))) args @ env in
        deepest_stack body new_env
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNil _ -> 0
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmId (name, _) -> name_to_offset name
  and name_to_offset name =
    match find env name with
    | RegOffset (words, RBP) -> words / -1 (* negative because stack direction *)
    | _ -> 0
  in
  max (helpA e) 0 (* if only parameters are used, helpA might return a negative value *)
;;

(* IMPLEMENT EVERYTHING BELOW *)

(* This data type lets us keep track of how a binding was introduced.
   We'll use it to discard unnecessary Seq bindings, and to distinguish
   letrec from let. Essentially, it accumulates just enough information
   in our binding list to tell us how to reconstruct an appropriate aexpr. *)
type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program ([], body, _) -> AProgram (helpA body, ())
    | _ -> raise (InternalCompilerError "Top-level declarations should have been desugared away")
  and helpC (e : tag expr) : unit cexpr * unit anf_bind list =
    match e with
    | EPrim1 (op, arg, _) ->
        let arg_imm, arg_setup = helpI arg in
        (CPrim1 (op, arg_imm, ()), arg_setup)
    | EPrim2 (op, left, right, _) ->
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (CPrim2 (op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf (cond, _then, _else, _) ->
        let cond_imm, cond_setup = helpI cond in
        (CIf (cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ELet ([], body, _) -> helpC body
    | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELet ((BName (bind, _, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELet ((BTuple (_, _), _, _) :: _, _, _) ->
        raise (InternalCompilerError "Tuple bindings should have been desugared away")
    | ESeq (e1, e2, _) ->
        let e1_ans, e1_setup = helpC e1 in
        let e2_ans, e2_setup = helpC e2 in
        (e2_ans, e1_setup @ [BSeq e1_ans] @ e2_setup)
    | EApp (func, args, call_type, _) ->
        let args_ans, args_setup = List.split (List.map helpI args) in
        let func_ans, func_setup = helpI func in
        (* TODO: Do we need to flip the order of the setup?? *)
        (CApp (func_ans, args_ans, call_type, ()), func_setup @ List.concat args_setup)
    | ETuple (args, _) ->
        let imm_exprs, exprs_setup = List.split (List.map helpI args) in
        (CTuple (imm_exprs, ()), List.concat exprs_setup)
    | EGetItem (tuple, index, _) ->
        let imm_tuple, tuple_setup = helpI tuple in
        let imm_index, index_setup = helpI index in
        (CGetItem (imm_tuple, imm_index, ()), tuple_setup @ index_setup)
    | ESetItem (tuple, index, new_val, _) ->
        let imm_tuple, tuple_setup = helpI tuple in
        let imm_index, index_setup = helpI index in
        let imm_val, val_setup = helpI new_val in
        (CSetItem (imm_tuple, imm_index, imm_val, ()), tuple_setup @ index_setup @ val_setup)
    | ELambda (binds, body, _) ->
        let anf_body = helpA body in
        let bind_names =
          List.map
            (fun bind ->
              match bind with
              | BName (name, _, _) -> name
              | BBlank tag -> sprintf "blank_arg#%d" tag
              | _ -> raise (InternalCompilerError "Encountered BTuple in ANF - lambda.") )
            binds
        in
        (CLambda (bind_names, anf_body, ()), [])
    | ELetRec (bindings, body, _) ->
        let body_ans, body_setup = helpC body in
        let bindings_ans, bindings_setups =
          List.split
          @@ List.map
               (fun binding ->
                 match binding with
                 | BName (name, _, _), bound, _ ->
                     let b_ans, b_setup = helpC bound in
                     ((name, b_ans), b_setup)
                 | BBlank tag, bound, _ ->
                     let b_ans, b_setup = helpC bound in
                     (* TODO: Replace with a BSeq somehow *)
                     ((sprintf "blank_lr#%d" tag, b_ans), b_setup)
                 | _ -> raise (InternalCompilerError "Encountered BTuple in ANF - letrec.") )
               bindings
        in
        let bindings_setup = List.concat bindings_setups in
        (body_ans, body_setup @ bindings_setup @ [BLetRec bindings_ans])
    | _ ->
        let imm, setup = helpI e in
        (CImmExpr imm, setup)
  and helpI (e : tag expr) : unit immexpr * unit anf_bind list =
    match e with
    | ENumber (n, _) -> (ImmNum (n, ()), [])
    | EBool (b, _) -> (ImmBool (b, ()), [])
    | EId (name, _) -> (ImmId (name, ()), [])
    | ENil _ -> (ImmNil (), [])
    | ESeq (e1, e2, _) ->
        let _, e1_setup = helpI e1 in
        let e2_imm, e2_setup = helpI e2 in
        (e2_imm, e1_setup @ e2_setup)
    | ETuple (args, tag) ->
        let tmp = sprintf "tuple_%d" tag in
        let imm_args, args_setups = List.split (List.map helpI args) in
        let args_setup = List.concat args_setups in
        (ImmId (tmp, ()), args_setup @ [BLet (tmp, CTuple (imm_args, ()))])
    | EGetItem (tup, idx, tag) ->
        let tmp = sprintf "getItem_%d" tag in
        let imm_tup, tup_setup = helpI tup in
        let imm_idx, idx_setup = helpI idx in
        (ImmId (tmp, ()), tup_setup @ idx_setup @ [BLet (tmp, CGetItem (imm_tup, imm_idx, ()))])
    | ESetItem (tup, idx, newval, tag) ->
        let tmp = sprintf "getItem_%d" tag in
        let imm_tup, tup_setup = helpI tup in
        let imm_idx, idx_setup = helpI idx in
        let imm_newval, newval_setup = helpI newval in
        ( ImmId (tmp, ()),
          tup_setup @ idx_setup @ newval_setup
          @ [BLet (tmp, CSetItem (imm_tup, imm_idx, imm_newval, ()))] )
    | EPrim1 (op, arg, tag) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (ImmId (tmp, ()), arg_setup @ [BLet (tmp, CPrim1 (op, arg_imm, ()))])
    | EPrim2 (op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        ( ImmId (tmp, ()),
          left_setup @ right_setup @ [BLet (tmp, CPrim2 (op, left_imm, right_imm, ()))] )
    | EIf (cond, _then, _else, tag) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        (ImmId (tmp, ()), cond_setup @ [BLet (tmp, CIf (cond_imm, helpA _then, helpA _else, ()))])
    | EApp (func, args, call_type, tag) ->
        let tmp = sprintf "app_%d" tag in
        let imm_func, func_setup = helpI func in
        let imm_args, args_setups = List.split (List.map helpI args) in
        let args_setup = List.concat args_setups in
        ( ImmId (tmp, ()),
          func_setup @ args_setup @ [BLet (tmp, CApp (imm_func, imm_args, call_type, ()))] )
    | ELet ([], body, _) -> helpI body
    | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpI exp in
        (* MUST BE helpI, to avoid any missing final steps *)
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ body_setup)
    | ELet ((BName (bind, _, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELet ((BTuple (_, _), _, _) :: _, _, _) ->
        raise (InternalCompilerError "Tuple bindings should have been desugared away")
    | ELambda (binds, body, tag) ->
        let tmp = sprintf "lambda_%d" tag in
        let body_ans = helpA body in
        let bind_names =
          List.map
            (fun bind ->
              match bind with
              | BName (name, _, _) -> name
              | BBlank tag -> sprintf "blank_arg#%d" tag
              | _ -> raise (InternalCompilerError "Encountered BTuple in ANF - lambda.") )
            binds
        in
        (ImmId (tmp, ()), [BLet (tmp, CLambda (bind_names, body_ans, ()))])
        (* Hint: use BLet to bind the answer *)
    | ELetRec (bindings, body, _) ->
        (* TODO: Revise! I'm not sure if this is correct. I don't know where we would use BLet for the final answer. *)
        let body_ans, body_setup = helpI body in
        let bindings_ans, bindings_setups =
          List.split
          @@ List.map
               (fun binding ->
                 match binding with
                 | BName (name, _, _), bound, _ ->
                     let b_ans, b_setup = helpC bound in
                     ((name, b_ans), b_setup)
                 | BBlank tag, bound, _ ->
                     let b_ans, b_setup = helpC bound in
                     (* TODO: Replace with a BSeq somehow *)
                     ((sprintf "blank_lr#%d" tag, b_ans), b_setup)
                 | _ -> raise (InternalCompilerError "Encountered BTuple in ANF - letrec.") )
               bindings
        in
        let bindings_setup = List.concat bindings_setups in
        let bindings_anf = BLetRec bindings_ans in
        (body_ans, bindings_setup @ [bindings_anf] @ body_setup)
  (* Hint: use BLetRec for each of the binds, and BLet for the final answer *)
  and helpA e : unit aexpr =
    let ans, ans_setup = helpC e in
    List.fold_right
      (fun bind body ->
        (* Here's where the anf_bind datatype becomes most useful:
             BSeq binds get dropped, and turned into ASeq aexprs.
             BLet binds get wrapped back into ALet aexprs.
             BLetRec binds get wrapped back into ALetRec aexprs.
           Syntactically it looks like we're just replacing Bwhatever with Awhatever,
           but that's exactly the information needed to know which aexpr to build. *)
        match bind with
        | BSeq exp -> ASeq (exp, body, ())
        | BLet (name, exp) -> ALet (name, exp, body, ())
        | BLetRec names -> ALetRec (names, body, ()) )
      ans_setup (ACExpr ans)
  in
  helpP p
;;

let remove_dups (lst : 'a list) (eq : 'a -> 'a -> bool) : 'a list =
  List.fold_right
    (fun x acc ->
      if List.exists (eq x) acc then
        acc
      else
        x :: acc )
    lst []
;;

let free_vars (e : 'a aexpr) : string list =
  let rec helpI (e : 'a immexpr) (bound_ids : string list) : string list =
    match e with
    | ImmId (id, _) ->
        if List.mem id bound_ids then
          []
        else
          [id]
    | _ -> []
  and helpC (e : 'a cexpr) (bound_ids : string list) : string list =
    match e with
    | CIf (cond, thn, els, _) -> helpI cond bound_ids @ helpA thn bound_ids @ helpA els bound_ids
    | CPrim1 (_, expr, _) -> helpI expr bound_ids
    | CPrim2 (_, left, right, _) -> helpI left bound_ids @ helpI right bound_ids
    | CApp (func, args, _, _) ->
        helpI func bound_ids @ List.concat_map (fun arg -> helpI arg bound_ids) args
    | CImmExpr expr -> helpI expr bound_ids
    | CTuple (args, _) -> List.concat_map (fun arg -> helpI arg bound_ids) args
    | CGetItem (tup, idx, _) -> helpI tup bound_ids @ helpI idx bound_ids
    | CSetItem (tup, idx, new_elem, _) ->
        helpI tup bound_ids @ helpI idx bound_ids @ helpI new_elem bound_ids
    | CLambda (ids, body, _) -> helpA body (ids @ bound_ids)
  and helpA (e : 'a aexpr) (bound_ids : string list) : string list =
    match e with
    | ASeq (first, next, _) -> helpC first bound_ids @ helpA next bound_ids
    | ALet (name, bound, body, _) -> helpC bound bound_ids @ helpA body (name :: bound_ids)
    | ALetRec (binds, body, _) ->
        let declared, free =
          List.fold_left
            (fun (declared, free) (name, cexpr) ->
              (name :: declared, helpC cexpr (name :: declared) @ free) )
            (bound_ids, []) binds
        in
        helpA body declared @ free
    | ACExpr cexpr -> helpC cexpr bound_ids
  in
  remove_dups (helpA e []) ( = )
;;

let si_to_arg (si : int) : arg = RegOffset (~-si, RBP)

let naive_stack_allocation (AProgram (body, _) as prog : tag aprogram) : tag aprogram * arg envt =
  (* For the Xexpr helpers:
   * - Immediate values don't care about the env, so we ignore those.
   * - Cexprs are only interesting in the `CIf` case, since this case
   *   contains two Aexprs.
   * - Aexprs are where the main logic happens, since that is where we make new bindings.
       We convert the stack index to a RegOffset, then look at the bound expr, then the body.
       Note that whenever we recursively call helpA, we need to increment the stack index. 
   *)
  let rec helpC (cexp : tag cexpr) (env : arg envt) (si : int) : arg envt =
    match cexp with
    | CIf (_, thn, els, _) -> helpA thn env (si + 1) @ helpA els env (si + 1)
    | CPrim1 _ | CPrim2 _ | CApp _ | CImmExpr _ | CTuple _ | CGetItem _ | CSetItem _ -> env
    | CLambda (ids, body, _) ->
        let body_env = helpA body env (si + 1) in
        (* TODO: revisit adding 2 instead of 1 (we add 2 because before the ids 
         *       we put RBP and the return address (?)) 

         * Actually, we add 3, to account for the implicit 'self' argument.
         *)
        let args_env = List.mapi (fun index id -> (id, RegOffset (index + 3, RBP))) ids in
        args_env @ body_env
  and helpA (aexp : tag aexpr) (env : arg envt) (si : int) : arg envt =
    match aexp with
    | ALet (id, bound, body, _) ->
        let offset = (id, si_to_arg si) in
        let bound_offset = helpC bound env si in
        let body_offset = helpA body env (si + 1) in
        (offset :: bound_offset) @ body_offset
    | ACExpr cexp -> helpC cexp env si
    | ASeq (first, next, _) -> helpC first env si @ helpA next env (si + 1)
    | ALetRec ([], body, _) -> helpA body env (si + 1)
    | ALetRec ((id, bound) :: [], body, _) ->
        let offset = (id, si_to_arg si) in
        let bound_offset = helpC bound env si in
        let body_offset = helpA body env (si + 1) in
        (offset :: bound_offset) @ body_offset
    | ALetRec ((id, bound) :: rest, body, tag) ->
        let offset = (id, si_to_arg si) in
        let bound_offset = helpC bound env si in
        let body_offset = helpA body env (si + 1) in
        (offset :: bound_offset) @ body_offset @ helpA (ALetRec (rest, body, tag)) env (si + 1)
  in
  let body_env = helpA body [] 1 in
  (* We were rather sloppy with the process of adding to the environment,
   * so we just remove the duplicates in O(n^2) time at the end.
   *)
  (prog, remove_dups body_env (fun a b -> fst a = fst b))
;;

let err_call_not_closure_label = "err_not_closure#"

(* Checks that the value in the given location ends in 0x5 (the closure tag). *)
let check_function (reg : arg) =
  [ IMov (Reg scratch_reg, reg);
    IAnd (Reg scratch_reg, Const closure_tag_mask);
    IMov (Reg RAX, reg);
    (* put the checked value into RAX before potentially jumping.*)
    ICmp (Reg scratch_reg, Const closure_tag);
    IJne (Label err_call_not_closure_label) ]
;;

let err_arity_mismatch_label = "err_arity_mismatch#"

(* Assumes that the given argument is a function! *)
let check_arity (reg : arg) (arity : int) =
  let arity_const = Const (Int64.of_int arity)
  [
    IMov (Reg scratch_reg, reg);
    (* Remove the tag *)
    ISub (Reg scratch_reg, Const closure_tag);
    (* The function arity is the first value stored.
     * It is stored as a regular number, not as a SNAKEVAL.
     *)
    ICmp (RegOffset (0, scratch_reg), arity_const);
    (* Move the arity into RAX so we can report it as a potential bad value. *)
    IMov (Reg RAX, arity_const);
    IJne (Label err_arity_mismatch_label);
  ]

let rec compile_fun (fun_name : string) args body env : instruction list =
  raise (NotYetImplemented "Compile funs not yet implemented")

and compile_lambda (e : 'a cexpr) si env : instruction list =
  match e with
  | CLambda (args, body, tag) ->
      (* First, we set up all the things we will want to use to compile the function. *)
      let fun_name = sprintf "func#%d" tag in
      let fun_label, end_label = (ILabel fun_name, ILabel (fun_name ^ "_end")) in
      let acexp = ACExpr e in
      let arity = List.length args in
      let free = List.sort String.compare (free_vars acexp) in
      let closure = List.map (fun var -> List.assoc var env) free in
      let closed_count = List.length closure in
      (* Second, we can do the actual compilation. *)
      let moveClosureVarToStack idx =
        IMov
          ( RegOffset (~-8 * (idx + 1), RBP),
            (* move the i^th variable to the i^th slot *)
            RegOffset (24 + (8 * idx), RAX) )
        (* from the (i+3)^rd slot in the closure *)
      in
      let reserveSpace = ISub (Reg RSP, Const (Int64.of_int (8 * List.length free))) in
      let restoreFvs = List.mapi (fun i fv -> moveClosureVarToStack i) free in
      let newEnv = List.mapi (fun i fv -> (fv, RegOffset (~-8 * (i + 1), RBP))) free @ env in
      let compiledBody = compile_aexpr body (List.length args) newEnv in
      let vars = deepest_stack body env in
      let stack_size =
        Int64.of_int
          ( 8
          *
          (* TODO: FIX THIS HACK! *)
          if vars mod 2 = 1 then
            vars + 3
          else
            vars + 2 )
      in
      let stack_setup =
        [ ILabel fun_name;
          ILineComment "==== Stack set-up ====";
          IPush (Reg RBP);
          IMov (Reg RBP, Reg RSP);
          ISub (Reg RSP, Const stack_size);
          ILineComment "======================" ]
      in
      let unpack_closure =
        [ ILineComment "=== Unpack closure ===";
          IInstrComment (reserveSpace, "reserve space on the stack for closed-over vars");
          IInstrComment
            (IMov (Reg scratch_reg, RegOffset (2, RBP)), "Load and untag the self argument");
          ISub (Reg scratch_reg, Const closure_tag);
          ILineComment "Load values from the closure";
          ILineComment "======================" ]
      in
      (* Code for storing the closure itself *)
      let closure_label = sprintf "closure#%d" tag in
      let after_label = sprintf "after#%d" tag in
      let closure_instrs =
        [ IJmp (Label after_label);
          ILabel closure_label;
        ] @ 
          (* TODO: Insert compiled body here *)
          stack_setup
         @ [
          ILabel after_label;
          IMov (RegOffset (0, heap_reg), Const (Int64.of_int arity));
          IMov (RegOffset (1, heap_reg), Label closure_label);
          IMov (RegOffset (2, heap_reg), Const (Int64.of_int closed_count)) ]
        (* For each value in the closure, move it into the next slot in the heap block. *)
        @ List.concat
            (List.mapi
               (fun i var ->
                 [IMov (Reg scratch_reg, var); IMov (RegOffset (i + 3, heap_reg), Reg scratch_reg)] )
               closure )
        @ [ (* Return the closure *)
            IMov (Reg RAX, Reg heap_reg);
            (* Tag the closure to make it a SNAKEVAL *)
            IAdd (Reg RAX, Const closure_tag);
            (* Bump the heap by the appropriate amount. *)
            IAdd (Reg heap_reg, Const (Int64.of_int (word_size * (3 + closed_count)))) ]
          (* Note that we have 3 words of metadata: arity, code pointer, # vars.
           * In order to ensure that we keep the heap 16-aligned,
           * Closures must be an even number of words.
           * Since our metadata is odd, we only add padding if the # vars is even.
           *)
        @
        if closed_count mod 2 = 0 then
          [IAdd (Reg heap_reg, Const (Int64.of_int word_size))]
        else
          []
      in
      closure_instrs
  | _ -> raise (InternalCompilerError "Expected a CLambda in compile_lambda.")

and compile_aexpr (e : tag aexpr) (si : int) (env : arg envt) (num_args : int) (is_tail : bool) :
    instruction list =
  raise (NotYetImplemented "Compile aexpr not yet implemented")

and compile_cexpr (e : tag cexpr) si env num_args is_tail =
  raise (NotYetImplemented "Compile cexpr not yet implemented")

and compile_imm e env =
  match e with
  | ImmNum (n, _) -> Const (Int64.shift_left n 1)
  | ImmBool (true, _) -> const_true
  | ImmBool (false, _) -> const_false
  | ImmId (x, _) -> find env x
  | ImmNil _ -> Const tuple_tag
;;

let compile_prog ((anfed : tag aprogram), (env : arg envt)) : string =
  match anfed with
  | AProgram (body, _) ->
      let body_prologue, comp_body, body_epilogue =
        raise (NotYetImplemented "... do stuff with body ...")
      in
      let heap_start =
        [ ILineComment "heap start";
          IInstrComment
            ( IMov (Sized (QWORD_PTR, Reg heap_reg), Reg (List.nth first_six_args_registers 0)),
              "Load heap_reg with our argument, the heap pointer" );
          IInstrComment
            ( IAdd (Sized (QWORD_PTR, Reg heap_reg), Const 15L),
              "Align it to the nearest multiple of 16" );
          IMov (Reg scratch_reg, HexConst 0xFFFFFFFFFFFFFFF0L);
          IInstrComment
            ( IAnd (Sized (QWORD_PTR, Reg heap_reg), Reg scratch_reg),
              "by adding no more than 15 to it" ) ]
      in
      let main = to_asm (body_prologue @ heap_start @ comp_body @ body_epilogue) in
      raise (NotYetImplemented "... combine main with any needed extra setup and error handling ...")
;;

(* Feel free to add additional phases to your pipeline.
   The final pipeline phase needs to return a string,
   but everything else is up to you. *)

let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

(* Add at least one desugaring phase somewhere in here *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> add_err_phase well_formed is_well_formed
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase locate_bindings naive_stack_allocation
  |> add_phase result compile_prog
;;
