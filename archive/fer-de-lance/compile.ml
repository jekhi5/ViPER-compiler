open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
open Wellformed
open Desugar

(* 
  []========================================================[]
  ||  A note on organization:                               ||
  ||    We moved the well-formedness and desugaring code    ||
  ||    to their own respective files:                      ||
  ||      - wellformed.ml                                   ||
  ||      - desugar.ml                                      ||
  ||                                                        ||
  ||  Things we know are broken and will fail tests:        ||
  ||  - Checking for heap overflow (still broken from egg)  ||
  ||  - The tuple unpacking bug (a,b,c) = (1,2,3,4)         ||
  ||  - Checking for non-closure values (too eagerly...)    ||
  ||  - Native functions like print                         ||
  ||                                                        ||
  || It was a busy week, and I think we just have to        ||
  || take the L on this one...                              ||
  || Of our tests, 15 fail. We didn't have time to fix      ||
  || those specific files.                                  ||
  []========================================================[]
*)

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

let err_UNPACK_ERR = 18L

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

let heap_reg = R15

let scratch_reg = R11

let scratch_reg2 = R10

let not_a_number_comp_label = "error_not_number_comp"

let not_a_number_arith_label = "error_not_number_arith"

let not_a_bool_logic_label = "error_not_bool_logic"

let not_a_bool_if_label = "error_not_bool_if"

let overflow_label = "error_overflow"

(* Errors for tuples *)
let not_a_tuple_access_label = "error_not_tuple_access"

let not_a_number_index_label = "error_not_number_index"

let index_high_label = "error_get_high_index"

let index_low_label = "error_get_low_index"

let nil_deref_label = "error_nil_deref"

let err_call_not_closure_label = "err_not_closure"

let err_arity_mismatch_label = "err_arity_mismatch"

let err_unpack_err_label = "err_unpack_err"

let err_out_of_memory_label = "err_out_of_memory"

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

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

(* Enforces that the value in RAX is a bool. Goes to the specified label if not. *)
(* We could check a parameterized register, but that creates complexity in reporting the error. *)
(* We opt to hard-code RAX, for more consistency in exchange for some more boiler-plate code. *)
let check_bool (goto : string) : instruction list =
  [ IMov (Reg scratch_reg2, Reg RAX);
    IMov (Reg scratch_reg, HexConst bool_tag_mask);
    IAnd (Reg scratch_reg2, Reg scratch_reg);
    ICmp (Reg scratch_reg2, HexConst bool_tag);
    IJnz (Label goto) ]
;;

(* Enforces that the value in RAX is a num. Goes to the specified label if not. *)
let check_num (goto : string) : instruction list =
  [ IMov (Reg scratch_reg, HexConst num_tag_mask);
    ITest (Reg RAX, Reg scratch_reg);
    IJnz (Label goto) ]
;;

(* Enforces that the value in RAX is a tuple. Goes to the specified label if not. *)
let check_tuple (goto : string) : instruction list =
  (* This mangles RAX, btw.
     We must either reset rax after this,
     or use a temp register here.
  *)
  [ IMov (Reg scratch_reg2, Reg RAX);
    IAnd (Reg scratch_reg2, HexConst tuple_tag_mask);
    IMov (Reg scratch_reg, HexConst tuple_tag);
    ICmp (Reg scratch_reg2, Reg scratch_reg);
    IJnz (Label goto) ]
;;

(* Enforces that the value in RAX is not nil. Goes to the specified label if it is. *)
let check_not_nil (goto : string) : instruction list =
  [IMov (Reg scratch_reg, HexConst tuple_tag); ICmp (Reg RAX, Reg scratch_reg); IJz (Label goto)]
;;

let check_overflow = IJo (Label overflow_label)

(* Note: compile_cexpr helpers are directly copied from the previous assignment.  *)

(* Helper for numeric comparisons *)
let compare_prim2 (op : prim2) (e1 : arg) (e2 : arg) (t : tag) : instruction list =
  (* Move the first arg into RAX so we can type-check it. *)
  let string_op = "comparison_label" in
  let comp_label = sprintf "%s#%d" string_op t in
  let jump =
    match op with
    | Greater -> IJg (Label comp_label)
    | GreaterEq -> IJge (Label comp_label)
    | Less -> IJl (Label comp_label)
    | LessEq -> IJle (Label comp_label)
    | _ -> raise (InternalCompilerError "Expected comparison operator.")
  in
  let comp_done_label = sprintf "%s_done#%d" string_op t in
  [IMov (Reg RAX, e1)]
  @ check_num not_a_number_comp_label
  @ [IMov (Reg RAX, e2)]
  @ check_num not_a_number_comp_label
  @ [ ILineComment (sprintf "BEGIN %s#%d -------------" string_op t);
      IMov (Reg RAX, e1);
      (* cmp is weird and breaks if we don't use a temp register... *)
      IMov (Reg scratch_reg, e2);
      ICmp (Reg RAX, Reg scratch_reg);
      jump;
      IMov (Reg RAX, const_false);
      IJmp (Label comp_done_label);
      ILabel comp_label;
      IMov (Reg RAX, const_true);
      ILabel comp_done_label;
      ILineComment (sprintf "END %s#%d   -------------" string_op t) ]
;;

(* Helper for arithmetic operations *)
let arithmetic_prim2 (op : prim2) (e1 : arg) (e2 : arg) : instruction list =
  (* Move the first arg into RAX so we can type-check it. *)
  [IMov (Reg RAX, e1)]
  @ check_num not_a_number_arith_label
  @ [IMov (Reg RAX, e2)]
  @ check_num not_a_number_arith_label
  @
  match op with
  (* Arithmetic operators *)
  | Plus -> [IMov (Reg scratch_reg, e1); IAdd (Reg RAX, Reg scratch_reg); check_overflow]
  (* Make sure to check for overflow BEFORE shifting on multiplication! *)
  | Times ->
      [ IMov (Reg scratch_reg, e1);
        IMul (Reg RAX, Reg scratch_reg);
        check_overflow;
        ISar (Reg RAX, Const 1L) ]
  (* For minus, we need to move e1 back into RAX to compensate for the lack of commutativity, 
   * while also preserving the order in which our arguments will fail a typecheck.
   * So, `false - true` will fail on `false` every time.
   *)
  | Minus ->
      [ IMov (Reg scratch_reg, e2);
        IMov (Reg RAX, e1);
        ISub (Reg RAX, Reg scratch_reg);
        check_overflow ]
  (* Comparison operators *)
  | _ -> raise (InternalCompilerError "Expected arithmetic operator.")
;;

(* Helper for boolean and *)
let and_prim2 (e1 : arg) (e2 : arg) (t : tag) : instruction list =
  let true_label = sprintf "true#%d" t in
  let false_label = sprintf "false#%d" t in
  let logic_done_label = sprintf "and_done#%d" t in
  [ ILineComment (sprintf "BEGIN and#%d -------------" t);
    (* Move the first arg into RAX so we can type-check it. *)
    IMov (Reg RAX, e1) ]
  @ check_bool not_a_bool_logic_label
    (* In order to handle short-circuiting, we don't look at the second arg until later.
     * This means that `false and 5` will NOT raise a type error.
     *)
  @ [ IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJz (Label false_label);
      IMov (Reg RAX, e2) ]
  @ check_bool not_a_bool_logic_label
  @ [ (* Need to re-set scratch_reg since it gets changed in check_bool.*)
      IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJz (Label false_label);
      ILabel true_label;
      IMov (Reg RAX, const_true);
      IJmp (Label logic_done_label);
      ILabel false_label;
      IMov (Reg RAX, const_false);
      ILabel logic_done_label;
      ILineComment (sprintf "END and#%d   -------------" t) ]
;;

(* Helper for boolean or *)
let or_prim2 (e1 : arg) (e2 : arg) (t : tag) : instruction list =
  let true_label = sprintf "true#%d" t in
  let false_label = sprintf "false#%d" t in
  let logic_done_label = sprintf "or_done#%d" t in
  [ ILineComment (sprintf "BEGIN and#%d -------------" t);
    (* Move the first arg into RAX so we can type-check it. *)
    IMov (Reg RAX, e1) ]
  @ check_bool not_a_bool_logic_label
    (* In order to handle short-circuiting, we don't look at the second arg until later.
     * This means that `true or 5` will NOT raise a type error.
     *)
  @ [ IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJnz (Label true_label);
      IMov (Reg RAX, e2) ]
  @ check_bool not_a_bool_logic_label
  @ [ (* Need to re-set scratch_reg since it gets changed in check_bool.*)
      IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJnz (Label true_label);
      ILabel false_label;
      IMov (Reg RAX, const_false);
      IJmp (Label logic_done_label);
      ILabel true_label;
      IMov (Reg RAX, const_true);
      ILabel logic_done_label;
      ILineComment (sprintf "END or#%d   -------------" t) ]
;;

let move_with_scratch arg1 arg2 = [IMov (Reg scratch_reg, arg2); IMov (arg1, Reg scratch_reg)]

(* Checks that the value in the given location ends in 0x5 (the closure tag).
 * With this and `check_arity`, we make sure not to edit the original register.
 * We need to preserve the tag!
 *)
let check_function (reg : arg) =
  [ IMov (Reg scratch_reg, reg);
    IAnd (Reg scratch_reg, Const closure_tag_mask);
    IMov (Reg RAX, reg);
    (* put the checked value into RAX before potentially jumping.*)
    ICmp (Reg scratch_reg, Const closure_tag);
    IJne (Label err_call_not_closure_label) ]
;;

(* Assumes that the given argument is a function! *)
let check_arity (arity : int) =
  let arity_const = Const (Int64.of_int arity) in
  [ (* Remove the tag *)
    ISub (Reg RAX, HexConst closure_tag);
    (* The function arity is the first value stored.
     * It is stored as a regular number, not as a SNAKEVAL.
     *)
    ICmp (Sized (QWORD_PTR, RegOffset (0, RAX)), arity_const);
    IMov (Reg RSI, arity_const);
    IJne (Label err_arity_mismatch_label) ]
;;

let rec compile_fun (fun_name : string) args body env : instruction list =
  raise (NotYetImplemented "Compile funs not yet implemented")

and compile_lambda (e : tag cexpr) si env num_args is_tail =
  match e with
  | CLambda (args, body, tag) ->
      let fun_label = sprintf "func#%d" tag in
      let after_label = sprintf "func_end#%d" tag in
      let acexp = ACExpr e in
      let vars = deepest_stack acexp env in
      let arity = List.length args in
      let free_vars = List.sort String.compare (free_vars (ACExpr e)) in
      let free_var_regs = List.map (fun v -> List.assoc v env) free_vars in
      let num_free = List.length free_vars in
      let load_closure =
        List.concat
          (List.mapi
             (fun i (arg : arg) ->
               match arg with
               | Reg heap_reg ->
                   [ IMov (Reg RAX, arg);
                     IAdd (Reg RAX, Const closure_tag);
                     IMov (Sized (QWORD_PTR, RegOffset (i + 3, heap_reg)), Reg RAX) ]
               | _ ->
                   [ IMov (Sized (QWORD_PTR, Reg RAX), arg);
                     IMov (Sized (QWORD_PTR, RegOffset (i + 3, heap_reg)), Reg RAX) ] )
             free_var_regs )
      in
      let stack_padding =
        if vars mod 2 = 1 then
          vars + 1
        else
          vars
      in
      let _, _, unpack_closure_instrs, new_env =
        (* This fold needs two counters, so it can't just be a mapi.
         * i: The index in the closure
         * j: The offset from RBP, where we will move the variable.
         *)
        List.fold_left
          (fun (i, j, acc_instrs, old_env) id ->
            let offset = RegOffset (j, RBP) in
            ( (* Advance to the next word in the closure *)
              i + 1,
              (* Move up to the next slot above RBP *)
              j - 1,
              (* At this point in time, the closure pointer
               * should be stored in the scratch register. *)
              IMov (Reg RAX, RegOffset (i, scratch_reg)) (* Grab the closure ptr*)
              :: IMov (offset, Reg RAX) (* Put it where it belongs*)
              :: acc_instrs,
              (id, offset) :: old_env ) )
          (* Start the index at 3 to skip the metadata words. *)
          (3, ~-1, [], env)
          free_vars
      in
      let heap_padding =
        ( if (4 + arity) mod 2 == 0 then
            4 + arity
          else
            4 + arity + 1 )
        * word_size
      in
      let stack_size = Int64.of_int (word_size * (2 + stack_padding)) in
      let prelude =
        [IJmp (Label after_label); ILabel fun_label; IPush (Reg RBP); IMov (Reg RBP, Reg RSP)]
      in
      let load_closure_setup =
        [ ILineComment "=== Load closure values ===";
          IMov (Sized (QWORD_PTR, RegOffset (0, heap_reg)), Const (Int64.of_int arity));
          ILea (Reg scratch_reg, RelLabel fun_label);
          IMov (Sized (QWORD_PTR, RegOffset (1, heap_reg)), Reg scratch_reg);
          IMov (Sized (QWORD_PTR, RegOffset (2, heap_reg)), Const (Int64.of_int num_free)) ]
      in
      let compiled_body = compile_aexpr body si new_env (List.length args) is_tail in
      let stack_cleanup =
        [ILineComment "=== Stack clean-up ==="; IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet]
      in
      let bump_heap =
        [ ILineComment "===========================";
          IMov (Reg RAX, Reg heap_reg);
          IAdd (Reg RAX, Const closure_tag);
          IAdd (Reg heap_reg, Const (Int64.of_int heap_padding)) ]
      in
      prelude
      @ [ ILineComment "=== Unpacking closure ===";
          (* Boost RSP to make room for closed vars *)
          ISub (Reg RSP, Const (Int64.of_int (num_free * word_size)));
          (* The scratch reg is going to hold the tuple pointer.
           * (i.e. the implicit first argument)
           *)
          IMov (Reg scratch_reg, RegOffset (2, RBP));
          ISub (Reg scratch_reg, Const 5L) ]
      @ unpack_closure_instrs
      @ [ ISub (Reg RSP, Const stack_size);
          IMov (RegOffset (0, RSP), Reg RDI);
          ILineComment "=== Function call ===" ]
      @ compiled_body @ stack_cleanup @ [ILabel after_label] @ load_closure_setup @ load_closure
      @ bump_heap
  | _ -> raise (InternalCompilerError "Expected CLambda in compile_lambda")

and compile_call (e : tag cexpr) si env num_args is_tail =
  match e with
  | CApp (func, args, call_type, tag) ->
      let func_reg = compile_imm func env in
      let arity = List.length args in
      let compiled_args = List.map (fun arg -> compile_imm arg env) args in
      let dummy_arg, dummy_len =
        if List.length compiled_args mod 2 = 0 then
          ([IMov (Reg scratch_reg, Const 0L); IPush (Reg scratch_reg)], 1)
        else
          ([], 0)
      in
      (* Account for the padding arg *)
      let adjusted_offsets =
        List.mapi
          (fun i arg ->
            match arg with
            | RegOffset (n, RSP) -> RegOffset (n + dummy_len, RSP)
            | _ -> arg )
          compiled_args
      in
      let arg_offset = List.length adjusted_offsets + dummy_len + 1 in
      let push_args =
        (* I wish there was a List.concat_rev_map :,) *)
        dummy_arg
        @ List.concat
            (List.rev
               (List.map
                  (fun arg -> [IMov (Reg scratch_reg, arg); IPush (Reg scratch_reg)])
                  adjusted_offsets ) )
      in
      (* The amount by which to lower RSP *)
      let stack_pull = word_size * (List.length compiled_args + dummy_len + 1) in
      let offset_RSP =
        match func_reg with
        | RegOffset (n, RSP) -> RegOffset (n + arg_offset, RSP)
        | _ -> func_reg
      in
      let stack_cleanup = [IAdd (Reg RSP, Const (Int64.of_int stack_pull))] in
      check_function func_reg
      @ check_arity arity
      @ push_args
      @ [IMov (Reg scratch_reg, offset_RSP); IPush (Reg scratch_reg); ICall (RegOffset (1, RAX))]
      @ stack_cleanup
  | _ -> raise (InternalCompilerError "Expected CApp in compile_call")

and compile_aexpr (e : tag aexpr) (si : int) (env : arg envt) (num_args : int) (is_tail : bool) :
    instruction list =
  match e with
  | ALet (id, bound, body, _) ->
      let prelude =
        compile_cexpr bound si env num_args (* TODO: Come back to this number *) false
      in
      let body = compile_aexpr body si env num_args (* TODO: Come back to this number *) is_tail in
      let offset = find env id in
      prelude @ [IMov (offset, Reg RAX)] @ body
  | ALetRec (bindings, body, _) ->
      let new_env, compiled_bindings =
        List.fold_left
          (fun (acc_env, acc_instrs) (binder, bound) ->
            (* We know that new functions are always at the top of the heap, right before we compile. *)
            let rec_env = (binder, Reg heap_reg) :: acc_env in
            let offset = find env binder in
            let compiled_bound = compile_cexpr bound si rec_env num_args is_tail in
            (* TODO: Before or after? *)
            (env, acc_instrs @ compiled_bound @ [IMov (offset, Reg RAX)]) )
          (env, [ (* compiled code *) ]) bindings
      in
      let compiled_body = compile_aexpr body si new_env num_args is_tail in
      compiled_bindings @ compiled_body
  | ASeq (first, next, tag) ->
      let compiled_first = compile_cexpr first si env num_args is_tail in
      let compiled_next = compile_aexpr next si env num_args is_tail in
      compiled_first @ compiled_next
  | ACExpr cexp -> compile_cexpr cexp si env num_args is_tail

and compile_cexpr (e : tag cexpr) si env num_args is_tail =
  match e with
  | CImmExpr immexp ->
      [IMov (Reg scratch_reg, compile_imm immexp env); IMov (Reg RAX, Reg scratch_reg)]
  | CIf (cond, thn, els, t) ->
      let else_label = sprintf "if_else#%d" t in
      let done_label = sprintf "if_done#%d" t in
      (let cond_reg = compile_imm cond env in
       [ILineComment (sprintf "BEGIN conditional#%d   -------------" t); IMov (Reg RAX, cond_reg)]
       @ check_bool not_a_bool_if_label
       @ [ IMov (Reg scratch_reg, bool_mask);
           ITest (Reg RAX, Reg scratch_reg);
           IJz (Label else_label);
           ILineComment "  Then case:" ]
       @ compile_aexpr thn si env num_args is_tail
       @ [IJmp (Label done_label); ILineComment "  Else case:"; ILabel else_label]
       @ compile_aexpr els si env num_args is_tail )
      @ [ILabel done_label; ILineComment (sprintf "END conditional#%d     -------------" t)]
  | CPrim1 (op, e, t) -> (
      let e_reg = compile_imm e env in
      match op with
      | Add1 ->
          (IMov (Reg RAX, e_reg) :: check_num not_a_number_arith_label)
          @ [IAdd (Reg RAX, Const 2L); check_overflow]
      | Sub1 ->
          (IMov (Reg RAX, e_reg) :: check_num not_a_number_arith_label)
          @ [IAdd (Reg RAX, Const (-2L)); check_overflow]
      (* `xor` can't take a 64-bit literal, *)
      | Not ->
          (IMov (Reg RAX, e_reg) :: check_bool not_a_bool_logic_label)
          @ [IMov (Reg scratch_reg, bool_mask); IXor (Reg RAX, Reg scratch_reg)]
      | IsBool ->
          let false_label = sprintf "is_bool_false#%d" t in
          let done_label = sprintf "is_bool_done#%d" t in
          [ILineComment (sprintf "BEGIN is_bool%d -------------" t); IMov (Reg RAX, e_reg)]
          @ check_bool false_label
          @ [ IMov (Reg RAX, const_true);
              IJmp (Label done_label);
              ILabel false_label;
              IMov (Reg RAX, const_false);
              ILabel done_label;
              ILineComment (sprintf "END is_bool%d   -------------" t) ]
      | IsNum ->
          let false_label = sprintf "is_num_false#%d" t in
          let done_label = sprintf "is_num_done#%d" t in
          [ILineComment (sprintf "BEGIN is_num%d -------------" t); IMov (Reg RAX, e_reg)]
          @ check_num false_label
          @ [ IMov (Reg RAX, const_true);
              IJmp (Label done_label);
              ILabel false_label;
              IMov (Reg RAX, const_false);
              ILabel done_label;
              ILineComment (sprintf "END is_num%d   -------------" t) ]
      | Print ->
          [ (* Print both passes its value to the external function, and returns it. *)
            IMov (Reg RDI, e_reg);
            (* TODO: Is this right?? *)
            ICall (Label "print") (* The answer goes in RAX :) *) ]
      | IsTuple ->
          let false_label = sprintf "is_tuple_false#%d" t in
          let done_label = sprintf "is_tuple_done#%d" t in
          [ILineComment (sprintf "BEGIN is_tuple%d -------------" t); IMov (Reg RAX, e_reg)]
          @ check_tuple false_label
          @ check_not_nil false_label
          @ [ IMov (Reg RAX, const_true);
              IJmp (Label done_label);
              ILabel false_label;
              IMov (Reg RAX, const_false);
              ILabel done_label;
              ILineComment (sprintf "END is_tuple%d   -------------" t) ]
      | PrintStack -> raise (NotYetImplemented "Fill in PrintStack here") )
  | CPrim2 (op, e1, e2, t) -> (
      let e1_reg = compile_imm e1 env in
      let e2_reg = compile_imm e2 env in
      match op with
      | Plus | Minus | Times -> arithmetic_prim2 op e1_reg e2_reg
      | Greater | GreaterEq | Less | LessEq -> compare_prim2 op e1_reg e2_reg t
      | And -> and_prim2 e1_reg e2_reg t
      | Or -> or_prim2 e1_reg e2_reg t
      | Eq ->
          let true_label = sprintf "equal#%d" t in
          let done_label = sprintf "equal_done#%d" t in
          (* No typechecking for Eq. We can just see if the two values are equivalent. *)
          [ IMov (Reg RAX, e1_reg);
            IMov (Reg scratch_reg, e2_reg);
            ICmp (Reg RAX, Reg scratch_reg);
            IJe (Label true_label);
            IMov (Reg RAX, const_false);
            IJmp (Label done_label);
            ILabel true_label;
            IMov (Reg RAX, const_true);
            ILabel done_label ]
      | CheckSize ->
          (* Check that the tuple `e1` has size `e2`.
           * We don't have to type-check these since:
           * - By the time we evaluate a CheckSize, we have already guaranteed that e1 is a tuple
           * - We create CheckSize during desugaring, and we only ever make `e2` an ENumber.
           *)
          [ IMov (Reg RAX, e1_reg);
            IMov (Reg scratch_reg, RegOffset (0, RAX));
            IMov (Reg RAX, e2_reg);
            ISar (Reg RAX, Const 1L);
            ICmp (Reg scratch_reg, Reg RAX);
            IMul (Reg RAX, Const 2L);
            (* Note that RAX stores the expected arity. *)
            IJne (Label err_unpack_err_label) ] )
  | CLambda _ -> compile_lambda e si env num_args is_tail
  | CApp (func, args, Snake, tag) -> compile_call e si env num_args is_tail
  | CTuple (items, _) ->
      let n = List.length items in
      let heap_bump_amt =
        if n mod 2 == 0 then
          Int64.of_int word_size
        else
          0L
      in
      let loading_instrs =
        List.concat
        @@ List.mapi
             (fun i item -> move_with_scratch (RegOffset (i + 1, R15)) (compile_imm item env))
             items
      in
      ILineComment "=== Begin tuple initialization ==="
      :: move_with_scratch (RegOffset (0, R15)) (HexConst (Int64.of_int n))
      @ loading_instrs
      @ [ IMov (Reg RAX, Reg R15);
          IAdd (Reg RAX, Const 1L);
          IAdd (Reg R15, Const (Int64.of_int (word_size * (n + 1))));
          IInstrComment (IAdd (Reg R15, Const heap_bump_amt), "8 if even items, 0 if odd") ]
      @ [ILineComment "==== End tuple initialization ===="]
  | CGetItem (tup, idx, _) ->
      let tup_reg = compile_imm tup env in
      let idx_reg = compile_imm idx env in
      [ILineComment "==== Begin get-item ===="; IMov (Reg RAX, tup_reg)]
      @ check_tuple not_a_tuple_access_label
      @ [IMov (Reg RAX, tup_reg)]
      @ check_not_nil nil_deref_label
      @ [IMov (Reg RAX, idx_reg)]
      @ check_num not_a_number_index_label
      @ [ IMov (Reg RAX, tup_reg);
          (* Because we mangled RAX in check_tuple.*)
          ISub (Reg RAX, Const 1L);
          IMov (Reg R11, idx_reg);
          IShr (Reg R11, Const 1L);
          ICmp (Reg R11, Const 0L);
          IJl (Label index_low_label);
          ICmp (Reg R11, Reg RAX);
          IJge (Label index_high_label);
          (* IInstrComment
             (IAdd (Reg R11, Const 1L), "R11 already has n, now add 1 to account for the length"); *)
          ILineComment "Multiply the value in R11 by 8 with no further offset" ]
      @ move_with_scratch (Reg RAX) (RegOffsetReg (RAX, R11, word_size, word_size))
      @ [ILineComment "===== End get-item ====="]
  | CSetItem (tup, idx, value, _) ->
      let tup_reg = compile_imm tup env in
      let idx_reg = compile_imm idx env in
      let val_reg = compile_imm value env in
      let tuple_slot_offset = RegOffsetReg (RAX, R11, word_size, word_size) in
      [ILineComment "==== Begin set-item ===="; IMov (Reg RAX, tup_reg)]
      @ check_tuple not_a_tuple_access_label
      @ [IMov (Reg RAX, tup_reg)]
      @ check_not_nil nil_deref_label
      @ [IMov (Reg RAX, idx_reg)]
      @ check_num not_a_number_index_label
      @ [ IMov (Reg RAX, tup_reg);
          ISub (Reg RAX, Const 1L);
          IMov (Reg R11, idx_reg);
          IShr (Reg R11, Const 1L);
          ICmp (Reg R11, Const 0L);
          IJl (Label index_low_label);
          ICmp (Reg R11, Reg RAX);
          IJge (Label index_high_label);
          (* IInstrComment
             (IAdd (Reg R11, Const 1L), "R11 already has n, now add 1 to account for the length"); *)
          IMov (Reg scratch_reg2, val_reg);
          IInstrComment
            ( IMov (tuple_slot_offset, Reg scratch_reg2),
              "Store the location of the relevant value in RAX" );
          IMov (Reg RAX, Reg scratch_reg2);
          ILineComment "===== End set-item =====" ]
  | _ -> []

and compile_imm e env =
  match e with
  | ImmNum (n, _) -> Const (Int64.shift_left n 1)
  | ImmBool (true, _) -> const_true
  | ImmBool (false, _) -> const_false
  | ImmId (x, _) -> find env x
  | ImmNil _ -> Const tuple_tag
;;

let runtime_errors =
  List.concat_map
    (fun (label, err_code) ->
      [ ILabel label;
        IMov (Reg RDI, Const err_code);
        (* We ended up ignoring this argument in main.c. *)
        IMov (Reg RSI, Reg RAX);
        ICall (Label "error");
        IRet (* Theoretically we don't need this `ret`.*) ] )
    [ (not_a_number_comp_label, err_COMP_NOT_NUM);
      (not_a_number_arith_label, err_ARITH_NOT_NUM);
      (not_a_bool_logic_label, err_LOGIC_NOT_BOOL);
      (not_a_bool_if_label, err_IF_NOT_BOOL);
      (overflow_label, err_OVERFLOW);
      (not_a_tuple_access_label, err_GET_NOT_TUPLE);
      (not_a_number_index_label, err_GET_NOT_NUM);
      (index_high_label, err_GET_HIGH_INDEX);
      (index_low_label, err_GET_LOW_INDEX);
      (nil_deref_label, err_NIL_DEREF);
      (err_unpack_err_label, err_UNPACK_ERR);
      (err_out_of_memory_label, err_OUT_OF_MEMORY);
      (err_call_not_closure_label, err_CALL_NOT_CLOSURE);
      (err_arity_mismatch_label, err_CALL_ARITY_ERR) ]
;;

let compile_prog ((anfed : tag aprogram), (env : arg envt)) : string =
  match anfed with
  | AProgram (body, _) ->
      let body_prologue =
        "section .text\n\
         extern error\n\
         extern print\n\
         extern input\n\
         extern equal\n\
         global our_code_starts_here\n\
         our_code_starts_here:"
      in
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
      let compiled_body = compile_aexpr body 0 env vars false in
      let stack_setup =
        [IPush (Reg RBP); IMov (Reg RBP, Reg RSP); ISub (Reg RSP, Const stack_size)]
      in
      let stack_cleanup = [IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet] in
      let heap_start =
        [ ILineComment "=== Heap start ===";
          IInstrComment
            ( IMov (Sized (QWORD_PTR, Reg heap_reg), Reg (List.nth first_six_args_registers 0)),
              "Load heap_reg with our argument, the heap pointer" );
          IInstrComment
            ( IAdd (Sized (QWORD_PTR, Reg heap_reg), Const 15L),
              "Align it to the nearest multiple of 16" );
          IMov (Reg scratch_reg, HexConst 0xFFFFFFFFFFFFFFF0L);
          IInstrComment
            ( IAnd (Sized (QWORD_PTR, Reg heap_reg), Reg scratch_reg),
              "by adding no more than 15 to it" );
          ILineComment "==== Heap end ====" ]
      in
      let main =
        to_asm (stack_setup @ heap_start @ compiled_body @ stack_cleanup @ runtime_errors)
      in
      sprintf "%s%s\n" body_prologue main
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
