open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors

(* Documentation can be found at https://v2.ocaml.org/api/Set.S.html *)
module StringSet = Set.Make (String)

(* Documentation can be found at https://v2.ocaml.org/api/Map.S.html *)
module StringMap = Map.Make (String)

type 'a envt = (string * 'a) list

(* You might also find
     type 'a envt = 'a StringMap.t
   to be useful instead of a simple list of pairs. *)

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

let bind_eq b1 b2 =
  match b1 with
  | BBlank _ -> false (* Blank is not equal to anything, including itself. *)
  | BTuple _ -> false (* Tuples need to be unrolled before comparing. *)
  | BName (name1, _, _) -> (
    match b2 with
    | BName (name2, _, _) -> name1 = name2
    | _ -> false )
;;

let bind_loc (b : 'a bind) : 'a =
  match b with
  | BName (_, _, l) | BBlank l | BTuple (_, l) -> l
;;

(* Gets a mapping of function names to arity for all functions *)
let get_decl_env (decls : 'a decl list) : (string * int) list =
  List.map
    (fun d ->
      match d with
      | DFun (funname, args, _, _) -> (funname, List.length args) )
    decls
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

let rec find_decl (ds : 'a decl list) (name : string) : 'a decl option =
  match ds with
  | [] -> None
  | (DFun (fname, _, _, _) as d) :: ds_rest ->
      if name = fname then
        Some d
      else
        find_decl ds_rest name
;;

let rec find_one (l : 'a list) (elt : 'a) : bool =
  match l with
  | [] -> false
  | x :: xs -> elt = x || find_one xs elt
;;

let rec find_dup (l : 'a list) : 'a option =
  match l with
  | [] | [_] -> None
  | x :: xs ->
      if find_one xs x then
        Some x
      else
        find_dup xs
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

(* A couple of getters for binds. *)
let bind_name (b : 'a bind) : string =
  match b with
  | BName (name, _, _) -> name
  | BBlank _ -> ""
  | BTuple _ ->
      raise
        (* Since we can only get the name of a BName,
         * it only makes sense to call this function *after* desugaring.
         * Ergo, desugaring should happen first, and then well-formedness checking.
         *)
        (InternalCompilerError (sprintf "Getting name of BTuple %s" (Pretty.string_of_bind b)) )
;;

(* Get *all* nested binds. *)
let rec un_nest_bind (b : 'a bind) : 'a bind list =
  match b with
  | BName _ | BBlank _ -> [b]
  | BTuple (subs, _) -> List.concat_map un_nest_bind subs
;;

(* WILL NOT properly handle the bound expressions! 
 * This is merely for well-formedness checks on the binds. 
 * An un-nested binding contains no BTuples!
 *)
let un_nest_binding ((bind, bound, a) : 'a binding) : 'a binding list =
  List.map (fun b -> (b, bound, a)) (un_nest_bind bind)
;;

let is_well_formed (p : sourcespan program) : sourcespan program fallible =
  (* BEGIN EXPR CHECKS *)
  (* Check for duplicate bindings *)
  let rec check_dup_binding (bindings : 'a binding list) _ =
    (* TODO: Handle multiple bindings! *)
    List.fold_left
      (fun (seen, exns) ((bind, _, loc) as binding) ->
        match List.find_opt (fun (a, _, _) -> bind_eq a bind) seen with
        | Some (_, _, orig_loc) ->
            (* Note that we can safely call bind_name here:
             * - There are no tuples, because we make sure to un-nest our bindings.
             * - No BBlanks will satisfy the equality check, so they will never be found. 
             *)
            (seen, DuplicateId (bind_name bind, loc, orig_loc) :: exns)
        | None -> (binding :: seen, exns) )
      ([ (* bind, body, loc *) ], [ (* exns *) ])
      (List.concat_map un_nest_binding bindings)
  (* Check scope in each binding body *)
  and check_scope
      (bindings : 'a binding list)
      _
      id_env
      (non_shadowable_ids : sourcespan envt)
      decl_env
      (is_rec : bool) =
    (* Each bound body is allowed to use the names of all previous, bindings 
     * Note that this is a little weird for tuple bindings:
     * Since we check for each sub-binding individually against the same body,
     * we rely on the first sub-binding to catch all the errors.
     *
     * Furthermore, the presence of BBlanks means that "" is technically a valid name.
     * BUT, this name will never be parsed.
     *)
    List.fold_left
      (fun (let_env, non_shadowed_ids, exns) (bind, body, _) ->
        let new_env = bind_name bind :: let_env in
        let non_shadowable =
          match bind with
          | BName (name, shadowable, loc) ->
              if shadowable then
                non_shadowed_ids
              else
                (name, loc) :: non_shadowed_ids
          | _ -> non_shadowed_ids
        in
        ( new_env,
          non_shadowable,
          wf_E body
            ( if is_rec then
                new_env
              else
                let_env )
            non_shadowable_ids decl_env
          @ ( match bind with
            | BName (name, _, loc2) -> (
              match List.assoc_opt name non_shadowed_ids with
              | Some loc1 -> [ShadowId (name, loc1, loc2)]
              | _ -> [] )
            | _ -> [] )
          @ exns ) )
      (id_env, non_shadowable_ids, [])
      (List.concat_map un_nest_binding bindings)
  (* END EXPR CHECKS *)
  (* BEGIN DECL CHECKS *)
  (* Check for duplicate function names *)
  and check_dup_fnames ds _ =
    List.fold_left
      (fun (seen, exns) (DFun (fname, _, _, loc) as d) ->
        (* Look in the environment. If the function name exists, duplicate that. *)
        let dup = find_decl seen fname in
        match dup with
        | Some (DFun (_, _, _, loc_orig)) -> (seen, DuplicateFun (fname, loc, loc_orig) :: exns)
        | None -> (d :: seen, exns) )
      ([ (* seen decls list *) ], [ (* exns list *) ])
      ds
  and check_dup_args ds _ =
    List.concat_map
      (fun (DFun (_, (args : sourcespan bind list), _, _)) ->
        (* This one has a fold _inside_ of the map, 
         * so we need to discard the irrelevant acc value earlier than the prior case. *)
        snd
          (List.fold_left
             (fun (seen, exns) (arg : sourcespan bind) ->
               let arg_name = bind_name arg in
               let arg_loc = bind_loc arg in
               match List.find_opt (fun a -> bind_eq a arg) seen with
               | Some orig_bind ->
                   (seen, DuplicateId (arg_name, arg_loc, bind_loc orig_bind) :: exns)
               | None -> (
                 (* Second check: prevent reuse of function names as arguments.
                    This is not in the spec, but foo(foo) seems weird.
                    It will only get weirder once we have first-class functions.
                 *)
                 match find_decl ds arg_name with
                 | Some (DFun (_, _, _, loc_orig)) ->
                     (seen, DuplicateId (arg_name, arg_loc, loc_orig) :: exns)
                 | None -> (arg :: seen, exns) ) )
             ([ (* binds *) ], [ (* exns *) ])
             (List.concat_map un_nest_bind args) ) )
      ds
  (* END DECL CHECKS *)
  (* `nsis` => "Non-Shadowable Ids" *)
  and wf_E
      (e : sourcespan expr)
      (id_env : string list)
      (nsis : sourcespan envt)
      (decl_env : (string * int) list) : exn list =
    match e with
    | EBool _ -> []
    | ENumber (n, loc) ->
        (* Handle static overflow! *)
        if n > Int64.div Int64.max_int 2L || n < Int64.div Int64.min_int 2L then
          [Overflow (n, loc)]
        else
          []
    | EId (x, loc) ->
        if find_one id_env x then
          []
        else
          [UnboundId (x, loc)]
    | EPrim1 (_, e, _) -> wf_E e id_env nsis decl_env
    | EPrim2 (_, l, r, _) -> wf_E l id_env nsis decl_env @ wf_E r id_env nsis decl_env
    | EIf (c, t, f, _) ->
        wf_E c id_env nsis decl_env @ wf_E t id_env nsis decl_env @ wf_E f id_env nsis decl_env
    | ELet (bindings, body, _) ->
        let _, dup_bind_exns = check_dup_binding bindings body in
        let _, new_nsis, bind_body_exns = check_scope bindings body id_env nsis decl_env false in
        (* Pass 3: Check scope in the let body *)
        let let_body_exns =
          wf_E body
            ( List.map
                (fun (bind, _, _) -> bind_name bind)
                (List.concat_map un_nest_binding bindings)
            @ id_env )
            new_nsis decl_env
        in
        dup_bind_exns @ bind_body_exns @ let_body_exns
    | EApp (fval, args, _, _) ->
        wf_E fval id_env nsis decl_env
        @ List.concat_map (fun arg -> wf_E arg id_env nsis decl_env) args
    | ESeq (l, r, _) -> wf_E l id_env nsis decl_env @ wf_E r id_env nsis decl_env
    | ETuple (items, _) -> List.concat_map (fun x -> wf_E x id_env nsis decl_env) items
    | EGetItem (tup, idx, _) -> wf_E tup id_env nsis decl_env @ wf_E idx id_env nsis decl_env
    | ESetItem (tup, idx, value, _) ->
        wf_E tup id_env nsis decl_env
        @ wf_E idx id_env nsis decl_env
        @ wf_E value id_env nsis decl_env
    | ENil _ -> []
    | ELambda (binds, body, tag) ->
        (* This is a hack to let us reuse the bindings for these checks *)
        let hacked_bindings : 'a binding list =
          List.map (fun bind -> (bind, ENil tag, tag)) binds
        in
        let _, dup_bind_exns = check_dup_binding hacked_bindings body in
        let _, new_nsis, bind_body_exns =
          check_scope hacked_bindings body id_env nsis decl_env false
        in
        (* Pass 3: Check scope in the let body *)
        let let_body_exns =
          wf_E body
            ( List.map
                (fun (bind, _, _) -> bind_name bind)
                (List.concat_map un_nest_binding hacked_bindings)
            @ id_env )
            new_nsis decl_env
        in
        dup_bind_exns @ bind_body_exns @ let_body_exns
    | ELetRec (bindings, body, _) ->
        let _, dup_bind_exns = check_dup_binding bindings body in
        let _, new_nsis, bind_body_exns = check_scope bindings body id_env nsis decl_env true in
        (* Pass 3: Check scope in the let body *)
        let let_body_exns =
          wf_E body
            ( List.map
                (fun (bind, _, _) -> bind_name bind)
                (List.concat_map un_nest_binding bindings)
            @ id_env )
            new_nsis decl_env
        in
        dup_bind_exns @ bind_body_exns @ let_body_exns
  and wf_D (ds : 'a decl list) (decl_env : (string * int) list) : exn list =
    (* Pass 1: *)
    let _, dup_fname_exns = check_dup_fnames ds decl_env in
    let dup_arg_exns = check_dup_args ds decl_env in
    (* Pass 2: *)
    (* Check well-formedness of all decl bodies, using the decl environment. *)
    let decl_body_exns =
      List.concat_map
        (fun (DFun (_, args, body, _)) ->
          let all_args = List.concat_map un_nest_bind args in
          let all_arg_names = List.map bind_name all_args in
          let non_shadowable_args =
            List.concat_map
              (fun bind ->
                match bind with
                | BName (name, false, loc) -> [(name, loc)]
                | _ -> [] )
              all_args
          in
          wf_E body all_arg_names non_shadowable_args decl_env )
        ds
    in
    dup_fname_exns @ dup_arg_exns @ decl_body_exns
  in
  match p with
  | Program (declss, body, _) -> (
      let decl_envs = List.map get_decl_env declss in
      let decls_results = List.map2 (fun decls decl_env -> wf_D decls decl_env) declss decl_envs in
      let body_result = wf_E body [] [] (List.concat decl_envs) in
      let total_errors = List.concat decls_results @ body_result in
      match total_errors with
      | [] -> Ok p
      | _ -> Error total_errors )
;;

(* Convert a Let with multiple bindings into multiple Lets with one binding. *)
(* INVARIANT: All `ELet`s have a single binding. *)
let simplify_multi_bindings (Program ((declss : 'a decl list list), (body : 'a expr), (a : 'a))) :
    'a program =
  let rec helpE e =
    match e with
    (* Avoid making a new Let if there are no bindings *)
    | ELet (_ :: [], _, _) -> e
    | ELet (binding :: rest_bindings, body, a) ->
        ELet ([binding], helpE (ELet (rest_bindings, body, a)), a)
    | EPrim1 (op, e, a) -> EPrim1 (op, helpE e, a)
    | EPrim2 (op, e1, e2, a) -> EPrim2 (op, helpE e1, helpE e2, a)
    | ETuple (items, a) -> ETuple (List.map helpE items, a)
    | EGetItem (t, e, a) -> EGetItem (helpE t, helpE e, a)
    | ESetItem (t, e, v, a) -> ESetItem (helpE t, helpE e, helpE v, a)
    | EIf (c, t, e, a) -> EIf (helpE c, helpE t, helpE e, a)
    | EApp (n, args, c, a) -> EApp (n, List.map helpE args, c, a)
    | _ -> e
  in
  let helpD d =
    match d with
    | DFun (fname, args, body, a) -> DFun (fname, args, helpE body, a)
  in
  Program (List.map (List.map helpD) declss, helpE body, a)
;;

(* Let's make this global. *)
let make_gensym _ =
  let next = ref 0 in
  fun name ->
    next := !next + 1;
    sprintf "%s#%d" name !next
;;

(* Convert Tuple bindings in `Let`s into multiple regular bindings. *)
(* This pass has to happen before other passes, because we introduce new bindings. *)
(* INVARIANT: No `ELet` contains a `BTuple` *)
let simplify_tuple_bindings (Program ((declss : 'a decl list list), (body : 'a expr), (a : 'a))) :
    'a program =
  let gensym = make_gensym () in
  let rec help_bind ((bind, bound, _) as binding) : 'a binding list =
    match bind with
    | BTuple (sub_binds, alpha) ->
        let temp_name = gensym "temp_tuple_name" in
        let temp_id = EId (temp_name, alpha) in
        (* Check for shadow (later) *)
        (BName (temp_name, false, alpha), bound, alpha)
        :: List.concat
             (List.mapi
                (fun i sub_bind ->
                  let indexer = ENumber (Int64.of_int i, alpha) in
                  match sub_bind with
                  | BName _ | BBlank _ -> [(sub_bind, EGetItem (temp_id, indexer, alpha), alpha)]
                  | BTuple _ -> help_bind (sub_bind, EGetItem (temp_id, indexer, alpha), alpha) )
                sub_binds )
    | _ -> [binding]
  in
  let rec helpE e =
    match e with
    (* Avoid making a new Let if there are no bindings *)
    | ELet ([], _, _) -> e
    | ELet (bindings, body, a) ->
        ELet (List.concat_map (fun binding -> help_bind binding) bindings, helpE body, a)
    | EPrim1 (op, e, a) -> EPrim1 (op, helpE e, a)
    | EPrim2 (op, e1, e2, a) -> EPrim2 (op, helpE e1, helpE e2, a)
    | ETuple (items, a) -> ETuple (List.map helpE items, a)
    | EGetItem (t, e, a) -> EGetItem (helpE t, helpE e, a)
    | ESetItem (t, e, v, a) -> ESetItem (helpE t, helpE e, helpE v, a)
    | EIf (c, t, e, a) -> EIf (helpE c, helpE t, helpE e, a)
    | EApp (n, args, c, a) -> EApp (n, List.map helpE args, c, a)
    | _ -> e
  in
  let helpD d =
    match d with
    | DFun (fname, args, body, a) ->
        let desugared_args, context =
          List.split
            (List.map
               (fun arg ->
                 match arg with
                 | BBlank _ | BName _ -> (arg, [])
                 | BTuple (sub_args, a) ->
                     let temp_name = gensym "temp_arg" in
                     let new_bind = BName (temp_name, false, a) in
                     let new_id = EId (temp_name, a) in
                     (new_bind, help_bind (arg, new_id, a)) )
               args )
        in
        let bindings = List.concat context in
        let new_body =
          if List.length bindings > 0 then
            ELet (List.concat_map help_bind bindings, helpE body, a)
          else
            helpE body
        in
        DFun (fname, desugared_args, new_body, a)
  in
  Program (List.map (List.map helpD) declss, helpE body, a)
;;

(* Converts all `ESeq`s to `ELet`s. *)
(* INVARIANT: There are no `ESeq`s in the resulting program. *)
let seq_to_let (Program ((declss : 'a decl list list), (body : 'a expr), (a : 'a))) : 'a program =
  let rec helpE e : 'a expr =
    match e with
    | ESeq (e1, e2, a) -> ELet ([(BBlank a, e1, a)], helpE e2, a)
    | EPrim1 (op, e, a) -> EPrim1 (op, helpE e, a)
    | EPrim2 (op, e1, e2, a) -> EPrim2 (op, helpE e1, helpE e2, a)
    | ETuple (items, a) -> ETuple (List.map helpE items, a)
    | EGetItem (t, e, a) -> EGetItem (helpE t, helpE e, a)
    | ESetItem (t, e, v, a) -> ESetItem (helpE t, helpE e, helpE v, a)
    | ELet (bindings, body, a) ->
        let desugared_bindings =
          List.map (fun (bind, bound, a) -> (bind, helpE bound, a)) bindings
        in
        ELet (desugared_bindings, helpE body, a)
    | EIf (c, t, e, a) -> EIf (helpE c, helpE t, helpE e, a)
    | EApp (n, args, c, a) -> EApp (n, List.map helpE args, c, a)
    | _ -> e
  in
  let helpD d =
    match d with
    | DFun (fname, args, body, a) -> DFun (fname, args, helpE body, a)
  in
  Program (List.map (List.map helpD) declss, helpE body, a)
;;

(* Convert all Blank bindings into mangled ids. *)
(* ASSUME: No BTuple bindings *)
(* INVARIANT: All bindings are solely BNames. *)
let eliminate_blank_bindings (Program ((declss : 'a decl list list), (body : 'a expr), (a : 'a))) :
    'a program =
  let gensym = make_gensym () in
  let rec helpE e =
    match e with
    (* Avoid making a new Let if there are no bindings *)
    | ELet ([], _, _) -> e
    | ELet (bindings, body, a) ->
        ELet
          ( List.map
              (fun ((bind, bound, alpha) as binding) ->
                match bind with
                (* Look here for shadow-able *)
                | BBlank _ -> (BName (gensym "blank", false, alpha), bound, alpha)
                | BName _ -> binding
                | BTuple _ -> raise (InternalCompilerError "Expected no BTuples at this point") )
              bindings,
            helpE body,
            a )
    | EPrim1 (op, e, a) -> EPrim1 (op, helpE e, a)
    | EPrim2 (op, e1, e2, a) -> EPrim2 (op, helpE e1, helpE e2, a)
    | ETuple (items, a) -> ETuple (List.map helpE items, a)
    | EGetItem (t, e, a) -> EGetItem (helpE t, helpE e, a)
    | ESetItem (t, e, v, a) -> ESetItem (helpE t, helpE e, helpE v, a)
    | EIf (c, t, e, a) -> EIf (helpE c, helpE t, helpE e, a)
    | EApp (n, args, c, a) -> EApp (n, List.map helpE args, c, a)
    | _ -> e
  in
  let helpD d =
    match d with
    | DFun (fname, args, body, a) ->
        let processed_args =
          List.map
            (fun arg ->
              match arg with
              (* Look here for shadow-able *)
              | BBlank tag -> BName (gensym "blank", false, tag)
              | BName _ -> arg
              | BTuple _ -> raise (InternalCompilerError "Expected no BTuples at this point") )
            args
        in
        DFun (fname, processed_args, helpE body, a)
  in
  Program (List.map (List.map helpD) declss, helpE body, a)
;;

type funenvt = call_type envt

let initial_fun_env : funenvt =
  [ (* call_types indicate whether a given function is implemented by something in the runtime,
       as a snake function, as a primop (in case that's useful), or just unknown so far *)
    ("print", Prim);
    ("input", Native);
    ("equal", Native) ]
;;

(* Convert each EApp to the appropriate type, using initial_fun_envt. *)
(* ASSUME: All EApps are unknown. *)
(* INVARIANT: No EApp is unknown. *)
let annotate_call_types (Program ((declss : 'a decl list list), (body : 'a expr), (a : 'a))) :
    'a program =
  let rec helpE e =
    match e with
    | EApp (fval, args, _, a) -> (
      match fval with
      (* This case matches for ID application x(1) *)
      | EId (fname, _) -> (
        match List.assoc_opt fname initial_fun_env with
        (* TODO: We can add name filters for Prims. *)
        | Some ctype -> EApp (fval, args, ctype, a)
        | None -> EApp (fval, args, Snake, a) )
      (* This is application of a literal, i.e. `((fun x -> x + 1) 5)` *)
      | _ -> EApp (fval, args, Snake, a) )
    | EPrim1 (op, e, a) -> EPrim1 (op, helpE e, a)
    | EPrim2 (op, e1, e2, a) -> EPrim2 (op, helpE e1, helpE e2, a)
    | ETuple (items, a) -> ETuple (List.map helpE items, a)
    | EGetItem (t, e, a) -> EGetItem (helpE t, helpE e, a)
    | ESetItem (t, e, v, a) -> ESetItem (helpE t, helpE e, helpE v, a)
    | EIf (c, t, e, a) -> EIf (helpE c, helpE t, helpE e, a)
    | ELet (bindings, body, a) ->
        ELet (List.map (fun (b, e, a) -> (b, helpE e, a)) bindings, helpE body, a)
    | _ -> e
  and helpD (DFun (name, args, body, a)) = DFun (name, args, helpE body, a) in
  Program (List.map (List.map helpD) declss, helpE body, a)
;;

(* Eliminate all of the decls by converting them to LetRecs *)
(* ASSUME: is_well_formed confirmed there are no inter-decls calls *)
(* INVARIANT: program decls becomes [] *)
let elim_declss (Program ((declss : 'a decl list list), (prog_body : 'a expr), (a : 'a))) :
    'a program =
  let decl_to_binding (DFun (name, binds, decl_body, tag)) : 'a binding =
    (BName (name, false, tag), ELambda (binds, decl_body, tag), tag)
  in
  Program
    ( [],
      List.fold_left
        (fun (acc : 'a expr) (decls : 'a decl list) ->
          ELetRec (List.map decl_to_binding decls, acc, a) )
        prog_body declss,
      a )
;;

let desugar (p : 'a program) : 'a program =
  p
  |> seq_to_let (* Introduces blank bindings, so must precede their elimination. *)
  |> simplify_tuple_bindings (* Removes nested binds, making some following phases simpler.*)
  |> eliminate_blank_bindings
  |> simplify_multi_bindings
  |> annotate_call_types
  |> elim_declss
;;

let remove_dups (lst : 'a list) : 'a list =
  List.fold_right
    (fun x acc ->
      if List.exists (fun e -> fst e = fst x) acc then
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
  helpA e []
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
         *)
        let args_env = List.mapi (fun index id -> (id, RegOffset (index + 2, RBP))) ids in
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
  (prog, remove_dups body_env)
;;

let rec compile_fun (fun_name : string) args body env : instruction list =
  raise (NotYetImplemented "Compile funs not yet implemented")

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
  | ImmNil _ -> raise (NotYetImplemented "Finish this")
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
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase locate_bindings naive_stack_allocation
  |> add_phase result compile_prog
;;
