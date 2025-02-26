open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors

type 'a envt = (string * 'a) list

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

let tuple_tag = 0x0000000000000001L

let tuple_tag_mask = 0x0000000000000007L

let nil_tag = tuple_tag

let nil_tag_mask = 0x1111111111111111L

let err_COMP_NOT_NUM = 1L

let err_ARITH_NOT_NUM = 2L

let err_LOGIC_NOT_BOOL = 3L

let err_IF_NOT_BOOL = 4L

let err_OVERFLOW = 5L

let err_ACCESS_NOT_TUPLE = 6L

let err_GET_LOW_INDEX = 7L

let err_GET_HIGH_INDEX = 8L

let err_INDEX_NOT_NUM = 9L

let err_NIL_DEREF = 10L

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

let heap_reg = R15

let scratch_reg = R11

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

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

let word_size = 8

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

let rec find_opt ls x =
  match ls with
  | [] -> None
  | (y, v) :: rest ->
      if y = x then
        Some v
      else
        find_opt rest x
;;

let count_vars e =
  let rec helpA e =
    match e with
    | ALet (_, bind, body, _) -> 1 + max (helpC bind) (helpA body)
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

let rec find_one (l : 'a list) (elt : 'a) (comp : 'a -> 'a -> bool) : bool =
  match l with
  | [] -> false
  | x :: xs -> elt = x || find_one xs elt comp
;;

(* let rec find_dup (l : 'a list) : 'a option =
     match l with
     | [] | [_] -> None
     | x :: xs ->
         if find_one xs x then
           Some x
         else
           find_dup xs
   ;; *)

type funenvt = call_type envt

let initial_fun_env : funenvt =
  [ (* call_types indicate whether a given function is implemented by something in the runtime,
       as a snake function, as a primop (in case that's useful), or just unknown so far *) ]
;;

let rename_and_tag (p : tag program) : tag program =
  let rec rename (env : string envt) p =
    match p with
    | Program (decls, body, tag) ->
        let rec addToEnv funenv decl =
          match decl with
          | DFun (name, _, _, _) -> (name, Snake) :: funenv
        in
        let initial_funenv = List.map (fun (name, ct) -> (name, ct)) initial_fun_env in
        let funenv = List.fold_left addToEnv initial_funenv decls in
        Program (List.map (helpD funenv env) decls, helpE funenv env body, tag)
  and helpD funenv env decl =
    match decl with
    | DFun (name, args, body, tag) ->
        let newArgs, env' = helpBS env args in
        DFun (name, newArgs, helpE funenv env' body, tag)
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
  and helpBG funenv env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a) :: bindings ->
        let b', env' = helpB env b in
        let e' = helpE funenv env e in
        let bindings', env'' = helpBG funenv env' bindings in
        ((b', e', a) :: bindings', env'')
  and helpE funenv env e =
    match e with
    | ESeq (e1, e2, tag) -> ESeq (helpE funenv env e1, helpE funenv env e2, tag)
    | ETuple (es, tag) -> ETuple (List.map (helpE funenv env) es, tag)
    | EGetItem (e, idx, tag) -> EGetItem (helpE funenv env e, helpE funenv env idx, tag)
    | ESetItem (e, idx, newval, tag) ->
        ESetItem (helpE funenv env e, helpE funenv env idx, helpE funenv env newval, tag)
    | EPrim1 (op, arg, tag) -> EPrim1 (op, helpE funenv env arg, tag)
    | EPrim2 (op, left, right, tag) ->
        EPrim2 (op, helpE funenv env left, helpE funenv env right, tag)
    | EIf (c, t, f, tag) -> EIf (helpE funenv env c, helpE funenv env t, helpE funenv env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId (name, tag) -> ( try EId (find env name, tag) with Not_found -> e )
    | EApp (name, args, native, tag) ->
        let call_type =
          match find_opt funenv name with
          | None -> native
          | Some ct -> ct
        in
        EApp (name, List.map (helpE funenv env) args, call_type, tag)
    | ELet (binds, body, tag) ->
        let binds', env' = helpBG funenv env binds in
        let body' = helpE funenv env' body in
        ELet (binds', body', tag)
  in
  rename [] p
;;

(* Returns the stack-index (in words) of the deepest stack index used for any
   of the variables in this expression *)
let deepest_stack e env =
  let rec helpA e =
    match e with
    | ALet (name, bind, body, _) ->
        List.fold_left max 0 [name_to_offset name; helpC bind; helpA body]
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (c, t, f, _) -> List.fold_left max 0 [helpI c; helpA t; helpA f]
    | CPrim1 (_, i, _) -> helpI i
    | CPrim2 (_, i1, i2, _) -> max (helpI i1) (helpI i2)
    | CApp (_, args, _, _) -> List.fold_left max 0 (List.map helpI args)
    | CTuple (elms, _) -> List.fold_left max 0 (List.map helpI elms)
    | CGetItem (tup, idx, _) -> max (helpI tup) (helpI idx)
    | CSetItem (tup, idx, newval, _) -> List.fold_left max 0 [helpI tup; helpI idx; helpI newval]
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmNil _ -> 0
    | ImmId (name, _) -> name_to_offset name
  and name_to_offset name =
    match find env name with
    | RegOffset (words, RBP) -> words / -1 (* negative because stack direction *)
    | _ -> 0
  in
  max (helpA e) 0 (* if only parameters are used, helpA might return a negative value *)
;;

(* IMPLEMENT EVERYTHING BELOW *)

(* Convert a Let with multiple bindings into multiple Lets with one binding. *)
(* INVARIANT: All `ELet`s have a single binding. *)
let simplify_multi_bindings (Program ((decls : 'a decl list), (body : 'a expr), (a : 'a))) :
    'a program =
  let rec helpE e =
    match e with
    (* Avoid making a new Let if there are no bindings *)
    | ELet (_ :: [], _, _) -> e
    | ELet (binding :: rest_bindings, body, a) ->
        ELet ([binding], helpE (ELet (rest_bindings, body, a)), a)
    | _ -> e
  in
  let helpD d =
    match d with
    | DFun (fname, args, body, a) -> DFun (fname, args, helpE body, a)
  in
  Program (List.map helpD decls, helpE body, a)
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
let simplify_tuple_bindings (Program ((decls : 'a decl list), (body : 'a expr), (a : 'a))) :
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
            ELet (bindings, helpE body, a)
          else
            helpE body
        in
        DFun (fname, desugared_args, new_body, a)
  in
  Program (List.map helpD decls, helpE body, a)
;;

(* Converts all `ESeq`s to `ELet`s. *)
(* INVARIANT: There are no `ESeq`s in the resulting program. *)
let seq_to_let (Program ((decls : 'a decl list), (body : 'a expr), (a : 'a))) : 'a program =
  let rec helpE e =
    match e with
    | ESeq (e1, e2, alpha) -> ELet ([(BBlank alpha, e1, alpha)], e2, alpha)
    | _ -> e
  in
  let helpD d =
    match d with
    | DFun (fname, args, body, a) -> DFun (fname, args, helpE body, a)
  in
  Program (List.map helpD decls, helpE body, a)
;;

(* Convert all Blank bindings into mangled ids. *)
(* ASSUME: No BTuple bindings *)
(* INVARIANT: All bindings are solely BNames. *)
let eliminate_blank_bindings (Program ((decls : 'a decl list), (body : 'a expr), (a : 'a))) :
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
  Program (List.map helpD decls, helpE body, a)
;;

let desugar (p : 'a program) : 'a program =
  p
  |> seq_to_let (* Introduces blank bindings, so must precede their elimination. *)
  |> simplify_tuple_bindings (* Removes nested binds, making some following phases simpler.*)
  |> eliminate_blank_bindings
  |> simplify_multi_bindings
;;

(* Happens last, once new bindings will no longer be created. *)
(* TODO: New phases for Eprim1/2 -> EApp? *)

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program (decls, body, _) -> AProgram (List.map helpD decls, helpA body, ())
  and helpD (d : tag decl) : unit adecl =
    match d with
    | DFun (name, args, body, _) ->
        let args =
          List.map
            (fun a ->
              match a with
              | BName (a, _, _) -> a
              | _ -> raise (InternalCompilerError "Expected only BNames at this stage.") )
            args
        in
        ADFun (name, args, helpA body, ())
  and helpC (e : tag expr) : unit cexpr * (string * unit cexpr) list =
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
    | ELet ((bind, exp, _) :: rest, body, pos) -> (
      match bind with
      | BName (id, _, _) ->
          let exp_ans, exp_setup = helpC exp in
          let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
          (body_ans, exp_setup @ [(id, exp_ans)] @ body_setup)
      | _ -> raise (InternalCompilerError "Expected only BNames at this stage.") )
    | EApp (funname, args, ct, _) ->
        let new_args, new_setup = List.split (List.map helpI args) in
        (CApp (funname, new_args, ct, ()), List.concat new_setup)
    (* NOTE: You may need more cases here, for sequences and tuples *)
    | ESeq _ -> raise (InternalCompilerError "We do not have sequences at this stage.")
    | ETuple (exprs, _) ->
        let imm_exprs, exprs_setup = List.split (List.map helpI exprs) in
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
    | _ ->
        let imm, setup = helpI e in
        (CImmExpr imm, setup)
  and helpI (e : tag expr) : unit immexpr * (string * unit cexpr) list =
    match e with
    | ENumber (n, _) -> (ImmNum (n, ()), [])
    | EBool (b, _) -> (ImmBool (b, ()), [])
    | EId (name, _) -> (ImmId (name, ()), [])
    | EPrim1 (op, arg, tag) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (ImmId (tmp, ()), arg_setup @ [(tmp, CPrim1 (op, arg_imm, ()))])
    | EPrim2 (op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (ImmId (tmp, ()), left_setup @ right_setup @ [(tmp, CPrim2 (op, left_imm, right_imm, ()))])
    | EIf (cond, _then, _else, tag) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        (ImmId (tmp, ()), cond_setup @ [(tmp, CIf (cond_imm, helpA _then, helpA _else, ()))])
    | EApp (funname, args, ct, tag) ->
        let tmp = sprintf "app_%d" tag in
        let new_args, new_setup = List.split (List.map helpI args) in
        (ImmId (tmp, ()), List.concat new_setup @ [(tmp, CApp (funname, new_args, ct, ()))])
    | ELet ([], body, _) -> helpI body
    | ELet ((bind, exp, _) :: rest, body, pos) -> (
      match bind with
      | BName (id, _, _) ->
          let exp_ans, exp_setup = helpC exp in
          let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
          (body_ans, exp_setup @ [(id, exp_ans)] @ body_setup)
      | _ -> raise (InternalCompilerError "Expected only BNames at this stage.") )
    | ESeq _ -> raise (InternalCompilerError "We do not have sequences at this stage.")
    | ETuple (exprs, tag) ->
        let tmp = sprintf "tuple_%d" tag in
        let imm_exprs, exprs_setup = List.split (List.map helpI exprs) in
        (ImmId (tmp, ()), List.concat exprs_setup @ [(tmp, CTuple (imm_exprs, ()))])
    | EGetItem (tuple, index, tag) ->
        let tmp = sprintf "getItem_%d" tag in
        let imm_tuple, tuple_setup = helpI tuple in
        let imm_index, index_setup = helpI index in
        (ImmId (tmp, ()), tuple_setup @ index_setup @ [(tmp, CGetItem (imm_tuple, imm_index, ()))])
    | ESetItem (tuple, index, new_val, tag) ->
        let tmp = sprintf "setItem_%d" tag in
        let imm_tuple, tuple_setup = helpI tuple in
        let imm_index, index_setup = helpI index in
        let imm_val, val_setup = helpI new_val in
        ( ImmId (tmp, ()),
          tuple_setup @ index_setup @ val_setup
          @ [(tmp, CSetItem (imm_tuple, imm_index, imm_val, ()))] )
    | ENil _ -> (ImmNil (), [])
  and helpA e : unit aexpr =
    let ans, ans_setup = helpC e in
    List.fold_right (fun (bind, exp) body -> ALet (bind, exp, body, ())) ans_setup (ACExpr ans)
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
  and check_scope (bindings : 'a binding list) _ id_env decl_env =
    (* Each bound body is allowed to use the names of all previous, bindings 
     * Note that this is a little weird for tuple bindings:
     * Since we check for each sub-binding individually against the same body,
     * we rely on the first sub-binding to catch all the errors.
     *
     * Furthermore, the presence of BBlanks means that "" is technically a valid name.
     * BUT, this name will never be parsed.
     *)
    List.fold_left
      (fun (let_env, exns) (bind, body, _) ->
        (bind_name bind :: let_env, wf_E body let_env decl_env @ exns) )
      (id_env, [])
      (List.concat_map un_nest_binding bindings)
  and check_fun_errors funname args loc decl_env =
    let unbound_fun_error =
      if find_one (fst @@ List.split @@ decl_env) funname ( = ) then
        []
      else
        [UnboundFun (funname, loc)]
    in
    if unbound_fun_error = [] then
      (* We made sure that the function name is in the `decl_env` above, so `List.assoc` will not error *)
      let expected_arity = List.assoc funname decl_env in
      let given_arity = List.length args in
      if given_arity = expected_arity then
        []
      else
        [Arity (expected_arity, given_arity, loc)]
    else
      []
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
  and wf_E (e : sourcespan expr) (id_env : string list) (decl_env : (string * int) list) : exn list
      =
    match e with
    | EBool _ -> []
    | ENumber (n, loc) ->
        (* Handle static overflow! *)
        if n > Int64.div Int64.max_int 2L || n < Int64.div Int64.min_int 2L then
          [Overflow (n, loc)]
        else
          []
    | EId (x, loc) ->
        if find_one id_env x ( = ) then
          []
        else
          [UnboundId (x, loc)]
    | EPrim1 (_, e, _) -> wf_E e id_env decl_env
    | EPrim2 (_, l, r, _) -> wf_E l id_env decl_env @ wf_E r id_env decl_env
    | EIf (c, t, f, _) -> wf_E c id_env decl_env @ wf_E t id_env decl_env @ wf_E f id_env decl_env
    | ELet (bindings, body, _) ->
        let _, dup_bind_exns = check_dup_binding bindings body in
        let _, bind_body_exns = check_scope bindings body id_env decl_env in
        (* Pass 3: Check scope in the let body *)
        let let_body_exns =
          wf_E body
            ( List.map
                (fun (bind, _, _) -> bind_name bind)
                (List.concat_map un_nest_binding bindings)
            @ id_env )
            decl_env
        in
        dup_bind_exns @ bind_body_exns @ let_body_exns
    | EApp (funname, args, _, loc) -> check_fun_errors funname args loc decl_env
    | ESeq (l, r, _) -> wf_E l id_env decl_env @ wf_E r id_env decl_env
    | ETuple (items, _) -> List.concat_map (fun x -> wf_E x id_env decl_env) items
    | EGetItem (tup, idx, _) -> wf_E tup id_env decl_env @ wf_E idx id_env decl_env
    | ESetItem (tup, idx, value, _) ->
        wf_E tup id_env decl_env @ wf_E idx id_env decl_env @ wf_E value id_env decl_env
    | ENil _ -> []
  and wf_D (ds : 'a decl list) (decl_env : (string * int) list) : exn list =
    (* Pass 1: *)
    let _, dup_fname_exns = check_dup_fnames ds decl_env in
    let dup_arg_exns = check_dup_args ds decl_env in
    (* Pass 2: *)
    (* Check well-formedness of all decl bodies, using the decl environment. *)
    let decl_body_exns =
      List.concat_map
        (fun (DFun (_, args, body, _)) ->
          wf_E body (List.map bind_name (List.concat_map un_nest_bind args)) decl_env )
        ds
    in
    dup_fname_exns @ dup_arg_exns @ decl_body_exns
  in
  match p with
  | Program (decls, body, _) -> (
      let decl_env = get_decl_env decls in
      let decls_result = wf_D decls decl_env in
      let body_result = wf_E body [] decl_env in
      let total_errors = decls_result @ body_result in
      match total_errors with
      | [] -> Ok p
      | _ -> Error total_errors )
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

(* Convert a stack index into a RegOffset *)
let si_to_arg (si : int) : arg = RegOffset (~-si, RBP)

let naive_stack_allocation (AProgram (decls, body, _) as prog : tag aprogram) :
    tag aprogram * arg envt =
  (* For the Xexpr helpers:
   * - Immediate values don't care about the env, so we ignore those.
   * - Cexprs are only interesting in the `CIf` case, since this case
   *   contains two Aexprs.
   * - Aexprs are where the main logic happens, since that is where we make new bindings.
       We convert the stack index to a RegOffset, then look at the bound expr, then the body.
       Note that whenever we recursively call helpA, we need to increment the stack index. 
   *
   * For Decls: 
   * - We decided to store function arguments here, to avoid doing it elsewhere.
       This is against the assignment's instructions, but it made more sense to us that way.
   *)
  let rec helpD decls env si =
    (* Every function arg is located at the same place relative to the function.
     * (i.e. either in an arg, or below RBP.)
     * Therefore, we decided to encode these in the environment as well.
     *)
    List.concat_map
      (fun (ADFun (_, args, body, _)) ->
        let body_env = helpA body env (si + 1) in
        (* Why do we need to add 2 here? *)
        (*  +0   | RBP 
         *  +1   | Return Address
         *  +2   | Argument 1
         *  ...
         *  +n+2 | Argument n
         *)
        let args_env = List.mapi (fun i a -> (a, RegOffset (i + 2, RBP))) args in
        args_env @ body_env )
      decls
  and helpC (cexp : tag cexpr) (env : arg envt) (si : int) : arg envt =
    match cexp with
    | CIf (_, thn, els, _) -> helpA thn env (si + 1) @ helpA els env (si + 1)
    | CPrim1 _ | CPrim2 _ | CApp _ | CImmExpr _ | CTuple _ | CGetItem _ | CSetItem _ -> env
  and helpA (aexp : tag aexpr) (env : arg envt) (si : int) : arg envt =
    match aexp with
    | ALet (id, bound, body, _) ->
        let offset = (id, si_to_arg si) in
        let bound_offset = helpC bound env si in
        let body_offset = helpA body env (si + 1) in
        (offset :: bound_offset) @ body_offset
    | ACExpr cexp -> helpC cexp env si
  in
  let decls_env = helpD decls [] 1 in
  let body_env = helpA body decls_env 1 in
  (* We were rather sloppy with the process of adding to the environment,
   * so we just remove the duplicates in O(n^2) time at the end.
   *)
  (prog, remove_dups body_env)
;;

(* Enforces that the value in RAX is a bool. Goes to the specified label if not. *)
(* We could check a parameterized register, but that creates complexity in reporting the error. *)
(* We opt to hard-code RAX, for more consistency in exchange for some more boiler-plate code. *)
let check_bool (goto : string) : instruction list =
  [IMov (Reg scratch_reg, HexConst num_tag_mask); ITest (Reg RAX, Reg scratch_reg); IJz goto]
;;

(* Enforces that the value in RAX is a num. Goes to the specified label if not. *)
let check_num (goto : string) : instruction list =
  [IMov (Reg scratch_reg, HexConst num_tag_mask); ITest (Reg RAX, Reg scratch_reg); IJnz goto]
;;

(* Enforces that the value in RAX is a tuple. Goes to the specified label if not. *)
let check_tuple (goto : string) : instruction list =
  [IMov (Reg scratch_reg, HexConst tuple_tag_mask); ITest (Reg RAX, Reg scratch_reg); IJz goto]
;;

(* Enforces that the value in RAX is a nil. Goes to the specified label if not. *)
let check_not_nil (goto : string) : instruction list =
  [IMov (Reg scratch_reg, HexConst nil_tag_mask); ITest (Reg RAX, Reg scratch_reg); IJz goto]
;;

let check_overflow = IJo overflow_label

(* Note: compile_cexpr helpers are directly copied from the previous assignment.  *)

(* Helper for numeric comparisons *)
let compare_prim2 (op : prim2) (e1 : arg) (e2 : arg) (t : tag) : instruction list =
  (* Move the first arg into RAX so we can type-check it. *)
  let string_op = "comparison_label" in
  let comp_label = sprintf "%s#%d" string_op t in
  let jump =
    match op with
    | Greater -> IJg comp_label
    | GreaterEq -> IJge comp_label
    | Less -> IJl comp_label
    | LessEq -> IJle comp_label
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
      IJmp comp_done_label;
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
      IJz false_label;
      IMov (Reg RAX, e2) ]
  @ check_bool not_a_bool_logic_label
  @ [ (* Need to re-set scratch_reg since it gets changed in check_bool.*)
      IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJz false_label;
      ILabel true_label;
      IMov (Reg RAX, const_true);
      IJmp logic_done_label;
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
      IJnz true_label;
      IMov (Reg RAX, e2) ]
  @ check_bool not_a_bool_logic_label
  @ [ (* Need to re-set scratch_reg since it gets changed in check_bool.*)
      IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJnz true_label;
      ILabel false_label;
      IMov (Reg RAX, const_false);
      IJmp logic_done_label;
      ILabel true_label;
      IMov (Reg RAX, const_true);
      ILabel logic_done_label;
      ILineComment (sprintf "END or#%d   -------------" t) ]
;;

let move_with_scratch arg1 arg2 = [IMov (Reg scratch_reg, arg2); IMov (arg1, Reg scratch_reg)]

(* if you think that this signature is incomplete or incorrect,
   feel free to change it as appropriate and leave a comment explaining why. *)
let rec compile_fun (fun_name : string) (args : string list) (env : arg envt) : instruction list =
  raise (NotYetImplemented "Compile funs not yet implemented")

and compile_aexpr (e : tag aexpr) (env : arg envt) (num_args : int) (is_tail : bool) :
    instruction list =
  match e with
  | ALet (id, bound, body, _) ->
      let prelude = compile_cexpr bound env num_args (* TODO: Come back to this number *) false in
      let body = compile_aexpr body env num_args (* TODO: Come back to this number *) is_tail in
      let offset = find env id in
      prelude @ [IMov (offset, Reg RAX)] @ body
  | ACExpr cexp -> compile_cexpr cexp env num_args is_tail

and compile_cexpr (e : tag cexpr) (env : arg envt) (num_args : int) (is_tail : bool) =
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
           IJz else_label;
           ILineComment "  Then case:" ]
       @ compile_aexpr thn env num_args is_tail
       @ [IJmp done_label; ILineComment "  Else case:"; ILabel else_label]
       @ compile_aexpr els env num_args is_tail )
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
          [ ILineComment (sprintf "BEGIN is_bool%d -------------" t);
            IMov (Reg RAX, e_reg);
            ITest (Reg RAX, HexConst num_tag_mask);
            IJz false_label;
            IMov (Reg RAX, const_true);
            IJmp done_label;
            ILabel false_label;
            IMov (Reg RAX, const_false);
            ILabel done_label;
            ILineComment (sprintf "END is_bool%d   -------------" t) ]
      | IsNum ->
          let false_label = sprintf "is_num_false#%d" t in
          let done_label = sprintf "is_num_done#%d" t in
          [ ILineComment (sprintf "BEGIN is_num%d -------------" t);
            IMov (Reg RAX, e_reg);
            ITest (Reg RAX, HexConst num_tag_mask);
            (* Jump not zero because this is the inverted case from is_bool *)
            IJnz false_label;
            IMov (Reg RAX, const_true);
            IJmp done_label;
            ILabel false_label;
            IMov (Reg RAX, const_false);
            ILabel done_label;
            ILineComment (sprintf "END is_num%d   -------------" t) ]
      | Print ->
          [ (* Print both passes its value to the external function, and returns it. *)
            IMov (Reg RDI, e_reg);
            ICall "print" (* The answer goes in RAX :) *) ]
      | IsTuple -> raise (NotYetImplemented "IsTuple not implemented yet")
      | PrintStack -> raise (NotYetImplemented "Fill in PrintStack here")
      (* TODO *) )
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
            IJe true_label;
            IMov (Reg RAX, const_false);
            IJmp done_label;
            ILabel true_label;
            IMov (Reg RAX, const_true);
            ILabel done_label ] )
  | CApp (fun_name, args, call_type, _) ->
      let arg_regs = List.map (fun a -> compile_imm a env) args in
      (* We need to handle our caller-save registers here, and set up the args. *)
      let m = List.length args in
      List.concat
        (List.rev_map (fun a -> [IMov (Reg scratch_reg, a); IPush (Reg scratch_reg)]) arg_regs)
      @ [ICall fun_name]
      @ [IAdd (Reg RSP, Const (Int64.of_int (8 * m)))]
  | CTuple (items, _) ->
      let n = List.length items in
      let heap_bump_amt =
        if n mod 2 == 0 then
          8L
        else
          0L
      in
      let loading_instrs =
        List.concat
        @@ List.mapi
             (fun i item -> move_with_scratch (RegOffset (i + 1, R15)) (compile_imm item env))
             items
      in
      move_with_scratch (RegOffset (0, R15)) (HexConst (Int64.of_int n))
      @ loading_instrs
      @ [ IMov (Reg RAX, Reg R15);
          IAdd (Reg RAX, Const 1L);
          IAdd (Reg R15, Const (Int64.of_int (8 * (n + 1))));
          IInstrComment (IAdd (Reg R15, Const heap_bump_amt), "0 if even args, 8 if odd") ]
  | CGetItem (tup, idx, _) ->
      let tup_reg = compile_imm tup env in
      let idx_reg = compile_imm idx env in
      [IMov (Reg RAX, idx_reg)]
      @ check_num not_a_number_index_label
      @ [IMov (Reg RAX, tup_reg)]
      @ check_tuple not_a_tuple_access_label
      @ check_not_nil nil_deref_label
      @ [ ISub (Reg RAX, Const 1L);
          IMov (Reg R11, idx_reg);
          IShr (Reg R11, Const 1L);
          ICmp (Reg R11, Const 0L);
          IJl index_low_label;
          ICmp (Reg R11, idx_reg);
          IJge index_high_label;
          IInstrComment
            (IAdd (Reg R11, Const 1L), "R11 already has n, now add 1 to account for the length");
          IInstrComment
            ( IMov (Reg RAX, RegOffsetReg (RAX, R11, 8, 0)),
              "Multiply the value in R11 by 8 with no further offset" ) ]
  | CSetItem (tup, idx, value, _) ->
      let tup_reg = compile_imm tup env in
      let idx_reg = compile_imm idx env in
      let val_reg = compile_imm value env in
      [IMov (Reg RAX, idx_reg)]
      @ check_num not_a_number_index_label
      @ [IMov (Reg RAX, tup_reg)]
      @ check_tuple not_a_tuple_access_label
      @ check_not_nil nil_deref_label
      @ [ ISub (Reg RAX, Const 1L);
          IMov (Reg R11, idx_reg);
          IShr (Reg R11, Const 1L);
          ICmp (Reg R11, Const 0L);
          IJl index_low_label;
          ICmp (Reg R11, idx_reg);
          IJge index_high_label;
          IInstrComment
            (IAdd (Reg R11, Const 1L), "R11 already has n, now add 1 to account for the length");
          IInstrComment
            ( IMov (RegOffsetReg (RAX, R11, 8, 0), val_reg),
              "Multiply the value in R11 by 8 with no further offset and put the new value in place"
            ) ]

and compile_imm e env =
  match e with
  | ImmNum (n, loc) -> HexConst n
  | ImmBool (true, _) -> const_true
  | ImmBool (false, _) -> const_false
  | ImmId (x, _) -> find env x
  | ImmNil _ -> HexConst 1L
;;

let runtime_errors =
  List.concat_map
    (fun (label, err_code) ->
      [ ILabel label;
        IMov (Reg RDI, Const err_code);
        (* We ended up ignoring this argument in main.c. *)
        IMov (Reg RSI, Reg RAX);
        ICall "error";
        IRet (* Theoretically we don't need this `ret`.*) ] )
    [ (not_a_number_comp_label, err_COMP_NOT_NUM);
      (not_a_number_arith_label, err_ARITH_NOT_NUM);
      (not_a_bool_logic_label, err_LOGIC_NOT_BOOL);
      (not_a_bool_if_label, err_IF_NOT_BOOL);
      (overflow_label, err_OVERFLOW);
      (not_a_tuple_access_label, err_ACCESS_NOT_TUPLE);
      (not_a_number_index_label, err_INDEX_NOT_NUM);
      (index_high_label, err_GET_HIGH_INDEX);
      (index_low_label, err_GET_LOW_INDEX);
      (nil_deref_label, err_NIL_DEREF) ]
;;

let compile_decl (ADFun (fname, args, body, _)) (env : arg envt) : instruction list =
  (* Step 1: Set up the stack 
   * Step 2: Map arg names to their locations in registers/on the stack
   *  -> This is handled in `compile_aexpr`.
   * Step 3: Compile the function body
   * Step 4: Clean up the stack
   *)
  let m = List.length args in
  let vars = deepest_stack body env in
  let stack_size =
    Int64.of_int
      ( 8
      *
      if vars mod 2 = 1 then
        vars + 1
      else
        vars )
  in
  let stack_setup =
    [ ILabel fname;
      ILineComment "==== Stack set-up ====";
      IPush (Reg RBP);
      IMov (Reg RBP, Reg RSP);
      ISub (Reg RSP, Const stack_size);
      ILineComment "======================" ]
  in
  let stack_cleanup =
    [ ILineComment "=== Stack clean-up ===";
      IAdd (Reg RSP, Const stack_size);
      IMov (Reg RSP, Reg RBP);
      IPop (Reg RBP);
      IRet;
      ILineComment "======================" ]
  in
  stack_setup @ compile_aexpr body env m false @ stack_cleanup
;;

let compile_prog (AProgram (decls, body, t), (env : arg envt)) : string =
  let all_decls = decls @ [ADFun ("our_code_starts_here", [], body, t)] in
  let compiled_decls = List.concat_map (fun d -> compile_decl d env) all_decls in
  let body_prologue = "section .text\nextern error\nextern print\nglobal our_code_starts_here" in
  let heap_start =
    [ ILineComment "heap start";
      IInstrComment
        ( IMov (Reg heap_reg, Reg (List.nth first_six_args_registers 0)),
          "Load heap_reg with our argument, the heap pointer" );
      IInstrComment (IAdd (Reg heap_reg, Const 15L), "Align it to the nearest multiple of 16");
      IInstrComment
        (IAnd (Reg heap_reg, HexConst 0xFFFFFFFFFFFFFFF0L), "by adding no more than 15 to it") ]
  in
  let main = to_asm (heap_start @ compiled_decls @ runtime_errors) in
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

(* Add a desugaring phase somewhere in here *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  (* Desugar to add invariants for well_formed? *)
  |> add_err_phase well_formed is_well_formed
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase locate_bindings naive_stack_allocation
  |> add_phase result compile_prog
;;
