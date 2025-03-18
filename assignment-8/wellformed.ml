open Errors
open Exprs
open Phases
open Printf

let bind_eq b1 b2 =
  match b1 with
  | BBlank _ -> false (* Blank is not equal to anything, including itself. *)
  | BTuple _ -> false (* Tuples need to be unrolled before comparing. *)
  | BName (name1, _, _) -> (
    match b2 with
    | BName (name2, _, _) -> name1 = name2
    | _ -> false )
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

let rec find_decl (ds : 'a decl list) (name : string) : 'a decl option =
  match ds with
  | [] -> None
  | (DFun (fname, _, _, _) as d) :: ds_rest ->
      if name = fname then
        Some d
      else
        find_decl ds_rest name
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