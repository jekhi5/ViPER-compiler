open Errors
open Exprs
open Phases
open Printf

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
                 | BTuple (_, a) ->
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
  (* |> seq_to_let  Introduces blank bindings, so must precede their elimination. *)
  (* Disabled for now, since we should handle this in ANF. *)
  |> simplify_tuple_bindings (* Removes nested binds, making some following phases simpler.*)
  |> eliminate_blank_bindings
  |> simplify_multi_bindings
  |> annotate_call_types
  |> elim_declss
;;