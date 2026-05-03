open Compile_constants
open Exprs

let u = StringSet.union

let d = StringSet.diff

let free_vars (e : 'a aexpr) : StringSet.t =
  let rec helpI (e : 'a immexpr) (bound_ids : StringSet.t) : StringSet.t =
    match e with
    | ImmId (id, _) when not (StringSet.mem id bound_ids) -> StringSet.singleton id
    | _ -> StringSet.empty
  and helpC (e : 'a cexpr) (bound_ids : StringSet.t) : StringSet.t =
    match e with
    | CIf (cond, thn, els, _) ->
        helpI cond bound_ids |> u (helpA thn bound_ids) |> u (helpA els bound_ids)
    | CPrim1 (_, expr, _) -> helpI expr bound_ids
    | CPrim2 (_, left, right, _) -> helpI left bound_ids |> u (helpI right bound_ids)
    | CApp (func, args, _, _) ->
        helpI func bound_ids
        |> u (List.fold_left (fun set arg -> helpI arg bound_ids |> u set) StringSet.empty args)
    | CImmExpr expr -> helpI expr bound_ids
    | CTuple (args, _) ->
        List.fold_left (fun set arg -> helpI arg bound_ids |> u set) StringSet.empty args
    | CGetItem (tup, idx, _) -> helpI tup bound_ids |> u (helpI idx bound_ids)
    | CSetItem (tup, idx, new_elem, _) ->
        helpI tup bound_ids |> u (helpI idx bound_ids) |> u (helpI new_elem bound_ids)
    | CLambda (ids, body, _) -> helpA body (StringSet.of_list ids |> u bound_ids)
    | CTryCatch (t, _, c, _) -> helpI t bound_ids |> u (helpI c bound_ids)
    | CCheck (checks, _) ->
        List.fold_left (fun set check -> helpI check bound_ids |> u set) StringSet.empty checks
    | CTestOp1 (e1, e2, _, _) -> helpI e1 bound_ids |> u (helpI e2 bound_ids)
    | CTestOp2 (e1, e2, _, _, _) -> helpI e1 bound_ids |> u (helpI e2 bound_ids)
    | CTestOp2Pred (e1, e2, pred, _, _) ->
        helpI e1 bound_ids |> u (helpI e2 bound_ids) |> u (helpI pred bound_ids)
  and helpA (e : 'a aexpr) (bound_ids : StringSet.t) : StringSet.t =
    match e with
    | ASeq (first, next, _) -> helpC first bound_ids |> u (helpA next bound_ids)
    | ALet (name, bound, body, _) ->
        helpC bound bound_ids |> u (helpA body (StringSet.add name bound_ids))
    | ALetRec (binds, body, _) ->
        let declared, free =
          List.fold_left
            (fun (declared, free) (name, cexpr) ->
              (StringSet.add name declared, helpC cexpr (StringSet.add name declared) |> u free) )
            (bound_ids, StringSet.empty) binds
        in
        helpA body declared |> u free
    | ACExpr cexpr -> helpC cexpr bound_ids
  in
  helpA e StringSet.empty
;;

let free_vars_cache (AProgram (body, _) : 'a aprogram) : freevars aprogram =
  let empty = StringSet.empty in
  let rec helpI (e : 'a immexpr) : StringSet.t immexpr * StringSet.t =
    match e with
    (* FV[x] = {x} *)
    | ImmId (id, _) -> (ImmId (id, StringSet.singleton id), StringSet.singleton id)
    (* FV[num] = {} *)
    | ImmNum (n, _) -> (ImmNum (n, empty), empty)
    | ImmBool (b, _) -> (ImmBool (b, empty), empty)
    | ImmNil _ -> (ImmNil empty, empty)
    | ImmExcept (ex, _) -> (ImmExcept (ex, empty), empty)
  and helpC (e : 'a cexpr) : StringSet.t cexpr * StringSet.t =
    match e with
    | CIf (cond, thn, els, _) ->
        let new_cond, free_cond = helpI cond in
        let new_thn, free_thn = helpA thn in
        let new_els, free_els = helpA els in
        let free = free_cond |> u free_thn |> u free_els in
        (CIf (new_cond, new_thn, new_els, free), free)
    | CPrim1 (op, expr, _) ->
        let new_expr, free = helpI expr in
        (CPrim1 (op, new_expr, free), free)
    | CPrim2 (op, left, right, _) ->
        let new_left, free_left = helpI left in
        let new_right, free_right = helpI right in
        let free = free_left |> u free_right in
        (CPrim2 (op, new_left, new_right, free), free)
    | CApp (func, args, call_type, _) ->
        let new_func, free_func = helpI func in
        let new_args, free_args =
          List.fold_left
            (fun (acc, set) arg ->
              let new_arg, free_arg = helpI arg in
              (new_arg :: acc, set |> u free_arg) )
            ([], empty) args
        in
        let free = free_args |> u free_func in
        (CApp (new_func, new_args, call_type, free), free)
    | CImmExpr expr ->
        let new_expr, free = helpI expr in
        (CImmExpr new_expr, free)
    | CTuple (args, _) ->
        let new_args, free =
          List.fold_left
            (fun (acc, set) arg ->
              let new_arg, free_arg = helpI arg in
              (new_arg :: acc, free_arg |> u set) )
            ([], empty) args
        in
        (CTuple (new_args, free), free)
    | CGetItem (tup, idx, _) ->
        let new_tup, free_tup = helpI tup in
        let new_idx, free_idx = helpI idx in
        let free = free_idx |> u free_tup in
        (CGetItem (new_tup, new_idx, free), free)
    | CSetItem (tup, idx, new_elem, _) ->
        let new_tup, free_tup = helpI tup in
        let new_idx, free_idx = helpI idx in
        let new_val, free_val = helpI new_elem in
        let free = free_idx |> u free_tup |> u free_val in
        (CSetItem (new_tup, new_idx, new_val, free), free)
    (* FV[lam(x): b] = FV[b] ∖ {x} *)
    | CLambda (ids, body, _) ->
        let new_body, free_body = helpA body in
        let free = d free_body (StringSet.of_list ids) in
        (CLambda (ids, new_body, free), free)
    | CTryCatch (t, except, c, _) ->
        let new_try, free_try = helpI t in
        let new_catch, free_catch = helpI c in
        let free = free_try |> u free_catch in
        (CTryCatch (new_try, except, new_catch, free), free)
    | CCheck (checks, _) ->
        let new_checks, free =
          List.fold_left
            (fun (acc, set) check ->
              let new_check, free_arg = helpI check in
              (new_check :: acc, free_arg |> u set) )
            ([], empty) checks
        in
        (CCheck (new_checks, free), free)
    | CTestOp1 (e1, e2, negation, _) ->
        let new_e1, free_e1 = helpI e1 in
        let new_e2, free_e2 = helpI e2 in
        let free = free_e1 |> u free_e2 in
        (CTestOp1 (new_e1, new_e2, negation, free), free)
    | CTestOp2 (e1, e2, tt, negation, _) ->
        let new_e1, free_e1 = helpI e1 in
        let new_e2, free_e2 = helpI e2 in
        let free = free_e1 |> u free_e2 in
        (CTestOp2 (new_e1, new_e2, tt, negation, free), free)
    | CTestOp2Pred (e1, e2, pred, negation, _) ->
        let new_e1, free_e1 = helpI e1 in
        let new_e2, free_e2 = helpI e2 in
        let new_pred, free_pred = helpI pred in
        let free = free_e1 |> u free_e2 |> u free_pred in
        (CTestOp2Pred (new_e1, new_e2, new_pred, negation, free), free)
  and helpA (e : 'a aexpr) : StringSet.t aexpr * StringSet.t =
    match e with
    | ASeq (first, next, _) ->
        let new_first, free_first = helpC first in
        let new_next, free_next = helpA next in
        let free = free_first |> u free_next in
        (ASeq (new_first, new_next, free), free)
    (* FV[let x = e in b] = FV[e] ∪ (FV[b] ∖ {x}) *)
    | ALet (name, bound, body, _) ->
        let new_bound, free_bound = helpC bound in
        let new_body, free_body = helpA body in
        let free = free_bound |> u (StringSet.remove name free_body) in
        (ALet (name, new_bound, new_body, free), free)
    (* FV[let rec x = e in b] = (FV[e] ∪ FV[b]) ∖ {x} *)
    | ALetRec (binds, body, _) ->
        let new_binds, free_binds =
          (* This fold means that LetRec free variables are unidirectional!
           * Mutual recursion is not possible!
           *)
          List.fold_left
            (fun (acc, free) (name, cexpr) ->
              let new_bound, free_bound = helpC cexpr in
              ((name, new_bound) :: acc, free_bound |> u free) )
            ([], StringSet.empty) binds
        in
        let new_body, free_body = helpA body in
        let free = free_body |> u free_binds in
        let free = StringSet.diff free (StringSet.of_list (List.map fst binds)) in
        (ALetRec (new_binds, new_body, free), free)
    | ACExpr cexpr ->
        let new_c, free = helpC cexpr in
        (ACExpr new_c, free)
  in
  let new_body, free_body = helpA body in
  AProgram (new_body, free_body)
;;

let get_cache (expr : StringSet.t aexpr) : StringSet.t =
  let helpI (imm_expr : StringSet.t immexpr) : StringSet.t =
    match imm_expr with
    | ImmNum (_, c) | ImmBool (_, c) | ImmId (_, c) | ImmNil c | ImmExcept (_, c) -> c
  in
  let helpC (cexpr : StringSet.t cexpr) : StringSet.t =
    match cexpr with
    | CIf (_, _, _, cache)
     |CPrim1 (_, _, cache)
     |CPrim2 (_, _, _, cache)
     |CTuple (_, cache)
     |CGetItem (_, _, cache)
     |CSetItem (_, _, _, cache)
     |CLambda (_, _, cache)
     |CApp (_, _, _, cache)
     |CTryCatch (_, _, _, cache)
     |CCheck (_, cache)
     |CTestOp1 (_, _, _, cache)
     |CTestOp2 (_, _, _, _, cache)
     |CTestOp2Pred (_, _, _, _, cache)
     |CImmExpr (ImmId (_, cache)) -> cache
    | CImmExpr thing -> helpI thing
  in
  match expr with
  | ASeq (_, _, cache) | ALet (_, _, _, cache) | ALetRec (_, _, cache) -> cache
  | ACExpr cexpr -> helpC cexpr
;;
