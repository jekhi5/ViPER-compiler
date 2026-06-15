open Printf
open Pretty
open Phases
open Exprs
open Errors
open Constants
open Env
open Util
open Free_vars

let empty = StringSet.empty

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

(*
 * `expr` - The expression of which the live_in set is being computed
 * `live_out` - The live_out set of THIS expression. IE: `live_out` == `live_in` of the NEXT expression
 *  Returns: The same kind of expression where the `a position of the expression now holds the live_in set
 *           as well as all subexpressions also holding their own live_in set
 *)
let rec compute_live_in (expr : freevars aexpr) (live_out : livevars) : livevars aexpr =
  (* TODO: unioning all of the `live_in` sets with `live_out` at the end might be redundant
   *       and potentially wrong if we're set_diff-ing things beforehand. Review this.
   *       See the `CApp` case
   *)
  let helpI (imm_expr : StringSet.t immexpr) (live_out : StringSet.t) : StringSet.t immexpr =
    match imm_expr with
    | ImmNum (num, _) -> ImmNum (num, live_out)
    | ImmBool (bool, _) -> ImmBool (bool, live_out)
    | ImmId (id, _) -> ImmId (id, live_out |> u (StringSet.singleton id))
    | ImmNil _ -> ImmNil live_out
    | ImmExcept (ex, _) -> ImmExcept (ex, live_out)
  in
  let helpC (cexpr : StringSet.t cexpr) (live_out : StringSet.t) : StringSet.t cexpr =
    match cexpr with
    | CIf (cond, thn, els, _) ->
        let live_els = compute_live_in els live_out in
        let live_thn = compute_live_in thn live_out in
        let live_out_cond = get_cache live_els |> u (get_cache live_thn) in
        let live_cond = helpI cond live_out_cond in
        let aexpr_live_cond = ACExpr (CImmExpr live_cond) in
        let free_vars =
          free_vars aexpr_live_cond |> u (free_vars live_els) |> u (free_vars live_thn)
        in
        let live_in =
          get_cache aexpr_live_cond
          |> u (get_cache live_thn)
          |> u (get_cache live_els)
          |> u free_vars
        in
        CIf (live_cond, live_thn, live_els, live_in)
    | CImmExpr imm_expr -> CImmExpr (helpI imm_expr live_out)
    | CLambda (args, body, _) ->
        let live_body = compute_live_in body live_out in
        let args_set = StringSet.of_list args in
        let free_vars = free_vars live_body in
        let live_in = d (get_cache live_body |> u free_vars) args_set in
        CLambda (args, live_body, live_in)
    | CPrim1 (op, thing, _) ->
        let live_thing = helpI thing live_out in
        let aexpr_live_thing = ACExpr (CImmExpr live_thing) in
        let free_vars = free_vars aexpr_live_thing in
        let live_in = get_cache aexpr_live_thing |> u free_vars in
        CPrim1 (op, live_thing, live_in)
    | CPrim2 (op, left, right, _) ->
        let live_right = helpI right live_out in
        let live_out_left = get_cache (ACExpr (CImmExpr live_right)) |> u live_out in
        let live_left = helpI left live_out_left in
        let aexpr_live_left = ACExpr (CImmExpr live_left) in
        let aexpr_live_right = ACExpr (CImmExpr live_right) in
        let free_vars = free_vars aexpr_live_left |> u (free_vars aexpr_live_right) in
        let live_in = get_cache aexpr_live_left |> u (get_cache aexpr_live_right) |> u free_vars in
        CPrim2 (op, live_left, live_right, live_in)
    | CApp (func, args, call_type, _) ->
        (* `live_func`'s live_in value includes the given live_out, thus, the given
         * live_out is propogated through all the args and is thus included in the
         * final `live_in` of the whole CApp
         *)
        let live_func = helpI func live_out in
        let last_arg_live_out = get_cache (ACExpr (CImmExpr live_func)) in
        let live_in_args, live_args =
          List.fold_right
            (fun arg ((arg_live_out : StringSet.t), new_args) ->
              let live_arg = helpI arg arg_live_out in
              let free_vars = free_vars (ACExpr (CImmExpr live_arg)) in
              let live_in = get_cache (ACExpr (CImmExpr live_arg)) |> u free_vars in
              (live_in, live_arg :: new_args) )
            args (last_arg_live_out, [])
        in
        let live_in = live_in_args |> u (free_vars (ACExpr (CImmExpr live_func))) in
        CApp (live_func, live_args, call_type, live_in)
    | CTuple (elems, _) ->
        let live_in, live_elems =
          List.fold_right
            (fun elem ((elem_live_out : StringSet.t), new_elems) ->
              let live_elem = helpI elem elem_live_out in
              let free_vars = free_vars (ACExpr (CImmExpr live_elem)) in
              let elem_live_in = get_cache (ACExpr (CImmExpr live_elem)) |> u free_vars in
              (elem_live_in, live_elem :: new_elems) )
            elems (live_out, [])
        in
        CTuple (live_elems, live_in)
    | CGetItem (tup, idx, _) ->
        let live_tup = helpI tup live_out in
        let aexpr_live_tup = ACExpr (CImmExpr live_tup) in
        let live_idx = helpI idx (get_cache aexpr_live_tup) in
        let aexpr_live_idx = ACExpr (CImmExpr live_idx) in
        let free_vars = free_vars aexpr_live_idx |> u (free_vars aexpr_live_tup) in
        let live_in = get_cache aexpr_live_idx |> u (get_cache aexpr_live_tup) |> u free_vars in
        CGetItem (live_tup, live_idx, live_in)
    | CSetItem (tup, idx, new_elem, _) ->
        let live_tup = helpI tup live_out in
        let aexpr_live_tup = ACExpr (CImmExpr live_tup) in
        let live_idx = helpI idx (get_cache aexpr_live_tup) in
        let aexpr_live_idx = ACExpr (CImmExpr live_idx) in
        let live_new_elem = helpI new_elem (get_cache aexpr_live_idx) in
        let aexpr_live_new_elem = ACExpr (CImmExpr live_new_elem) in
        let free_vars =
          free_vars aexpr_live_idx
          |> u (free_vars aexpr_live_tup)
          |> u (free_vars aexpr_live_new_elem)
        in
        let live_in =
          get_cache aexpr_live_tup
          |> u (get_cache aexpr_live_idx)
          |> u (get_cache aexpr_live_new_elem)
          |> u free_vars
        in
        CSetItem (live_tup, live_idx, live_new_elem, live_in)
    | CTryCatch (t, except, c, _) ->
        let live_catch = helpI c live_out in
        let live_try = helpI t live_out in
        let aexpr_live_try = ACExpr (CImmExpr live_try) in
        let aexpr_live_catch = ACExpr (CImmExpr live_catch) in
        let free_vars = free_vars aexpr_live_catch |> u (free_vars aexpr_live_try) in
        let live_in = get_cache aexpr_live_try |> u (get_cache aexpr_live_catch) |> u free_vars in
        CTryCatch (live_try, except, live_catch, live_in)
    | CCheck (checks, _) ->
        let live_in, live_checks =
          List.fold_right
            (fun check ((check_live_out : StringSet.t), new_checks) ->
              let live_check = helpI check check_live_out in
              let free_vars = free_vars (ACExpr (CImmExpr live_check)) in
              let check_live_in = get_cache (ACExpr (CImmExpr live_check)) |> u free_vars in
              (check_live_in, live_check :: new_checks) )
            checks (live_out, [])
        in
        CCheck (live_checks, live_in)
    | CTestOp1 (e1, e2, negation, _) ->
        let live_e2 = helpI e2 live_out in
        let aexpr_live_e2 = ACExpr (CImmExpr live_e2) in
        let live_e1 = helpI e1 (get_cache aexpr_live_e2) in
        let aexpr_live_e1 = ACExpr (CImmExpr live_e1) in
        let free_vars = free_vars aexpr_live_e2 |> u (free_vars aexpr_live_e1) in
        let live_in = get_cache aexpr_live_e1 |> u (get_cache aexpr_live_e2) |> u free_vars in
        CTestOp1 (live_e1, live_e2, negation, live_in)
    | CTestOp2 (e1, e2, tt, negation, _) ->
        let live_e2 = helpI e2 live_out in
        let aexpr_live_e2 = ACExpr (CImmExpr live_e2) in
        let live_e1 = helpI e1 (get_cache aexpr_live_e2) in
        let aexpr_live_e1 = ACExpr (CImmExpr live_e1) in
        let free_vars = free_vars aexpr_live_e2 |> u (free_vars aexpr_live_e1) in
        let live_in = get_cache aexpr_live_e1 |> u (get_cache aexpr_live_e2) |> u free_vars in
        CTestOp2 (live_e1, live_e2, tt, negation, live_in)
    | CTestOp2Pred (e1, e2, pred, negation, _) ->
        let live_e2 = helpI e2 live_out in
        let aexpr_live_e2 = ACExpr (CImmExpr live_e2) in
        let live_e1 = helpI e1 (get_cache aexpr_live_e2) in
        let aexpr_live_e1 = ACExpr (CImmExpr live_e1) in
        let live_pred = helpI pred (get_cache aexpr_live_e1) in
        let aexpr_live_pred = ACExpr (CImmExpr live_pred) in
        let free_vars =
          free_vars aexpr_live_e2 |> u (free_vars aexpr_live_e1) |> u (free_vars aexpr_live_pred)
        in
        let live_in =
          get_cache aexpr_live_e1
          |> u (get_cache aexpr_live_e2)
          |> u (get_cache aexpr_live_pred)
          |> u free_vars
        in
        CTestOp2Pred (live_e1, live_e2, live_pred, negation, live_in)
  in
  match expr with
  | ASeq (first, next, _) ->
      let live_next = compute_live_in next live_out in
      let live_first = helpC first (get_cache live_next) in
      let aexpr_live_first = ACExpr live_first in
      let free_vars = free_vars aexpr_live_first |> u (free_vars live_next) in
      let live_in = get_cache aexpr_live_first |> u (get_cache live_next) |> u free_vars in
      ASeq (live_first, live_next, live_in)
  | ALet (x, e, b, _) ->
      let live_b = compute_live_in b live_out in
      let live_e = helpC e (get_cache live_b) in
      let free_vars = free_vars live_b |> u (free_vars (ACExpr live_e)) in
      let live_in =
        d
          (live_out |> u free_vars |> u (get_cache live_b) |> u (get_cache (ACExpr live_e)))
          (StringSet.singleton x)
      in
      ALet (x, live_e, live_b, live_in)
  | ALetRec (bindings, body, _) ->
      let live_body = compute_live_in body live_out in
      let bound_live_out, live_bindings =
        List.fold_right
          (fun (id, bound) ((this_live_out : StringSet.t), live_bounds) ->
            let live_bound = helpC bound this_live_out in
            let free_vars = free_vars (ACExpr live_bound) in
            let live_out_bound = get_cache (ACExpr live_bound) |> u free_vars in
            (live_out_bound, live_bounds @ [(id, live_bound)]) )
          bindings (live_out, [])
      in
      let names, _ = List.split bindings in
      let names_set = StringSet.of_list names in
      let live_in =
        d (get_cache live_body |> u bound_live_out |> u (free_vars live_body)) names_set
      in
      ALetRec (live_bindings, live_body, live_in)
  | ACExpr cexpr -> ACExpr (helpC cexpr live_out)

and live_in_program (AProgram (body, _)) = AProgram (compute_live_in body empty, empty)

let string_of_set s =
  "(" ^ List.fold_left (fun acc str -> acc ^ ", " ^ str) "" (StringSet.to_list s) ^ ")"
;;
