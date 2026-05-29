open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
open Constants
open Env
open Util
open Free_vars

let si_to_arg (si : int) : arg = RegOffset (~-si, RBP)

let naive_stack_allocation (AProgram (body, _) as prog : tag aprogram) :
    tag aprogram * arg name_envt name_envt =
  let rec helpC (cexp : tag cexpr) (env : arg name_envt name_envt) (si : int) (env_name : string) :
      arg name_envt name_envt =
    match cexp with
    | CPrim1 _
     |CPrim2 _
     |CApp _
     |CImmExpr _
     |CTuple _
     |CGetItem _
     |CSetItem _
     |CTryCatch _
     |CCheck _
     |CTestOp1 _
     |CTestOp2 _
     |CTestOp2Pred _ -> env
    | CIf (_, thn, els, _) ->
        let thn_env = helpA thn env (si + 1) env_name in
        helpA els thn_env (si + 1) env_name
    | CLambda (ids, body, _) ->
        (*
         * Actually, we add 3, to account for the implicit 'self' argument.
         *)
        let num_free = StringSet.cardinal @@ free_vars (ACExpr cexp) in
        let args_locs = List.mapi (fun index id -> (id, RegOffset (index + 3, RBP))) ids in
        let args_env =
          List.fold_left
            (fun envt_envt (id, location) -> update_envt_envt env_name id location envt_envt)
            env args_locs
        in
        helpA body args_env (num_free + 1) env_name
  and helpA (aexp : tag aexpr) (env : arg name_envt name_envt) (si : int) (env_name : string) :
      arg name_envt name_envt =
    match aexp with
    | ACExpr cexp -> helpC cexp env si env_name
    | ASeq (first, next, _) ->
        merge_envs (helpA next env (si + 1) env_name) (helpC first env si env_name)
    | ALetRec ([], body, _) -> helpA body env (si + 1) env_name
    | ALet (id, (CLambda _ as lambda), body, _) ->
        let add_base_env_for_lambda = StringMap.add id StringMap.empty env in
        let offset = si_to_arg si in
        let body_offset = helpA body add_base_env_for_lambda (si + 1) env_name in
        let cur_envt = update_envt_envt env_name id offset body_offset in
        let lambda_offset = helpC lambda cur_envt si id in
        lambda_offset
    | ALet (id, bound, body, _) ->
        let offset = si_to_arg si in
        let body_env = helpA body env (si + 1) env_name in
        let cur_envt = update_envt_envt env_name id offset body_env in
        let bound_env = helpC bound cur_envt si env_name in
        bound_env
    | ALetRec ((id, (CLambda _ as lambda)) :: rest, body, tag) ->
        let add_base_env_for_lambda = StringMap.add id StringMap.empty env in
        let cur_offset = si_to_arg si in
        let body_envt_envt = helpA body add_base_env_for_lambda (si + 1) env_name in
        let cur_envt = update_envt_envt env_name id cur_offset body_envt_envt in
        let lambda_offset = helpC lambda cur_envt si id in
        let with_self_reference = update_envt_envt id id (RegOffset (2, RBP)) lambda_offset in
        (* This is where we could put our mutual recursion code -- If we had any! *)
        let rest_env = helpA (ALetRec (rest, body, tag)) with_self_reference (si + 1) env_name in
        rest_env
    | ALetRec ((id, bound) :: rest, body, tag) ->
        let offset = si_to_arg si in
        let body_env = helpA body env (si + 1) env_name in
        let cur_envt = update_envt_envt env_name id offset body_env in
        let bound_env = helpC bound cur_envt si env_name in
        let rest_env = helpA (ALetRec (rest, body, tag)) bound_env (si + 1) env_name in
        rest_env
  in
  let body_env = helpA body (assoc_to_map [(ocsh_name, StringMap.empty)]) 1 ocsh_name in
  (prog, body_env)
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

let deepest_stack (env : arg name_envt) : int =
  StringMap.fold
    (fun _ value acc ->
      match value with
      | RegOffset (words, _) -> max (words / ~-1) acc
      | _ -> acc )
    env 0
;;
