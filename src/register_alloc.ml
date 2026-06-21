open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
open Graph
open Constants
open Env
open Util
open Free_vars
open Liveness
open Naive_alloc

let naive_stack_allocation = naive_stack_allocation

(* Consumes an AExpr tagged with sets of live variables *)
let interfere (e : livevars aexpr) : grapht =
  let rec helpA e g =
    match e with
    | ASeq (_, next, l) ->
        let g' = add_nodes g (StringSet.to_list l) in
        helpA next (connect_set l g')
    | ALet (x, _, b, l) ->
        let g' = add_node g x in
        let g' = add_nodes g' (StringSet.to_list l) in
        let connected = connect_set l g' in
        helpA b (connect x l connected)
    | ALetRec (bindings, b, l) ->
        let names, _ = List.split bindings in
        let g' = add_nodes g names in
        let g' = add_nodes g' (StringSet.to_list l) in
        let names = StringSet.of_list names in
        let connected_names = connect_set names g' in
        let connected_set = connect_set l connected_names in
        let all_connected = connect2 names l connected_set in
        helpA b all_connected
    | ACExpr (CIf (_, thn, els, l)) ->
        let g' = add_nodes g (StringSet.to_list l) in
        helpA thn (helpA els (connect_set l g'))
    | _ -> g
  in
  helpA e Graph.empty
;;

(* We got rid of the scratch registers because they were too important... *)
let colors = List.map (fun x -> Reg x) [R12; R13; R14; RBX]

let color_graph ?(colors = colors) (g : grapht) (init_env : arg name_envt) : arg name_envt =
  (* Get the node with the smallest degree. *)
  let rec worklist (gw : grapht) (stack : string list) : string list =
    match smallest_degree gw with
    | None -> stack
    | Some node -> worklist (remove_node gw node) (node :: stack)
  in
  let next_color (nodes : neighborst) (mapping : arg name_envt) : arg =
    let allocated =
      List.filter_map (fun node -> StringMap.find_opt node mapping) (NeighborSet.to_list nodes)
    in
    let next_offset =
      (* Remember to use -1 and `min` because the offsets grow downward. *)
      ~-1
      + List.fold_left
          (fun acc arg ->
            match arg with
            | RegOffset (n, _) -> min n acc
            | _ -> acc )
          0 allocated
    in
    let next_register = List.find_opt (fun color -> not (List.mem color allocated)) colors in
    match next_register with
    | None -> RegOffset (next_offset, RBP)
    | Some arg -> arg
  in
  let color_nodes (stack : string list) (mapping : arg name_envt) : arg name_envt =
    List.fold_right
      (fun node mapping' ->
        let neighbors = Graph.find node g in
        let color = next_color neighbors mapping' in
        StringMap.add node color mapping' )
      stack mapping
  in
  color_nodes (worklist g []) init_env
;;

let register_allocation (prog : tag aprogram) : tag aprogram * arg name_envt name_envt =
  let rec helpC (e : freevars cexpr) (env_name : string) (env_env : arg name_envt name_envt) :
      arg name_envt name_envt =
    match e with
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
     |CTestOp2Pred _ -> env_env
    | CIf (_, thn, els, _) ->
        let thn_env = helpA thn env_name env_env in
        helpA els env_name thn_env
    | CLambda (ids, body, _) ->
        let args_locs = List.mapi (fun index id -> (id, RegOffset (index + 3, RBP))) ids in
        let args_env =
          List.fold_left
            (fun envt_envt (id, location) -> update_envt_envt env_name id location envt_envt)
            env_env args_locs
        in
        helpA body env_name args_env
  (* helper for ANF expressions *)
  and helpA (e : freevars aexpr) (env_name : string) (env_env : arg name_envt name_envt) :
      arg name_envt name_envt =
    match e with
    | ACExpr cexp -> helpC cexp env_name env_env
    | ALetRec ([], body, _) -> helpA body env_name env_env
    | ALet (id, (CLambda _ as lambda), body, _) ->
        let add_base_env_for_lambda = StringMap.add id StringMap.empty env_env in
        let lambda_color_map = color_graph (interfere e) (safe_find_opt env_name env_env) in
        let lambda_offset = helpC lambda id add_base_env_for_lambda in
        let body_offset = helpA body env_name lambda_offset in
        let offset =
          safe_find_opt id lambda_color_map
            ~callee_tag:("ALet of lambda\n" ^ string_of_name_envt lambda_color_map)
        in
        let cur_envt = update_envt_envt env_name id offset body_offset in
        cur_envt
    | ALetRec ([(id, (CLambda _ as lambda))], body, _) ->
        let add_base_env_for_lambda = StringMap.add id StringMap.empty env_env in
        let lambda_color_map = color_graph (interfere e) (safe_find_opt env_name env_env) in
        let lambda_offset = helpC lambda id add_base_env_for_lambda in
        let body_offset = helpA body env_name lambda_offset in
        let offset =
          safe_find_opt id lambda_color_map
            ~callee_tag:("ALet of lambda\n" ^ string_of_name_envt lambda_color_map)
        in
        let cur_envt = update_envt_envt env_name id offset body_offset in
        cur_envt
    | ALet (_, bound, body, _) ->
        let cur_env = safe_find_opt env_name env_env in
        let colored = color_graph (interfere e) cur_env in
        let env_new = StringMap.add env_name colored env_env in
        let assign_env = helpC bound env_name env_new in
        helpA body env_name assign_env
    | ALetRec ([(_, bound)], body, _) ->
        (* LetRec is not yet truly implemented, since we can't handle mutual recursion. *)
        let bound_env = helpC bound env_name env_env in
        helpA body env_name bound_env
    | ASeq (first, next, _) ->
        let cur_env = safe_find_opt env_name env_env in
        let seq_env = color_graph (interfere e) cur_env in
        let env_new = StringMap.add env_name seq_env env_env in
        let fst_env = helpC first env_name env_new in
        helpA next env_name fst_env
    | _ -> raise (NotYetImplemented "lol")
  in
  let (AProgram (body, _)) = free_vars_cache prog in
  let initial_env = assoc_to_map [(ocsh_name, StringMap.empty)] in
  let body_env = helpA body ocsh_name initial_env in
  (prog, body_env)
;;
