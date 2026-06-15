open Printf
open Pretty
open Exprs
open Assembly
open Errors
open Constants

let print_env env how =
  debug_printf "Env is\n";
  List.iter (fun (id, bind) -> debug_printf "  %s -> %s\n" id (how bind)) env
;;

let assoc_to_map (assoc : (string * 'a) list) : 'a StringMap.t =
  List.fold_left (fun map (key, value) -> StringMap.add key value map) StringMap.empty assoc
;;

(* Prepends a list-like env onto an name_envt *)
let merge_envs env1 env2 = StringMap.union (fun _ first _ -> Some first) env1 env2

(* Combines two name_envts into one, preferring the first one *)
let prepend = merge_envs

(* you can add any functions or data defined by the runtime here for future use *)
let initial_val_env =
  assoc_to_map
    [ ("nil", (dummy_span, None, None));
      ("true", (dummy_span, None, None));
      ("false", (dummy_span, None, None)) ]
;;

let prim_bindings =
  assoc_to_map
    [ ("isnum", (dummy_span, Some 1, Some 1));
      ("isbool", (dummy_span, Some 1, Some 1));
      ("istuple", (dummy_span, Some 1, Some 1));
      ("add1", (dummy_span, Some 1, Some 1));
      ("sub1", (dummy_span, Some 1, Some 1));
      ("print", (dummy_span, Some 1, Some 1));
      ("printStack", (dummy_span, Some 0, Some 0)) ]
;;

let native_fun_bindings =
  assoc_to_map [("input", (dummy_span, Some 0, Some 0)); ("equal", (dummy_span, Some 2, Some 2))]
;;

let initial_fun_env = merge_envs prim_bindings native_fun_bindings

(* You may find some of these helpers useful *)

let rec find_decl (ds : 'a decl list) (name : string) : 'a decl option =
  match ds with
  | [] -> None
  | (DFun (fname, _, _, _) as d) :: ds_rest ->
      if name = fname then
        Some d
      else
        find_decl ds_rest name
;;

let find_opt (env : 'a name_envt) (elt : string) : 'a option = StringMap.find_opt elt env

let env_keys (e : 'a name_envt) : string list = List.map fst (StringMap.bindings e)

(* Scope_info stores the location where something was defined,
   and if it was a function declaration, then its type arity and argument arity *)
type scope_info = sourcespan * int option * int option

let gensym =
  let next = ref 0 in
  fun name ->
    next := !next + 1;
    sprintf "%s_%d" name !next
;;

(* Extend the inner mapping with `(inner_key, value)` *)
let update_envt_envt
    (outer_key : string)
    (inner_key : string)
    (value : 'a)
    (m : 'a name_envt name_envt) : 'a name_envt name_envt =
  StringMap.update outer_key
    (fun x ->
      match x with
      | None -> Some (StringMap.singleton inner_key value)
      | Some inner -> Some (StringMap.add inner_key value inner) )
    m
;;

let get_nested outer_key inner_key envt_envt =
  let maybe_inner_envt = StringMap.find_opt outer_key envt_envt in
  match maybe_inner_envt with
  | None ->
      raise (InternalCompilerError (sprintf "Unable to find inner env with the name: %s" outer_key))
  | Some inner_envt -> (
      let maybe_thing = StringMap.find_opt inner_key inner_envt in
      match maybe_thing with
      | None ->
          raise
            (InternalCompilerError
               (sprintf "Unable to find id: %s within inner_envt named: %s" inner_key outer_key) )
      | Some thing -> thing )
;;

let string_of_name_envt env =
  "\n"
  ^ ExtString.String.join "\n"
      (List.map (fun (name, arg) -> name ^ "=>" ^ arg_to_asm arg) (StringMap.bindings env))
  ^ "\n"
;;

let safe_find_opt ?callee_tag:(addn = "") key map =
  let maybe_thing = StringMap.find_opt key map in
  match maybe_thing with
  | None -> raise (InternalCompilerError (sprintf "Unable to find thing: %s. %s" key addn))
  | Some thing -> thing
;;
