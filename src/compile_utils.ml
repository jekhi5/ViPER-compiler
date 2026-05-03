open Compile_constants
open Errors
open Exprs
open Printf

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

let env_keys (e : 'a name_envt) : string list = List.map fst (StringMap.bindings e)

let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y, v) :: rest ->
      if y = x then
        v
      else
        find rest x
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

let find_opt (env : 'a name_envt) (elt : string) : 'a option = StringMap.find_opt elt env

let gensym =
  let next = ref 0 in
  fun name ->
    next := !next + 1;
    sprintf "%s_%d" name !next
;;
