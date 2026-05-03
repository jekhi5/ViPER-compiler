open Assembly
open Compile_constants
open Errors
open Printf

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
