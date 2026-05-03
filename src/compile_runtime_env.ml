open Compile_constants
open Compile_utils

let ocsh_name = "ocsh_0"

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
