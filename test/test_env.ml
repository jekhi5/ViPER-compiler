open Test_funcs
open Env
open Exprs
open Assembly
open Errors
open Constants
open OUnit2

(* Tests for the env functions for ViPER *)

let dummy = dummy_span

(* --- assoc_to_map --- *)

let test_suite =
  [ (* --- print_env --- *)
    tae "printEnvEmpty" () (print_env [] string_of_int);
    tae "printEnvNonEmpty" () (print_env [("x", 1); ("y", 2)] string_of_int);
    (* --- assoc_to_map --- *)
    tae "assocToMapEmpty" [] (StringMap.bindings (assoc_to_map []));
    tae "assocToMapSingle" [("a", 1)] (StringMap.bindings (assoc_to_map [("a", 1)]));
    tae "assocToMapMultiple"
      [("a", 1); ("b", 2); ("c", 3)]
      (StringMap.bindings (assoc_to_map [("c", 3); ("a", 1); ("b", 2)]));
    (* last-write-wins when key is duplicated in assoc list *)
    tae "assocToMapDupKey" [("a", 2)] (StringMap.bindings (assoc_to_map [("a", 1); ("a", 2)]));
    (* --- merge_envs / prepend --- *)
    (* first env wins on conflicts *)
    tae "mergeEnvsFirstWins" (Some 1)
      (StringMap.find_opt "k" (merge_envs (assoc_to_map [("k", 1)]) (assoc_to_map [("k", 99)])));
    (* keys only in the second env are preserved *)
    tae "mergeEnvsPreservesSecond" (Some 99)
      (StringMap.find_opt "y" (merge_envs (assoc_to_map [("x", 1)]) (assoc_to_map [("y", 99)])));
    (* merging two empty maps gives empty *)
    tae "mergeEnvsEmpty" [] (StringMap.bindings (merge_envs StringMap.empty StringMap.empty));
    (* prepend is merge_envs — first argument wins *)
    tae "prependFirstWins" (Some 10)
      (StringMap.find_opt "k" (prepend (assoc_to_map [("k", 10)]) (assoc_to_map [("k", 20)])));
    (* --- find_opt --- *)
    tae "findOptPresentKey" (Some 42) (find_opt (assoc_to_map [("x", 42)]) "x");
    tae "findOptMissingKey" None (find_opt (assoc_to_map [("x", 42)]) "y");
    tae "findOptEmptyEnv" None (find_opt StringMap.empty "x");
    (* --- env_keys --- *)
    tae "envKeysEmpty" [] (env_keys StringMap.empty);
    (* StringMap sorts keys alphabetically *)
    tae "envKeysSingle" ["a"] (env_keys (assoc_to_map [("a", 1)]));
    tae "envKeysSorted" ["a"; "b"; "c"] (env_keys (assoc_to_map [("c", 3); ("a", 1); ("b", 2)]));
    (* --- gensym --- *)
    (* two successive calls produce distinct names *)
    tae "gensymDistinct" false
      (let a = gensym "x" in
       let b = gensym "x" in
       a = b );
    (* the name is prefixed by the supplied string *)
    tae "gensymPrefix" true
      (let s = gensym "foo" in
       String.length s > 3 && String.sub s 0 4 = "foo_" );
    (* different base names stay distinct *)
    tae "gensymDifferentBases" false
      (let a = gensym "alpha" in
       let b = gensym "beta" in
       a = b );
    (* --- initial_val_env --- *)
    tae "initialValEnvHasNil" true (StringMap.mem "nil" initial_val_env);
    tae "initialValEnvHasTrue" true (StringMap.mem "true" initial_val_env);
    tae "initialValEnvHasFalse" true (StringMap.mem "false" initial_val_env);
    tae "initialValEnvSize" 3 (StringMap.cardinal initial_val_env);
    (* --- prim_bindings --- *)
    tae "primBindingsHasIsnum" true (StringMap.mem "isnum" prim_bindings);
    tae "primBindingsHasIsbool" true (StringMap.mem "isbool" prim_bindings);
    tae "primBindingsHasIstuple" true (StringMap.mem "istuple" prim_bindings);
    tae "primBindingsHasAdd1" true (StringMap.mem "add1" prim_bindings);
    tae "primBindingsHasSub1" true (StringMap.mem "sub1" prim_bindings);
    tae "primBindingsHasPrint" true (StringMap.mem "print" prim_bindings);
    tae "primBindingsHasPrintStack" true (StringMap.mem "printStack" prim_bindings);
    tae "primBindingsSize" 7 (StringMap.cardinal prim_bindings);
    (* arity values for a prim: (dummy_span, Some 1, Some 1) *)
    tae "primBindingsAdd1Arity" (dummy, Some 1, Some 1) (StringMap.find "add1" prim_bindings);
    tae "primBindingsPrintStackArity" (dummy, Some 0, Some 0)
      (StringMap.find "printStack" prim_bindings);
    (* --- native_fun_bindings --- *)
    tae "nativeFunBindingsHasInput" true (StringMap.mem "input" native_fun_bindings);
    tae "nativeFunBindingsHasEqual" true (StringMap.mem "equal" native_fun_bindings);
    tae "nativeFunBindingsSize" 2 (StringMap.cardinal native_fun_bindings);
    tae "nativeFunBindingsInputArity" (dummy, Some 0, Some 0)
      (StringMap.find "input" native_fun_bindings);
    tae "nativeFunBindingsEqualArity" (dummy, Some 2, Some 2)
      (StringMap.find "equal" native_fun_bindings);
    (* --- initial_fun_env --- *)
    (* contains all prims plus natives *)
    tae "initialFunEnvSize" 9 (StringMap.cardinal initial_fun_env);
    tae "initialFunEnvHasAdd1" true (StringMap.mem "add1" initial_fun_env);
    tae "initialFunEnvHasInput" true (StringMap.mem "input" initial_fun_env);
    (* --- find_decl --- *)
    tae "findDeclEmpty" None (find_decl [] "f");
    tae "findDeclNotPresent" None (find_decl [DFun ("g", [], EBool (true, dummy), dummy)] "f");
    tae "findDeclPresent"
      (Some (DFun ("f", [], EBool (true, dummy), dummy)))
      (find_decl [DFun ("f", [], EBool (true, dummy), dummy)] "f");
    tae "findDeclFirstMatch"
      (Some (DFun ("f", [], ENumber (1L, dummy), dummy)))
      (find_decl
         [DFun ("f", [], ENumber (1L, dummy), dummy); DFun ("f", [], ENumber (2L, dummy), dummy)]
         "f" );
    tae "findDeclMultipleDeclsCorrectOne"
      (Some (DFun ("g", [], EBool (false, dummy), dummy)))
      (find_decl
         [ DFun ("f", [], EBool (true, dummy), dummy);
           DFun ("g", [], EBool (false, dummy), dummy);
           DFun ("h", [], EBool (true, dummy), dummy) ]
         "g" );
    (* --- update_envt_envt --- *)
    (* inserting into an absent outer key creates a new inner map *)
    tae "updateEnvtEnvtNewOuter" 7
      (get_nested "outer" "inner" (update_envt_envt "outer" "inner" 7 StringMap.empty));
    (* inserting into an existing outer key adds to the inner map *)
    tae "updateEnvtEnvtExistingOuter" 99
      (let m = update_envt_envt "outer" "a" 1 StringMap.empty in
       get_nested "outer" "b" (update_envt_envt "outer" "b" 99 m) );
    (* update overwrites an existing inner key *)
    tae "updateEnvtEnvtOverwrite" 42
      (let m = update_envt_envt "outer" "k" 1 StringMap.empty in
       get_nested "outer" "k" (update_envt_envt "outer" "k" 42 m) );
    (* --- get_nested --- *)
    tae "getNestedPresent" 5
      (let m = update_envt_envt "A" "x" 5 StringMap.empty in
       get_nested "A" "x" m );
    tar "getNestedMissingOuter"
      (InternalCompilerError "Unable to find inner env with the name: missing") (fun _ ->
        get_nested "missing" "x" StringMap.empty );
    tar "getNestedMissingInner"
      (InternalCompilerError "Unable to find id: z within inner_envt named: A") (fun _ ->
        let m = update_envt_envt "A" "x" 5 StringMap.empty in
        get_nested "A" "z" m );
    (* --- string_of_name_envt --- *)
    tae "stringOfNameEnvtEmpty" "\n\n" (string_of_name_envt (StringMap.empty : arg StringMap.t));
    tae "stringOfNameEnvtSingleReg" "\na=>RAX\n"
      (string_of_name_envt (assoc_to_map [("a", Reg RAX)]));
    tae "stringOfNameEnvtMultiple" "\na=>RAX\nb=>[RBP-8]\n"
      (string_of_name_envt (assoc_to_map [("a", Reg RAX); ("b", RegOffset (-1, RBP))]));
    (* --- safe_find_opt --- *)
    tae "safeFindOptPresent" 99 (safe_find_opt "k" (assoc_to_map [("k", 99)]));
    tar "safeFindOptMissing" (InternalCompilerError "Unable to find thing: missing. ") (fun _ ->
        safe_find_opt "missing" (assoc_to_map [("k", 1)]) );
    tae "safeFindOptWithCalleeTag" 7 (safe_find_opt ~callee_tag:"ctx" "k" (assoc_to_map [("k", 7)]));
    tar "safeFindOptMissingWithCalleeTag" (InternalCompilerError "Unable to find thing: gone. ctx")
      (fun _ -> safe_find_opt ~callee_tag:"ctx" "gone" (assoc_to_map [("k", 1)]) ) ]
;;

module Suite : TestSuite = struct
  let suite = test_suite
end
