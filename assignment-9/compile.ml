open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors

(* NOTES:
 *  - We had to add `-no-pie` and `-gdwarf-4` to the clang args in the Makefile.
 *  - LetRec is known to be broken.
 *  - Native functions may work partially, and may crash.
      This is the error in deepest_stack, where identifiers are not found in the environment.
      Unfortunately, most of our legacy tests used native functions like print, so this causes problems...

 *  - Garbage collection does not work, unfortunately. We spent a lot of time working through our C code,
      but difficulties with our OCaml prevented us from testing it for a while.
      By the time we got regular compilation (i.e., recovery from FDL) working, we ran out of time to test GC.

 *  - We thought FDL was embarassing, but this is even worse.
      Our main issue is timing... We are both insanely busy all the time,
      and it is very difficult for us to find time to work as the semester 
      ends with extracurriculars and end-of-college-career stuff.
      We feel that we understand the theory of the class material,
      but have difficulties implementing it.
      
      This is all exacerbated by a non-zero amount of senioritis.

      It feels really bad to "choke at the finish line", but it is what it is.
      Hopefully we will do well on the second written assignment 
      (which is more theoretical in nature), and on the final project (which is more open-ended).

 *)

(* Documentation can be found at https://v2.ocaml.org/api/Set.S.html *)
module StringSet = Set.Make (String)

(* Documentation can be found at https://v2.ocaml.org/api/Map.S.html *)
module StringMap = Map.Make (String)

(* type 'a tag_envt = (tag * 'a) list *)

let print_env env how =
  debug_printf "Env is\n";
  List.iter (fun (id, bind) -> debug_printf "  %s -> %s\n" id (how bind)) env
;;

let blank_stack_val = 0xDEFACED

let heap_end_label = "?HEAP_END"

let const_true = HexConst 0xFFFFFFFFFFFFFFFFL

let const_false = HexConst 0x7FFFFFFFFFFFFFFFL

let bool_mask = HexConst 0x8000000000000000L

let bool_tag = 0x0000000000000007L

let bool_tag_mask = 0x0000000000000007L

let num_tag = 0x0000000000000000L

let num_tag_mask = 0x0000000000000001L

let closure_tag = 0x0000000000000005L

let closure_tag_mask = 0x0000000000000007L

let tuple_tag = 0x0000000000000001L

let tuple_tag_mask = 0x0000000000000007L

let const_nil = HexConst tuple_tag

let err_COMP_NOT_NUM = 1L

let err_ARITH_NOT_NUM = 2L

let err_LOGIC_NOT_BOOL = 3L

let err_IF_NOT_BOOL = 4L

let err_OVERFLOW = 5L

let err_GET_NOT_TUPLE = 6L

let err_GET_LOW_INDEX = 7L

let err_GET_HIGH_INDEX = 8L

let err_NIL_DEREF = 9L

let err_OUT_OF_MEMORY = 10L

let err_SET_NOT_TUPLE = 11L

let err_SET_LOW_INDEX = 12L

let err_SET_HIGH_INDEX = 13L

let err_CALL_NOT_CLOSURE = 14L

let err_CALL_ARITY_ERR = 15L

let err_INDEX_NOT_NUM = 16L

(* We added a Prim1 that just crashes the program. *)
let err_CRASH = 99L

let crash_label = "?crash"

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos)

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

let heap_reg = R15

let scratch_reg = R11

let scratch_reg2 = R10

let not_a_number_comp_label = "?error_not_number_comp"

let not_a_number_arith_label = "?error_not_number_arith"

let not_a_bool_logic_label = "?error_not_bool_logic"

let not_a_bool_if_label = "?error_not_bool_if"

let overflow_label = "?error_overflow"

(* Errors for tuples *)
let not_a_tuple_access_label = "?error_not_tuple_access"

let not_a_number_index_label = "?error_not_number_index"

let index_high_label = "?error_get_high_index"

let index_low_label = "?error_get_low_index"

let nil_deref_label = "?error_nil_deref"

let err_call_not_closure_label = "?err_not_closure"

let err_arity_mismatch_label = "?err_arity_mismatch"

let err_unpack_err_label = "?err_unpack_err"

let err_out_of_memory_label = "?err_out_of_memory"

let unpack_err_label = "?err_unpack_err"

let not_a_closure_label = "?err_not_closure"

let ocsh_name = "ocsh_0"

(* you can add any functions or data defined by the runtime here for future use *)

let assoc_to_map (assoc : (string * 'a) list) : 'a StringMap.t =
  List.fold_left (fun map (key, value) -> StringMap.add key value map) StringMap.empty assoc
;;

(* Merges two StringMap environments *)
let merge_envs env1 env2 = StringMap.union (fun _ first _ -> Some first) env1 env2

let initial_val_env = assoc_to_map []

let prim_bindings = assoc_to_map []

let native_fun_bindings = assoc_to_map []

let initial_fun_env = merge_envs prim_bindings native_fun_bindings

(* You may find some of these helpers useful *)

let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y, v) :: rest ->
      if y = x then
        v
      else
        find rest x
;;

(* let count_vars e =
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
;; *)

let rec replicate x i =
  if i = 0 then
    []
  else
    x :: replicate x (i - 1)
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

let rec find_opt (env : 'a name_envt) (elt : string) : 'a option = StringMap.find_opt elt env

(* Combines two name_envts into one, preferring the first one *)
let prepend env1 env2 =
  let rec help env1 env2 =
    match env1 with
    | [] -> env2
    | ((k, _) as fst) :: rst ->
        let rst_prepend = help rst env2 in
        if List.mem_assoc k env2 then
          rst_prepend
        else
          fst :: rst_prepend
  in
  help env1 env2
;;

let env_keys (e : 'a StringMap.t) : string list = fst @@ List.split @@ StringMap.bindings e

(* Scope_info stores the location where something was defined,
   and if it was a function declaration, then its type arity and argument arity *)
type scope_info = sourcespan * int option * int option

let is_well_formed (p : sourcespan program) : sourcespan program fallible =
  let rec wf_E e (env : scope_info name_envt) =
    debug_printf "In wf_E: %s\n" (ExtString.String.join ", " (env_keys env));
    match e with
    | ESeq (e1, e2, _) -> wf_E e1 env @ wf_E e2 env
    | ETuple (es, _) -> List.concat (List.map (fun e -> wf_E e env) es)
    | EGetItem (e, idx, _) -> wf_E e env @ wf_E idx env
    | ESetItem (e, idx, newval, _) -> wf_E e env @ wf_E idx env @ wf_E newval env
    | ENil _ -> []
    | EBool _ -> []
    | ENumber (n, loc) ->
        if n > Int64.div Int64.max_int 2L || n < Int64.div Int64.min_int 2L then
          [Overflow (n, loc)]
        else
          []
    | EId (x, loc) ->
        if find_one (env_keys env) x then
          []
        else
          [UnboundId (x, loc)]
    | EPrim1 (_, e, _) -> wf_E e env
    | EPrim2 (_, l, r, _) -> wf_E l env @ wf_E r env
    | EIf (c, t, f, _) -> wf_E c env @ wf_E t env @ wf_E f env
    | ELet (bindings, body, _) ->
        let rec find_locs x (binds : 'a bind list) : 'a list =
          match binds with
          | [] -> []
          | BBlank _ :: rest -> find_locs x rest
          | BName (y, _, loc) :: rest ->
              if x = y then
                loc :: find_locs x rest
              else
                find_locs x rest
          | BTuple (binds, _) :: rest -> find_locs x binds @ find_locs x rest
        in
        let rec find_dupes (binds : 'a bind list) : exn list =
          match binds with
          | [] -> []
          | BBlank _ :: rest -> find_dupes rest
          | BName (x, _, def) :: rest ->
              List.map (fun use -> DuplicateId (x, use, def)) (find_locs x rest) @ find_dupes rest
          | BTuple (binds, _) :: rest -> find_dupes (binds @ rest)
        in
        let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) bindings) in
        let rec process_binds (rem_binds : 'a bind list) (env : scope_info name_envt) =
          match rem_binds with
          | [] -> (env, [])
          | BBlank _ :: rest -> process_binds rest env
          | BTuple (binds, _) :: rest -> process_binds (binds @ rest) env
          | BName (x, allow_shadow, xloc) :: rest ->
              let shadow =
                if allow_shadow then
                  []
                else
                  match find_opt env x with
                  | None -> []
                  | Some (existing, _, _) -> [ShadowId (x, xloc, existing)]
              in
              let new_env = StringMap.add x (xloc, None, None) env in
              let newer_env, errs = process_binds rest new_env in
              (newer_env, shadow @ errs)
        in
        let rec process_bindings bindings (env : scope_info name_envt) =
          match bindings with
          | [] -> (env, [])
          | (b, e, _) :: rest ->
              let errs_e = wf_E e env in
              let env', errs = process_binds [b] env in
              let env'', errs' = process_bindings rest env' in
              (env'', errs @ errs_e @ errs')
        in
        let env2, errs = process_bindings bindings env in
        dupeIds @ errs @ wf_E body env2
    | EApp (func, args, _, loc) ->
        let rec_errors = List.concat (List.map (fun e -> wf_E e env) (func :: args)) in
        ( match func with
        | EId (funname, _) -> (
          match find_opt env funname with
          | Some (_, _, Some arg_arity) ->
              let actual = List.length args in
              if actual != arg_arity then
                [Arity (arg_arity, actual, loc)]
              else
                []
          | _ -> [] )
        | _ -> [] )
        @ rec_errors
    | ELetRec (binds, body, _) ->
        let nonfuns =
          List.find_all
            (fun b ->
              match b with
              | BName _, ELambda _, _ -> false
              | _ -> true )
            binds
        in
        let nonfun_errs = List.map (fun (b, _, where) -> LetRecNonFunction (b, where)) nonfuns in
        let rec find_locs x (binds : 'a bind list) : 'a list =
          match binds with
          | [] -> []
          | BBlank _ :: rest -> find_locs x rest
          | BName (y, _, loc) :: rest ->
              if x = y then
                loc :: find_locs x rest
              else
                find_locs x rest
          | BTuple (binds, _) :: rest -> find_locs x binds @ find_locs x rest
        in
        let rec find_dupes (binds : 'a bind list) : exn list =
          match binds with
          | [] -> []
          | BBlank _ :: rest -> find_dupes rest
          | BName (x, _, def) :: rest ->
              List.map (fun use -> DuplicateId (x, use, def)) (find_locs x rest)
          | BTuple (binds, _) :: rest -> find_dupes (binds @ rest)
        in
        let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) binds) in
        let rec process_binds (rem_binds : sourcespan bind list) (env : scope_info name_envt) =
          match rem_binds with
          | [] -> (env, [])
          | BBlank _ :: rest -> process_binds rest env
          | BTuple (binds, _) :: rest -> process_binds (binds @ rest) env
          | BName (x, allow_shadow, xloc) :: rest ->
              let shadow =
                if allow_shadow then
                  []
                else
                  match find_opt env x with
                  | None -> []
                  | Some (existing, _, _) ->
                      if xloc = existing then
                        []
                      else
                        [ShadowId (x, xloc, existing)]
              in
              let new_env = StringMap.add x (xloc, None, None) env in
              let newer_env, errs = process_binds rest new_env in
              (newer_env, shadow @ errs)
        in
        let env, bind_errs = process_binds (List.map (fun (b, _, _) -> b) binds) env in
        let rec process_bindings bindings env =
          match bindings with
          | [] -> (env, [])
          | (b, e, _) :: rest ->
              let env, errs = process_binds [b] env in
              let errs_e = wf_E e env in
              let env', errs' = process_bindings rest env in
              (env', errs @ errs_e @ errs')
        in
        let new_env, binding_errs = process_bindings binds env in
        let rhs_problems = List.map (fun (_, rhs, _) -> wf_E rhs new_env) binds in
        let body_problems = wf_E body new_env in
        nonfun_errs @ dupeIds @ bind_errs @ binding_errs @ List.flatten rhs_problems @ body_problems
    | ELambda (binds, body, _) ->
        let rec dupe x args =
          match args with
          | [] -> None
          | BName (y, _, loc) :: _ when x = y -> Some loc
          | BTuple (binds, _) :: rest -> dupe x (binds @ rest)
          | _ :: rest -> dupe x rest
        in
        let rec process_args rem_args =
          match rem_args with
          | [] -> []
          | BBlank _ :: rest -> process_args rest
          | BName (x, _, loc) :: rest ->
              ( match dupe x rest with
              | None -> []
              | Some where -> [DuplicateId (x, where, loc)] )
              @ process_args rest
          | BTuple (binds, _) :: rest -> process_args (binds @ rest)
        in
        let rec flatten_bind (bind : sourcespan bind) : (string * scope_info) list =
          match bind with
          | BBlank _ -> []
          | BName (x, _, xloc) -> [(x, (xloc, None, None))]
          | BTuple (args, _) -> List.concat (List.map flatten_bind args)
        in
        process_args binds
        @ wf_E body (merge_envs (assoc_to_map (List.concat (List.map flatten_bind binds))) env)
  and wf_D d (env : scope_info name_envt) =
    match d with
    | DFun (_, args, body, _) ->
        let rec dupe x args =
          match args with
          | [] -> None
          | BName (y, _, loc) :: _ when x = y -> Some loc
          | BTuple (binds, _) :: rest -> dupe x (binds @ rest)
          | _ :: rest -> dupe x rest
        in
        let rec process_args rem_args =
          match rem_args with
          | [] -> []
          | BBlank _ :: rest -> process_args rest
          | BName (x, _, loc) :: rest ->
              ( match dupe x rest with
              | None -> []
              | Some where -> [DuplicateId (x, where, loc)] )
              @ process_args rest
          | BTuple (binds, _) :: rest -> process_args (binds @ rest)
        in
        let rec arg_env args (env : scope_info name_envt) =
          match args with
          | [] -> env
          | BBlank _ :: rest -> arg_env rest env
          | BName (name, _, loc) :: rest -> StringMap.add name (loc, None, None) (arg_env rest env)
          | BTuple (binds, _) :: rest -> arg_env (binds @ rest) env
        in
        process_args args @ wf_E body (arg_env args env)
  and wf_G (g : sourcespan decl list) (env : scope_info name_envt) =
    let add_funbind (env : scope_info name_envt) d =
      match d with
      | DFun (name, args, _, loc) ->
          StringMap.add name (loc, Some (List.length args), Some (List.length args)) env
    in
    let env = List.fold_left add_funbind env g in
    let errs = List.concat (List.map (fun d -> wf_D d env) g) in
    (errs, env)
  in
  match p with
  | Program (decls, body, _) -> (
      let initial_env = initial_val_env in
      let initial_env =
        merge_envs initial_fun_env
          (StringMap.map
             (fun (_, arg_count) -> (dummy_span, Some arg_count, Some arg_count))
             initial_env )
      in
      let rec find name (decls : 'a decl list) =
        match decls with
        | [] -> None
        | DFun (n, _, _, loc) :: _ when n = name -> Some loc
        | _ :: rest -> find name rest
      in
      let rec dupe_funbinds decls =
        match decls with
        | [] -> []
        | DFun (name, _, _, loc) :: rest ->
            ( match find name rest with
            | None -> []
            | Some where -> [DuplicateFun (name, where, loc)] )
            @ dupe_funbinds rest
      in
      let all_decls = List.flatten decls in
      let help_G (env, exns) g =
        let g_exns, funbinds = wf_G g env in
        (merge_envs env funbinds, exns @ g_exns)
      in
      let env, exns = List.fold_left help_G (initial_env, dupe_funbinds all_decls) decls in
      debug_printf "In wf_P: %s\n" (ExtString.String.join ", " (env_keys env));
      let exns = exns @ wf_E body env in
      match exns with
      | [] -> Ok p
      | _ -> Error exns )
;;

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;; DESUGARING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)

let desugar (p : sourcespan program) : sourcespan program =
  let gensym =
    let next = ref 0 in
    fun name ->
      next := !next + 1;
      sprintf "%s_%d" name !next
  in
  let rec helpP (p : sourcespan program) =
    match p with
    | Program (decls, body, tag) ->
        (* This particular desugaring will convert declgroups into ELetRecs *)
        let merge_sourcespans ((s1, _) : sourcespan) ((_, s2) : sourcespan) : sourcespan =
          (s1, s2)
        in
        let wrap_G g body =
          match g with
          | [] -> body
          | f :: r ->
              let span = List.fold_left merge_sourcespans (get_tag_D f) (List.map get_tag_D r) in
              ELetRec (helpG g, body, span)
        in
        Program ([], List.fold_right wrap_G decls (helpE body), tag)
  and helpG g = List.map helpD g
  and helpD d =
    match d with
    | DFun (name, args, body, tag) ->
        let helpArg a =
          match a with
          | BTuple (_, tag) ->
              let name = gensym "argtup" in
              let newbind = BName (name, false, tag) in
              (newbind, [(a, EId (name, tag), tag)])
          | _ -> (a, [])
        in
        let newargs, argbinds = List.split (List.map helpArg args) in
        let newbody = ELet (List.flatten argbinds, body, tag) in
        (BName (name, false, tag), ELambda (newargs, helpE newbody, tag), tag)
  and helpBE bind =
    let b, e, btag = bind in
    let e = helpE e in
    match b with
    | BTuple (binds, ttag) -> (
      match e with
      | EId _ -> expandTuple binds ttag e
      | _ ->
          let newname = gensym "tup" in
          (BName (newname, false, ttag), e, btag) :: expandTuple binds ttag (EId (newname, ttag)) )
    | _ -> [(b, e, btag)]
  and expandTuple binds tag source : sourcespan binding list =
    let tupleBind i b =
      match b with
      | BBlank _ -> []
      | BName (_, _, btag) ->
          [(b, EGetItem (source, ENumber (Int64.of_int i, dummy_span), tag), btag)]
      | BTuple (binds, tag) ->
          let newname = gensym "tup" in
          let newexpr = EId (newname, tag) in
          ( BName (newname, false, tag),
            EGetItem (source, ENumber (Int64.of_int i, dummy_span), tag),
            tag )
          :: expandTuple binds tag newexpr
    in
    let size_check =
      EPrim2 (CheckSize, source, ENumber (Int64.of_int (List.length binds), dummy_span), dummy_span)
    in
    let size_check_bind = (BBlank dummy_span, size_check, dummy_span) in
    size_check_bind :: List.flatten (List.mapi tupleBind binds)
  and helpE e =
    match e with
    | ESeq (e1, e2, tag) -> ELet ([(BBlank tag, helpE e1, tag)], helpE e2, tag)
    | ETuple (exprs, tag) -> ETuple (List.map helpE exprs, tag)
    | EGetItem (e, idx, tag) -> EGetItem (helpE e, helpE idx, tag)
    | ESetItem (e, idx, newval, tag) -> ESetItem (helpE e, helpE idx, helpE newval, tag)
    | EId (x, tag) -> EId (x, tag)
    | ENumber (n, tag) -> ENumber (n, tag)
    | EBool (b, tag) -> EBool (b, tag)
    | ENil (t, tag) -> ENil (t, tag)
    | EPrim1 (op, e, tag) -> EPrim1 (op, helpE e, tag)
    | EPrim2 (op, e1, e2, tag) -> EPrim2 (op, helpE e1, helpE e2, tag)
    | ELet (binds, body, tag) ->
        let newbinds = List.map helpBE binds in
        List.fold_right (fun binds body -> ELet (binds, body, tag)) newbinds (helpE body)
    | ELetRec (bindexps, body, tag) ->
        (* ASSUMES well-formed letrec, so only BName bindings *)
        let newbinds = List.map (fun (bind, e, tag) -> (bind, helpE e, tag)) bindexps in
        ELetRec (newbinds, helpE body, tag)
    | EIf (cond, thn, els, tag) -> EIf (helpE cond, helpE thn, helpE els, tag)
    | EApp (name, args, native, tag) -> EApp (helpE name, List.map helpE args, native, tag)
    | ELambda (binds, body, tag) ->
        let expandBind bind =
          match bind with
          | BTuple (_, btag) ->
              let newparam = gensym "tuparg" in
              (BName (newparam, false, btag), helpBE (bind, EId (newparam, btag), btag))
          | _ -> (bind, [])
        in
        let params, newbinds = List.split (List.map expandBind binds) in
        let newbody =
          List.fold_right (fun binds body -> ELet (binds, body, tag)) newbinds (helpE body)
        in
        ELambda (params, newbody, tag)
  in
  helpP p
;;

(* ASSUMES desugaring is complete *)
let rename_and_tag (p : tag program) : tag program =
  let rec rename env p =
    match p with
    | Program (decls, body, tag) ->
        Program (List.map (fun group -> List.map (helpD env) group) decls, helpE env body, tag)
  and helpD env decl =
    match decl with
    | DFun (name, args, body, tag) ->
        let newArgs, env' = helpBS env args in
        DFun (name, newArgs, helpE env' body, tag)
  and helpB env b =
    match b with
    | BBlank _ -> (b, env)
    | BName (name, allow_shadow, tag) ->
        let name' = sprintf "%s_%d" name tag in
        (BName (name', allow_shadow, tag), (name, name') :: env)
    | BTuple (binds, tag) ->
        let binds', env' = helpBS env binds in
        (BTuple (binds', tag), env')
  and helpBS env (bs : tag bind list) =
    match bs with
    | [] -> ([], env)
    | b :: bs ->
        let b', env' = helpB env b in
        let bs', env'' = helpBS env' bs in
        (b' :: bs', env'')
  and helpBG env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a) :: bindings ->
        let b', env' = helpB env b in
        let e' = helpE env e in
        let bindings', env'' = helpBG env' bindings in
        ((b', e', a) :: bindings', env'')
  and helpE env e =
    match e with
    | ESeq (e1, e2, tag) -> ESeq (helpE env e1, helpE env e2, tag)
    | ETuple (es, tag) -> ETuple (List.map (helpE env) es, tag)
    | EGetItem (e, idx, tag) -> EGetItem (helpE env e, helpE env idx, tag)
    | ESetItem (e, idx, newval, tag) -> ESetItem (helpE env e, helpE env idx, helpE env newval, tag)
    | EPrim1 (op, arg, tag) -> EPrim1 (op, helpE env arg, tag)
    | EPrim2 (op, left, right, tag) -> EPrim2 (op, helpE env left, helpE env right, tag)
    | EIf (c, t, f, tag) -> EIf (helpE env c, helpE env t, helpE env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId (name, tag) -> ( try EId (find env name, tag) with InternalCompilerError _ -> e )
    | EApp (func, args, _, tag) ->
        let func = helpE env func in
        let call_type =
          (* TODO: If you want, try to determine whether func is a known function name, and if so,
             whether it's a Snake function or a Native function *)
          Snake
        in
        EApp (func, List.map (helpE env) args, call_type, tag)
    | ELet (binds, body, tag) ->
        let binds', env' = helpBG env binds in
        let body' = helpE env' body in
        ELet (binds', body', tag)
    | ELetRec (bindings, body, tag) ->
        let revbinds, env =
          List.fold_left
            (fun (revbinds, env) (b, e, t) ->
              let b, env = helpB env b in
              ((b, e, t) :: revbinds, env) )
            ([], env) bindings
        in
        let bindings' =
          List.fold_left (fun bindings (b, e, tag) -> (b, helpE env e, tag) :: bindings) [] revbinds
        in
        let body' = helpE env body in
        ELetRec (bindings', body', tag)
    | ELambda (binds, body, tag) ->
        let binds', env' = helpBS env binds in
        let body' = helpE env' body in
        ELambda (binds', body', tag)
  in
  rename [] p
;;

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;; ANFING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)

type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program ([], body, _) -> AProgram (helpA body, ())
    | Program _ -> raise (InternalCompilerError "decls should have been desugared away")
  and helpC (e : tag expr) : unit cexpr * unit anf_bind list =
    match e with
    | EPrim1 (op, arg, _) ->
        let arg_imm, arg_setup = helpI arg in
        (CPrim1 (op, arg_imm, ()), arg_setup)
    | EPrim2 (op, left, right, _) ->
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (CPrim2 (op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf (cond, _then, _else, _) ->
        let cond_imm, cond_setup = helpI cond in
        (CIf (cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ELet ([], body, _) -> helpC body
    | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELet ((BName (bind, _, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELetRec (binds, body, _) ->
        let processBind (bind, rhs, _) =
          match bind with
          | BName (name, _, _) -> (name, helpC rhs)
          | _ ->
              raise
                (InternalCompilerError
                   (sprintf "Encountered a non-simple binding in ANFing a let-rec: %s"
                      (string_of_bind bind) ) )
        in
        let names, new_binds_setup = List.split (List.map processBind binds) in
        let new_binds, new_setup = List.split new_binds_setup in
        let body_ans, body_setup = helpC body in
        (body_ans, List.concat new_setup @ (BLetRec (List.combine names new_binds) :: body_setup))
    | ELambda (args, body, tag) ->
        let processBind bind =
          match bind with
          | BName (name, _, _) -> name
          | _ ->
              raise
                (InternalCompilerError
                   (sprintf "Encountered a non-simple binding in ANFing a lambda: %s"
                      (string_of_bind bind) ) )
        in
        let new_clambda = CLambda (List.map processBind args, helpA body, ()) in
        let name = sprintf "lam_%d" tag in
        let imm_id = ImmId (name, ()) in
        (CImmExpr imm_id, [BLet (name, new_clambda)])
    | ELet ((BTuple (_, _), _, _) :: _, _, _) ->
        raise (InternalCompilerError "Tuple bindings should have been desugared away")
    | EApp (func, args, native, _) ->
        let func_ans, func_setup = helpI func in
        let new_args, new_setup = List.split (List.map helpI args) in
        (CApp (func_ans, new_args, native, ()), func_setup @ List.concat new_setup)
    | ESeq (e1, e2, _) ->
        let e1_ans, e1_setup = helpC e1 in
        let e2_ans, e2_setup = helpC e2 in
        (e2_ans, e1_setup @ [BSeq e1_ans] @ e2_setup)
    | ETuple (args, _) ->
        let new_args, new_setup = List.split (List.map helpI args) in
        (CTuple (new_args, ()), List.concat new_setup)
    | EGetItem (tup, idx, _) ->
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        (CGetItem (tup_imm, idx_imm, ()), tup_setup @ idx_setup)
    | ESetItem (tup, idx, newval, _) ->
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let new_imm, new_setup = helpI newval in
        (CSetItem (tup_imm, idx_imm, new_imm, ()), tup_setup @ idx_setup @ new_setup)
    | _ ->
        let imm, setup = helpI e in
        (CImmExpr imm, setup)
  and helpI (e : tag expr) : unit immexpr * unit anf_bind list =
    match e with
    | ENumber (n, _) -> (ImmNum (n, ()), [])
    | EBool (b, _) -> (ImmBool (b, ()), [])
    | EId (name, _) -> (ImmId (name, ()), [])
    | ENil _ -> (ImmNil (), [])
    | ESeq (e1, e2, _) ->
        let _, e1_setup = helpI e1 in
        let e2_imm, e2_setup = helpI e2 in
        (e2_imm, e1_setup @ e2_setup)
    | ETuple (args, tag) ->
        let tmp = sprintf "tup_%d" tag in
        let new_args, new_setup = List.split (List.map helpI args) in
        (ImmId (tmp, ()), List.concat new_setup @ [BLet (tmp, CTuple (new_args, ()))])
    | EGetItem (tup, idx, tag) ->
        let tmp = sprintf "get_%d" tag in
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        (ImmId (tmp, ()), tup_setup @ idx_setup @ [BLet (tmp, CGetItem (tup_imm, idx_imm, ()))])
    | ESetItem (tup, idx, newval, tag) ->
        let tmp = sprintf "set_%d" tag in
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let new_imm, new_setup = helpI newval in
        ( ImmId (tmp, ()),
          tup_setup @ idx_setup @ new_setup @ [BLet (tmp, CSetItem (tup_imm, idx_imm, new_imm, ()))]
        )
    | EPrim1 (op, arg, tag) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (ImmId (tmp, ()), arg_setup @ [BLet (tmp, CPrim1 (op, arg_imm, ()))])
    | EPrim2 (op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        ( ImmId (tmp, ()),
          left_setup @ right_setup @ [BLet (tmp, CPrim2 (op, left_imm, right_imm, ()))] )
    | EIf (cond, _then, _else, tag) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        (ImmId (tmp, ()), cond_setup @ [BLet (tmp, CIf (cond_imm, helpA _then, helpA _else, ()))])
    | EApp (func, args, native, tag) ->
        let tmp = sprintf "app_%d" tag in
        let new_func, func_setup = helpI func in
        let new_args, new_setup = List.split (List.map helpI args) in
        ( ImmId (tmp, ()),
          func_setup @ List.concat new_setup @ [BLet (tmp, CApp (new_func, new_args, native, ()))]
        )
    | ELet ([], body, _) -> helpI body
    | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELetRec (binds, body, tag) ->
        let tmp = sprintf "lam_%d" tag in
        let processBind (bind, rhs, _) =
          match bind with
          | BName (name, _, _) -> (name, helpC rhs)
          | _ ->
              raise
                (InternalCompilerError
                   (sprintf "Encountered a non-simple binding in ANFing a let-rec: %s"
                      (string_of_bind bind) ) )
        in
        let names, new_binds_setup = List.split (List.map processBind binds) in
        let new_binds, new_setup = List.split new_binds_setup in
        let body_ans, body_setup = helpC body in
        ( ImmId (tmp, ()),
          List.concat new_setup
          @ [BLetRec (List.combine names new_binds)]
          @ body_setup
          @ [BLet (tmp, body_ans)] )
    | ELambda (args, body, tag) ->
        let tmp = sprintf "lam_%d" tag in
        let processBind bind =
          match bind with
          | BName (name, _, _) -> name
          | _ ->
              raise
                (InternalCompilerError
                   (sprintf "Encountered a non-simple binding in ANFing a lambda: %s"
                      (string_of_bind bind) ) )
        in
        (ImmId (tmp, ()), [BLet (tmp, CLambda (List.map processBind args, helpA body, ()))])
    | ELet ((BName (bind, _, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELet ((BTuple (_, _), _, _) :: _, _, _) ->
        raise (InternalCompilerError "Tuple bindings should have been desugared away")
  and helpA e : unit aexpr =
    let ans, ans_setup = helpC e in
    List.fold_right
      (fun bind body ->
        match bind with
        | BSeq exp -> ASeq (exp, body, ())
        | BLet (name, exp) -> ALet (name, exp, body, ())
        | BLetRec names -> ALetRec (names, body, ()) )
      ans_setup (ACExpr ans)
  in
  helpP p
;;

(* For convenience. 
 * In general, I like the infix syntax `|> u` for union.
 *)
let u = StringSet.union

(* Is it more convenient to return a StringSet, or just to slap a to_list at the end? *)
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
  ExtString.String.join "\n"
    (List.map (fun (name, arg) -> name ^ "=>" ^ arg_to_asm arg) (StringMap.bindings env))
;;

let safe_find_opt ?callee_tag:(addn = "") key map =
  let maybe_thing = StringMap.find_opt key map in
  match maybe_thing with
  | None -> raise (InternalCompilerError (sprintf "Unable to find thing: %s. %s" key addn))
  | Some thing -> thing
;;

let si_to_arg (si : int) : arg = RegOffset (~-si, RBP)

(* IMPLEMENT THIS FROM YOUR PREVIOUS ASSIGNMENT *)

(* We chose to use `arg name_envt name_envt` as the type here.
 * This allows us to be more flippant with tags, since they lose their
 * semantic value after we are done with them.
 * Instead, we used names. Specifically, we used the name to which a lambda is bound.
 * (Using a name based on the tag is cheating.)
 * Most lambdas are bound, but some are not, e.g. `(lambda(x): x)(5)`.
 * To handle this, we changed ANF to wrap all lambdas in another binding, in rough terms:
 * `let foo = <lambda>` => `let lam_tmp = <lambda>, foo = lam_tmp`.
 * or: `<lambda>(5)` => `let lam_tmp = <lambda> in lam_tmp(5)`.
 * This way, the sub-environment name is structural, instead of being metadata-driven.
 *)

let naive_stack_allocation (AProgram (body, _) as prog : tag aprogram) :
    tag aprogram * arg name_envt name_envt =
  let rec helpC (cexp : tag cexpr) (env : arg name_envt name_envt) (si : int) (env_name : string) :
      arg name_envt name_envt =
    match cexp with
    | CPrim1 _ | CPrim2 _ | CApp _ | CImmExpr _ | CTuple _ | CGetItem _ | CSetItem _ -> env
    | CIf (_, thn, els, _) ->
        let thn_env = helpA thn env (si + 1) env_name in
        helpA els thn_env (si + 1) env_name
    | CLambda (ids, body, _) ->
        (* TODO: revisit adding 2 instead of 1 (we add 2 because before the ids 
         *       we put RBP and the return address (?)) 

         * Actually, we add 3, to account for the implicit 'self' argument.
         *)
        let args_locs = List.mapi (fun index id -> (id, RegOffset (index + 3, RBP))) ids in
        let args_env =
          List.fold_left
            (fun envt_envt (id, location) -> update_envt_envt env_name id location envt_envt)
            env args_locs
        in
        helpA body args_env 1 env_name
  and helpA (aexp : tag aexpr) (env : arg name_envt name_envt) (si : int) (env_name : string) :
      arg name_envt name_envt =
    match aexp with
    | ACExpr cexp -> helpC cexp env si env_name
    | ASeq (first, next, _) ->
        (* Order matters here? *)
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
        let offset = si_to_arg si in
        let body_offset = helpA body add_base_env_for_lambda (si + 1) env_name in
        let cur_envt = update_envt_envt env_name id offset body_offset in
        let lambda_offset = helpC lambda cur_envt si id in
        (* TODO: Think about this a little more. Is there too much indirection? *)
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
    (* | ALetRec ((id, bound) :: _, _, _) -> *)
    (* let binders, _ = List.split binds in
        let located_binders = List.mapi (fun i binder -> (binder, si_to_arg (i + si))) binders in
        (* let binder_buffer = si + List.length located_binders in *)
        let binds_env = List.fold_left
          (fun (acc_env : arg name_envt name_envt) ((id : string), (bound : tag cexpr)) ->
            match bound with
            | CLambda _ ->
                let add_base_env_for_lambda = StringMap.add id (assoc_to_map located_binders) acc_env in
                let bound_offset = helpC bound add_base_env_for_lambda si id in
                bound_offset
            | _ ->
                raise
                  (InternalCompilerError
                     (sprintf "Tried to allocate a non-lambda value in LetRec!: %s => %s" id
                        (string_of_cexpr bound) ) ) )
          env binds in
          let body_offset = helpA body binds_env (si + 1) env_name in
          body_offset *)
  in
  (* TODO: Change the name of the OCSH environment? *)
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

(* Returns the stack-index (in words) of the deepest stack index used for any
   of the variables in this expression *)
let rec deepest_stack_old e (env : arg name_envt) =
  let rec helpA e =
    match e with
    (* TODO: THIS IS THE CASE THAT SMELLS BAD *)
    (* | ALet (name, (CLambda _ as lambda), body, _) ->
        let new_env = StringMap.add name (RegOffset (1, RBP)) env in
        List.fold_left max 0
          [(*This number is a place holder ->*) 1; helpC lambda; deepest_stack body new_env] *)
    | ALet (name, bind, body, _) ->
        List.fold_left max 0 [name_to_offset name; helpC bind; helpA body]
    | ALetRec (binds, body, _) ->
        List.fold_left max (helpA body) (List.map (fun (name, _) -> name_to_offset name) binds)
    | ASeq (first, rest, _) -> max (helpC first) (helpA rest)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (c, t, f, _) -> List.fold_left max 0 [helpI c; helpA t; helpA f]
    | CPrim1 (_, i, _) -> helpI i
    | CPrim2 (_, i1, i2, _) -> max (helpI i1) (helpI i2)
    | CApp (func, args, _, _) -> max (helpI func) (List.fold_left max 0 (List.map helpI args))
    | CTuple (vals, _) -> List.fold_left max 0 (List.map helpI vals)
    | CGetItem (t, _, _) -> helpI t
    | CSetItem (t, _, v, _) -> max (helpI t) (helpI v)
    | CLambda (args, body, _) ->
        let new_mappings = assoc_to_map (List.mapi (fun i a -> (a, RegOffset (i + 3, RBP))) args) in
        let new_env = merge_envs new_mappings env in
        deepest_stack_old body new_env
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNil _ -> 0
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmId (name, _) -> name_to_offset name
  and name_to_offset name =
    match
      safe_find_opt name env
        ~callee_tag:(sprintf "DEEPEST_STACK! id: %s, env: %s" name (string_of_name_envt env))
    with
    | RegOffset (words, RBP) -> words / -1 (* negative because stack direction *)
    | _ -> 0
  in
  max (helpA e) 0 (* if only parameters are used, helpA might return a negative value *)
;;

let rec deepest_stack (env : arg name_envt) : int =
  StringMap.fold
    (fun _ value acc ->
      match value with
      | RegOffset (words, _) -> max (words / ~-1) acc
      | _ -> raise (InternalCompilerError "Encountered non-RegOffset in deepest_stack2") )
    env 0
;;

let move_with_scratch arg1 arg2 = [IMov (Reg scratch_reg, arg2); IMov (arg1, Reg scratch_reg)]

(* Sets the last four bits of the value in thze given location to 0. *)
let untag_snakeval arg = IAnd (arg, HexConst 0xFFFFFFF8L)

let crash = [IJmp (Label index_high_label)]

let check_tag value tag err_label =
  [ IMov (Reg scratch_reg, value);
    IAnd (Reg scratch_reg, Const 0x7L);
    (* 0x7 = 0...01111, i.e. the tag bits.*)
    ICmp (Reg scratch_reg, Const tag);
    IJne (Label err_label) ]
;;

(* Enforces that the value in RAX is a bool. Goes to the specified label if not. *)
(* We could check a parameterized register, but that creates complexity in reporting the error. *)
(* We opt to hard-code RAX, for more consistency in exchange for some more boiler-plate code. *)
let check_bool (goto : string) : instruction list =
  [ IMov (Reg scratch_reg2, Reg RAX);
    IMov (Reg scratch_reg, HexConst bool_tag_mask);
    IAnd (Reg scratch_reg2, Reg scratch_reg);
    ICmp (Reg scratch_reg2, HexConst bool_tag);
    IJnz (Label goto) ]
;;

(* Enforces that the value in RAX is a num. Goes to the specified label if not. *)
let check_num (goto : string) : instruction list =
  [ IMov (Reg scratch_reg, HexConst num_tag_mask);
    ITest (Reg RAX, Reg scratch_reg);
    IJnz (Label goto) ]
;;

(* Enforces that the value in RAX is a tuple. Goes to the specified label if not. *)
let check_tuple (goto : string) : instruction list =
  (* This mangles RAX, btw.
     We must either reset rax after this,
     or use a temp register here.
  *)
  [ IMov (Reg scratch_reg2, Reg RAX);
    IAnd (Reg scratch_reg2, HexConst tuple_tag_mask);
    IMov (Reg scratch_reg, HexConst tuple_tag);
    ICmp (Reg scratch_reg2, Reg scratch_reg);
    IJnz (Label goto) ]
;;

(* Enforces that the value in RAX is not nil. Goes to the specified label if it is. *)
let check_not_nil (goto : string) : instruction list =
  [IMov (Reg scratch_reg, HexConst tuple_tag); ICmp (Reg RAX, Reg scratch_reg); IJz (Label goto)]
;;

let check_overflow = IJo (Label overflow_label)

(* Checks that the value in the given location ends in 0x5 (the closure tag).
 * With this and `check_arity`, we make sure not to edit the original register.
 * We need to preserve the tag!
 *)
let check_function =
  [ IMov (Reg scratch_reg, Reg RAX);
    IAnd (Reg scratch_reg, Const closure_tag_mask);
    (* put the checked value into RAX before potentially jumping.*)
    ICmp (Reg scratch_reg, Const closure_tag);
    IJne (Label err_call_not_closure_label) ]
;;

(* Assumes that the given argument is a function! *)
let check_arity (arity : int) =
  let arity_const = Const (Int64.of_int (arity * 2)) in
  [ (* Remove the tag *)
    ISub (Reg RAX, HexConst closure_tag);
    (* The function arity is the first value stored.
     * It is stored as a SNAKEVAL.
     *)
    ICmp (Sized (QWORD_PTR, RegOffset (0, RAX)), arity_const);
    IMov (Reg RSI, arity_const);
    IJne (Label err_arity_mismatch_label) ]
;;

let check_memory size =
  [ IMov (Reg scratch_reg, Const size);
    IAdd (Reg scratch_reg, Reg heap_reg);
    IMov (Reg scratch_reg2, RelLabel heap_end_label);
    ICmp (Reg scratch_reg, Reg scratch_reg2);
    IJge (Label err_out_of_memory_label) ]
;;

(* Helper for numeric comparisons *)
let compare_prim2 (op : prim2) (e1 : arg) (e2 : arg) (t : tag) : instruction list =
  (* Move the first arg into RAX so we can type-check it. *)
  let string_op = "comparison_label" in
  let comp_label = sprintf "%s#%d" string_op t in
  let jump =
    match op with
    | Greater -> IJg (Label comp_label)
    | GreaterEq -> IJge (Label comp_label)
    | Less -> IJl (Label comp_label)
    | LessEq -> IJle (Label comp_label)
    | _ -> raise (InternalCompilerError "Expected comparison operator.")
  in
  let comp_done_label = sprintf "%s_done#%d" string_op t in
  [IMov (Reg RAX, e1)]
  @ check_num not_a_number_comp_label
  @ [IMov (Reg RAX, e2)]
  @ check_num not_a_number_comp_label
  @ [ ILineComment (sprintf "BEGIN %s#%d -------------" string_op t);
      IMov (Reg RAX, e1);
      (* cmp is weird and breaks if we don't use a temp register... *)
      IMov (Reg scratch_reg, e2);
      ICmp (Reg RAX, Reg scratch_reg);
      jump;
      IMov (Reg RAX, const_false);
      IJmp (Label comp_done_label);
      ILabel comp_label;
      IMov (Reg RAX, const_true);
      ILabel comp_done_label;
      ILineComment (sprintf "END %s#%d   -------------" string_op t) ]
;;

(* Helper for arithmetic operations *)
let arithmetic_prim2 (op : prim2) (e1 : arg) (e2 : arg) : instruction list =
  (* Move the first arg into RAX so we can type-check it. *)
  [IMov (Reg RAX, e1)]
  @ check_num not_a_number_arith_label
  @ [IMov (Reg RAX, e2)]
  @ check_num not_a_number_arith_label
  @
  match op with
  (* Arithmetic operators *)
  | Plus -> [IMov (Reg scratch_reg, e1); IAdd (Reg RAX, Reg scratch_reg); check_overflow]
  (* Make sure to check for overflow BEFORE shifting on multiplication! *)
  | Times ->
      [ IMov (Reg scratch_reg, e1);
        IMul (Reg RAX, Reg scratch_reg);
        check_overflow;
        ISar (Reg RAX, Const 1L) ]
  (* For minus, we need to move e1 back into RAX to compensate for the lack of commutativity, 
   * while also preserving the order in which our arguments will fail a typecheck.
   * So, `false - true` will fail on `false` every time.
   *)
  | Minus ->
      [ IMov (Reg scratch_reg, e2);
        IMov (Reg RAX, e1);
        ISub (Reg RAX, Reg scratch_reg);
        check_overflow ]
  (* Comparison operators *)
  | _ -> raise (InternalCompilerError "Expected arithmetic operator.")
;;

(* Helper for boolean and *)
let and_prim2 (e1 : arg) (e2 : arg) (t : tag) : instruction list =
  let true_label = sprintf "true#%d" t in
  let false_label = sprintf "false#%d" t in
  let logic_done_label = sprintf "and_done#%d" t in
  [ ILineComment (sprintf "BEGIN and#%d -------------" t);
    (* Move the first arg into RAX so we can type-check it. *)
    IMov (Reg RAX, e1) ]
  @ check_bool not_a_bool_logic_label
    (* In order to handle short-circuiting, we don't look at the second arg until later.
     * This means that `false and 5` will NOT raise a type error.
     *)
  @ [ IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJz (Label false_label);
      IMov (Reg RAX, e2) ]
  @ check_bool not_a_bool_logic_label
  @ [ (* Need to re-set scratch_reg since it gets changed in check_bool.*)
      IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJz (Label false_label);
      ILabel true_label;
      IMov (Reg RAX, const_true);
      IJmp (Label logic_done_label);
      ILabel false_label;
      IMov (Reg RAX, const_false);
      ILabel logic_done_label;
      ILineComment (sprintf "END and#%d   -------------" t) ]
;;

(* Helper for boolean or *)
let or_prim2 (e1 : arg) (e2 : arg) (t : tag) : instruction list =
  let true_label = sprintf "true#%d" t in
  let false_label = sprintf "false#%d" t in
  let logic_done_label = sprintf "or_done#%d" t in
  [ ILineComment (sprintf "BEGIN and#%d -------------" t);
    (* Move the first arg into RAX so we can type-check it. *)
    IMov (Reg RAX, e1) ]
  @ check_bool not_a_bool_logic_label
    (* In order to handle short-circuiting, we don't look at the second arg until later.
     * This means that `true or 5` will NOT raise a type error.
     *)
  @ [ IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJnz (Label true_label);
      IMov (Reg RAX, e2) ]
  @ check_bool not_a_bool_logic_label
  @ [ (* Need to re-set scratch_reg since it gets changed in check_bool.*)
      IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJnz (Label true_label);
      ILabel false_label;
      IMov (Reg RAX, const_false);
      IJmp (Label logic_done_label);
      ILabel true_label;
      IMov (Reg RAX, const_true);
      ILabel logic_done_label;
      ILineComment (sprintf "END or#%d   -------------" t) ]
;;

(* let rec replicate x i =
  if i = 0 then
    []
  else
    x :: replicate x (i - 1) *)

let rec reserve size tag =
  let ok = sprintf "$memcheck_%d" tag in
  [ IInstrComment
      (IMov (Reg RAX, LabelContents "?HEAP_END"), sprintf "Reserving %d words" (size / word_size));
    ISub (Reg RAX, Const (Int64.of_int size));
    ICmp (Reg RAX, Reg heap_reg);
    IJge (Label ok) ]
  @ native_call (Label "?try_gc")
      [ Sized (QWORD_PTR, Reg heap_reg);
        (* alloc_ptr in C *)
        Sized (QWORD_PTR, Const (Int64.of_int size));
        (* bytes_needed in C *)
        Sized (QWORD_PTR, Reg RBP);
        (* first_frame in C *)
        Sized (QWORD_PTR, Reg RSP) (* stack_top in C *) ]
  @ [ IInstrComment
        ( IMov (Reg heap_reg, Reg RAX),
          "assume gc success if returning here, so RAX holds the new heap_reg value" );
      ILabel ok ]

(* IMPLEMENT THIS FROM YOUR PREVIOUS ASSIGNMENT *)
(* Additionally, you are provided an initial environment of values that you may want to
   assume should take up the first few stack slots.  See the compiliation of Programs
   below for one way to use this ability... *)
and compile_fun name args body (env_env : arg name_envt name_envt) tag si free_var_offsets :
    instruction list * instruction list * instruction list =
  (* Debug instruction that terminates the program *)
  let env = safe_find_opt name env_env ~callee_tag:(sprintf "COMPILE_FUN! id: %s" name) in
  let fun_label = name in
  let after_label = name ^ "_end" in
  let acexp = ACExpr (CLambda (args, body, 0)) in
  (* let acexp = body in  *)
  let vars = deepest_stack env in
  let arity = List.length args in
  let free_vars = StringSet.elements (free_vars acexp) in
  (* The order we get these out of the set is not the same as their order on the stack. *)
  (* let free_var_regs = List.rev @@ List.mapi (fun i _ -> RegOffset (i + 3, RBP)) free_vars in *)
  let num_free = List.length free_vars in
  let load_closure =
    List.concat
      (List.mapi
         (fun i (arg : arg) ->
           match arg with
           (* Handles self-reference by tagging the heap pointer with the closure tag.
            * This works because we know that this closure will be on the top of the heap at this given moment.
            *)
           | Reg heap_reg ->
               [ IMov (Reg RAX, arg);
                 IAdd (Reg RAX, Const closure_tag);
                 IMov (Sized (QWORD_PTR, RegOffset (i + 3, heap_reg)), Reg RAX) ]
           | _ ->
               [ IMov (Sized (QWORD_PTR, Reg RAX), arg);
                 IMov (Sized (QWORD_PTR, RegOffset (i + 3, heap_reg)), Reg RAX) ] )
         free_var_offsets )
  in
  let stack_padding =
    if vars mod 2 = 1 then
      vars + 1
    else
      vars
  in
  let _, _, unpack_closure_instrs, new_env =
    (* This fold needs two counters, so it can't just be a mapi.
     * i: The index in the closure
     * j: The offset from RBP, where we will move the variable.
     *)
    List.fold_left
      (fun (i, j, acc_instrs, old_env) id ->
        let offset = RegOffset (j, RBP) in
        ( (* Advance to the next word in the closure *)
          i + 1,
          (* Move up to the next slot above RBP *)
          j - 1,
          (* At this point in time, the closure pointer
           * should be stored in the scratch register. *)
          IMov (Reg RAX, RegOffset (i, scratch_reg)) (* Grab the closure ptr*)
          :: IMov (offset, Reg RAX) (* Put it where it belongs*)
          :: acc_instrs,
          update_envt_envt name id offset old_env ) )
      (* Start the index at 3 to skip the metadata words. *)
      (3, ~-1, [], env_env)
      free_vars
  in
  let heap_padding =
    ( if (4 + arity) mod 2 == 0 then
        4 + arity
      else
        4 + arity + 1 )
    * word_size
  in
  let gc = [] in
  (* reserve heap_padding tag in *)
  let stack_size = Int64.of_int (word_size * (2 + stack_padding)) in
  let prelude =
    [IJmp (Label after_label); ILabel fun_label; IPush (Reg RBP); IMov (Reg RBP, Reg RSP)]
  in
  let load_closure_setup =
    [ ILineComment "=== Load closure values ===";
      (* Convert the `arity` and the `num_free` to be SNALVALs *)
      IMov (Sized (QWORD_PTR, RegOffset (0, heap_reg)), Const (Int64.of_int (arity * 2)));
      ILea (Reg scratch_reg, RelLabel fun_label);
      IMov (Sized (QWORD_PTR, RegOffset (1, heap_reg)), Reg scratch_reg);
      IMov (Sized (QWORD_PTR, RegOffset (2, heap_reg)), Const (Int64.of_int (num_free * 2))) ]
  in
  (* TODO: what should the value be for SI? *)
  let compiled_body = compile_aexpr body si new_env (List.length args) false name in
  let stack_cleanup =
    [ILineComment "=== Stack clean-up ==="; IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet]
  in
  let bump_heap =
    [ ILineComment "===========================";
      IMov (Reg RAX, Reg heap_reg);
      IAdd (Reg RAX, Const closure_tag);
      IAdd (Reg heap_reg, Const (Int64.of_int heap_padding)) ]
  in
  ( prelude,
    [ ILineComment "=== Unpacking closure ===";
      (* Boost RSP to make room for closed vars *)
      ISub (Reg RSP, Const (Int64.of_int (num_free * word_size)));
      (* The scratch reg is going to hold the tuple pointer.
       * (i.e. the implicit first argument)
       * This means that we can't mangle it!
       *)
      IMov (Reg scratch_reg, RegOffset (2, RBP));
      ISub (Reg scratch_reg, Const 5L) ]
    @ unpack_closure_instrs
    @ [ ILineComment "=====================";
        ISub (Reg RSP, Const stack_size);
        IMov (RegOffset (0, RSP), Reg RDI);
        ILineComment "=== Function call ===" ]
    @ compiled_body
    @ stack_cleanup
    @ [ILabel after_label]
    @ check_memory (Int64.of_int heap_padding)
    (* @ gc *)
    @ load_closure_setup
    @ load_closure,
    bump_heap )

and compile_aexpr
    (e : tag aexpr)
    (si : int)
    (env_env : arg name_envt name_envt)
    (num_args : int)
    (is_tail : bool)
    (env_name : string) : instruction list =
  match e with
  | ALet (id, (CLambda (args, fun_body, tag) as lambda), let_body, _) ->
      let cur_env =
        safe_find_opt env_name env_env
          ~callee_tag:(sprintf "COMPILE_AEXPR! ALet1. env_name: %s" env_name)
      in
      let prelude =
        (* Since we're stepping into the body of a lambda, we set the env_name to the current id. *)
        let free = StringSet.elements @@ free_vars (ACExpr lambda) in
        let free_locations = List.map (fun v -> safe_find_opt v cur_env) free in
        let a, b, c = compile_fun id args fun_body env_env tag si free_locations in
        a @ b @ c
      in
      let body = compile_aexpr let_body si env_env num_args is_tail env_name in
      let offset =
        safe_find_opt id cur_env
          ~callee_tag:
            (sprintf "COMPILE_AEXPR! Alet1. id: %s, env: %s" id (string_of_name_envt cur_env))
      in
      prelude @ [IMov (offset, Reg RAX)] @ body
  | ALet (id, bound, body, _) ->
      let cur_env =
        safe_find_opt env_name env_env
          ~callee_tag:(sprintf "COMPILE_AEXPR! Alet2. env_name: %s" env_name)
      in
      let prelude = compile_cexpr bound si env_env num_args false env_name in
      let body = compile_aexpr body si env_env num_args is_tail env_name in
      let offset =
        safe_find_opt id cur_env
          ~callee_tag:
            (sprintf "COMPILE_AEXPR! Alet2. id: %s, env: %s" id (string_of_name_envt cur_env))
      in
      prelude @ [IMov (offset, Reg RAX)] @ body
  | ALetRec (bindings, let_body, _) ->
      let new_env, compiled_bindings =
        List.fold_left
          (fun (acc_env, acc_instrs) (binder, bound) ->
            (* We know that new functions are always at the top of the heap, right before we compile. *)
            let rec_env = update_envt_envt env_name binder (Reg heap_reg) acc_env in
            let offset = get_nested env_name binder env_env in
            let compiled_bound =
              match bound with
              (* Since we're stepping into the body of a lambda, we set the env_name to the current id. *)
              | CLambda (args, fun_body, tag) as lambda ->
                (* TODO: Fix this! *)
                let free = StringSet.elements @@ free_vars (ACExpr lambda) in
                let free_locations = List.map (fun v -> safe_find_opt v (safe_find_opt binder rec_env)) free in
                  let a, b, c = compile_fun binder args fun_body env_env tag si free_locations in
                  a @ b @ c
              | _ -> compile_cexpr bound si rec_env num_args is_tail env_name
            in
            (* TODO: Before or after? *)
            (* TODO: rec_env or env_env? *)
            (rec_env, acc_instrs @ compiled_bound @ [IMov (offset, Reg RAX)]) )
          (env_env, [ (* compiled code *) ])
          bindings
      in
      let compiled_body = compile_aexpr let_body si new_env num_args is_tail env_name in
      compiled_bindings @ compiled_body
  | ASeq (first, next, _) ->
      let compiled_first = compile_cexpr first si env_env num_args is_tail env_name in
      let compiled_next = compile_aexpr next si env_env num_args is_tail env_name in
      compiled_first @ compiled_next
  | ACExpr cexp -> compile_cexpr cexp si env_env num_args is_tail env_name

and compile_cexpr (e : tag cexpr) si (env_env : arg name_envt name_envt) num_args is_tail env_name =
  match e with
  | CImmExpr immexp ->
      [IMov (Reg scratch_reg, compile_imm immexp env_env env_name); IMov (Reg RAX, Reg scratch_reg)]
  | CIf (cond, thn, els, t) ->
      let else_label = sprintf "if_else#%d" t in
      let done_label = sprintf "if_done#%d" t in
      (let cond_reg = compile_imm cond env_env env_name in
       [ILineComment (sprintf "BEGIN conditional#%d   -------------" t); IMov (Reg RAX, cond_reg)]
       @ check_bool not_a_bool_if_label
       @ [ IMov (Reg scratch_reg, bool_mask);
           ITest (Reg RAX, Reg scratch_reg);
           IJz (Label else_label);
           ILineComment "  Then case:" ]
       @ compile_aexpr thn si env_env num_args is_tail env_name
       @ [IJmp (Label done_label); ILineComment "  Else case:"; ILabel else_label]
       @ compile_aexpr els si env_env num_args is_tail env_name )
      @ [ILabel done_label; ILineComment (sprintf "END conditional#%d     -------------" t)]
  | CPrim1 (op, e, t) -> (
      let e_reg = compile_imm e env_env env_name in
      match op with
      | Add1 ->
          (IMov (Reg RAX, e_reg) :: check_num not_a_number_arith_label)
          @ [IAdd (Reg RAX, Const 2L); check_overflow]
      | Sub1 ->
          (IMov (Reg RAX, e_reg) :: check_num not_a_number_arith_label)
          @ [IAdd (Reg RAX, Const (-2L)); check_overflow]
      (* `xor` can't take a 64-bit literal, *)
      | Not ->
          (IMov (Reg RAX, e_reg) :: check_bool not_a_bool_logic_label)
          @ [IMov (Reg scratch_reg, bool_mask); IXor (Reg RAX, Reg scratch_reg)]
      | IsBool ->
          let false_label = sprintf "is_bool_false#%d" t in
          let done_label = sprintf "is_bool_done#%d" t in
          [ILineComment (sprintf "BEGIN is_bool%d -------------" t); IMov (Reg RAX, e_reg)]
          @ check_bool false_label
          @ [ IMov (Reg RAX, const_true);
              IJmp (Label done_label);
              ILabel false_label;
              IMov (Reg RAX, const_false);
              ILabel done_label;
              ILineComment (sprintf "END is_bool%d   -------------" t) ]
      | IsNum ->
          let false_label = sprintf "is_num_false#%d" t in
          let done_label = sprintf "is_num_done#%d" t in
          [ILineComment (sprintf "BEGIN is_num%d -------------" t); IMov (Reg RAX, e_reg)]
          @ check_num false_label
          @ [ IMov (Reg RAX, const_true);
              IJmp (Label done_label);
              ILabel false_label;
              IMov (Reg RAX, const_false);
              ILabel done_label;
              ILineComment (sprintf "END is_num%d   -------------" t) ]
      | Print ->
          [ (* Print both passes its value to the external function, and returns it. *)
            IMov (Reg RDI, e_reg);
            (* TODO: Is this right?? *)
            ICall (Label "print") (* The answer goes in RAX :) *) ]
      | IsTuple ->
          let false_label = sprintf "is_tuple_false#%d" t in
          let done_label = sprintf "is_tuple_done#%d" t in
          [ILineComment (sprintf "BEGIN is_tuple%d -------------" t); IMov (Reg RAX, e_reg)]
          @ check_tuple false_label
          @ check_not_nil false_label
          @ [ IMov (Reg RAX, const_true);
              IJmp (Label done_label);
              ILabel false_label;
              IMov (Reg RAX, const_false);
              ILabel done_label;
              ILineComment (sprintf "END is_tuple%d   -------------" t) ]
      | PrintStack -> raise (NotYetImplemented "Fill in PrintStack here")
      | Crash -> [IJmp (Label crash_label)] )
  | CPrim2 (op, e1, e2, t) -> (
      let e1_reg = compile_imm e1 env_env env_name in
      let e2_reg = compile_imm e2 env_env env_name in
      match op with
      | Plus | Minus | Times -> arithmetic_prim2 op e1_reg e2_reg
      | Greater | GreaterEq | Less | LessEq -> compare_prim2 op e1_reg e2_reg t
      | And -> and_prim2 e1_reg e2_reg t
      | Or -> or_prim2 e1_reg e2_reg t
      | Eq ->
          let true_label = sprintf "equal#%d" t in
          let done_label = sprintf "equal_done#%d" t in
          (* No typechecking for Eq. We can just see if the two values are equivalent. *)
          [ IMov (Reg RAX, e1_reg);
            IMov (Reg scratch_reg, e2_reg);
            ICmp (Reg RAX, Reg scratch_reg);
            IJe (Label true_label);
            IMov (Reg RAX, const_false);
            IJmp (Label done_label);
            ILabel true_label;
            IMov (Reg RAX, const_true);
            ILabel done_label ]
      | CheckSize ->
          (* Check that the tuple `e1` has size `e2`.
           * We don't have to type-check these since:
           * - By the time we evaluate a CheckSize, we have already guaranteed that e1 is a tuple
           * - We create CheckSize during desugaring, and we only ever make `e2` an ENumber.
           *)
          [ IMov (Reg RAX, e1_reg);
            IMov (Reg scratch_reg, RegOffset (0, RAX));
            IMov (Reg RAX, e2_reg);
            ISar (Reg RAX, Const 1L);
            ICmp (Reg scratch_reg, Reg RAX);
            IMul (Reg RAX, Const 2L);
            (* Note that RAX stores the expected arity. *)
            IJne (Label err_unpack_err_label) ] )
  (* | CLambda _ -> compile_lambda e si env_env num_args is_tail env_name *)
  | CLambda _ -> raise (InternalCompilerError "Encountered an un-bound CLambda!")
  | CApp (callee, args, Snake, _) ->
      (* let closure_name = (match callee with ImmId (id, _) -> id | _ -> raise (InternalCompilerError "Tried to call a literal")) in *)
      let compiled_closure = compile_cexpr (CImmExpr callee) si env_env num_args is_tail env_name in
      let compiled_args = List.map (fun arg -> compile_imm arg env_env env_name) args in
      (ILineComment "~~~~~~~~~~" :: compiled_closure) @ call (Reg RAX) compiled_args
  (* | CApp (_, _, Snake, _) -> compile_call e si env_env num_args is_tail env_name *)
  | CApp _ -> raise (NotYetImplemented "CApp for native")
  | CTuple (items, tag) ->
      let n = List.length items in
      (* expected: (1, 2, 3, 5)
       * but got: forwarding to 0x4
       * Pain.
       * To avoid this, we make tuples and closures hold snakevals for their metadata.
       *)
      let n_snake = Int64.of_int (2 * n) in
      let heap_size = Int64.of_int (word_size * (n + 1)) in
      (* This is a gross way to do this and I'm sorry. *)
      let heap_bump_amt, heap_bump_amt_int =
        if n mod 2 == 0 then
          (Int64.of_int word_size, word_size)
        else
          (0L, 0)
      in
      let gc = reserve heap_bump_amt_int tag in
      (* let gc = [] in *)
      let loading_instrs =
        List.concat
        @@ List.mapi
             (fun i item ->
               move_with_scratch (RegOffset (i + 1, R15)) (compile_imm item env_env env_name) )
             items
      in
      ILineComment "=== Begin tuple initialization ==="
      :: move_with_scratch (RegOffset (0, R15)) (HexConst n_snake)
      @ loading_instrs
      @ gc
      @ check_memory heap_size
      @ [ IMov (Reg RAX, Reg R15);
          IAdd (Reg RAX, Const 1L);
          IAdd (Reg R15, Const heap_size);
          IInstrComment (IAdd (Reg R15, Const heap_bump_amt), "8 if even items, 0 if odd") ]
      @ [ILineComment "==== End tuple initialization ===="]
  | CGetItem (tup, idx, _) ->
      let tup_reg = compile_imm tup env_env env_name in
      let idx_reg = compile_imm idx env_env env_name in
      [ILineComment "==== Begin get-item ===="; IMov (Reg RAX, tup_reg)]
      @ check_tuple not_a_tuple_access_label
      @ [IMov (Reg RAX, tup_reg)]
      @ check_not_nil nil_deref_label
      @ [IMov (Reg RAX, idx_reg)]
      @ check_num not_a_number_index_label
      @ [ IMov (Reg RAX, tup_reg);
          ISub (Reg RAX, Const tuple_tag);
          IMov (Reg R11, idx_reg);
          ICmp (Reg R11, Reg RAX);
          IJge (Label index_high_label);
          IShr (Reg R11, Const 1L);
          ICmp (Reg R11, Const 0L);
          IJl (Label index_low_label);
          IMov (Reg RAX, Sized (QWORD_PTR, RegOffsetReg (RAX, R11, word_size, word_size)));
          (* IInstrComment
             (IAdd (Reg R11, Const 1L), "R11 already has n, now add 1 to account for the length"); *)
          ILineComment "Multiply the value in R11 by 8 with no further offset" ]
      @ move_with_scratch (Reg RAX) (RegOffsetReg (RAX, R11, word_size, word_size))
      @ [ILineComment "===== End get-item ====="]
  | CSetItem (tup, idx, value, _) ->
      let tup_reg = compile_imm tup env_env env_name in
      let idx_reg = compile_imm idx env_env env_name in
      let val_reg = compile_imm value env_env env_name in
      let tuple_slot_offset = RegOffsetReg (RAX, R11, word_size, word_size) in
      [ILineComment "==== Begin set-item ===="; IMov (Reg RAX, tup_reg)]
      @ check_tuple not_a_tuple_access_label
      @ [IMov (Reg RAX, tup_reg)]
      @ check_not_nil nil_deref_label
      @ [IMov (Reg RAX, idx_reg)]
      @ check_num not_a_number_index_label
      @ [ IMov (Reg RAX, tup_reg);
          ISub (Reg RAX, Const tuple_tag);
          IMov (Reg R11, idx_reg);
          ICmp (Reg R11, Reg RAX);
          IJge (Label index_high_label);
          IShr (Reg R11, Const 1L);
          ICmp (Reg R11, Const 0L);
          IJl (Label index_low_label);
          (* IInstrComment
             (IAdd (Reg R11, Const 1L), "R11 already has n, now add 1 to account for the length"); *)
          IMov (Reg scratch_reg2, val_reg);
          IInstrComment
            ( IMov (tuple_slot_offset, Reg scratch_reg2),
              "Store the location of the relevant value in RAX" );
          IMov (Reg RAX, Reg scratch_reg2);
          ILineComment "===== End set-item =====" ]

and compile_imm e (env_env : arg name_envt name_envt) env_name =
  match e with
  | ImmNum (n, _) -> Const (Int64.shift_left n 1)
  | ImmBool (true, _) -> const_true
  | ImmBool (false, _) -> const_false
  | ImmId (x, _) -> get_nested env_name x env_env
  | ImmNil _ -> Const tuple_tag

and args_help args regs =
  match (args, regs) with
  | arg :: args, reg :: regs -> IMov (Sized (QWORD_PTR, Reg reg), arg) :: args_help args regs
  | args, [] -> List.rev_map (fun arg -> IPush arg) args
  | [], _ -> []

and native_call label args =
  (* We know that on entry to every function, RSP is 16-byte aligned.
     We know that every frame is a multiple of 16 bytes.
     The call instruction pushes one return pointer onto the stack.
     The first thing we do is push RBP onto the stack
     So, we add 8 bytes of padding IFF the number of spilled args is *ODD*.
  *)
  let num_stack_args = max (List.length args - 6) 0 in
  let padding_needed = num_stack_args mod 2 <> 0 in
  let setup =
    ( if padding_needed then
        [IInstrComment (IPush (Sized (QWORD_PTR, Const 0L)), "Padding to 16-byte alignment")]
      else
        [] )
    @ args_help args first_six_args_registers
  in
  let teardown =
    ( if num_stack_args = 0 then
        []
      else
        [ IInstrComment
            ( IAdd (Reg RSP, Const (Int64.of_int (word_size * num_stack_args))),
              sprintf "Popping %d arguments" num_stack_args ) ] )
    @
    if padding_needed then
      [IInstrComment (IAdd (Reg RSP, Const (Int64.of_int word_size)), "Unpadding one word")]
    else
      []
  in
  setup @ [ICall label] @ teardown

(* UPDATE THIS TO HANDLE FIRST-CLASS FUNCTIONS AS NEEDED -- THIS CODE WILL NOT WORK AS WRITTEN *)
and call (closure : arg) args =
  let closure_to_rax = [IMov (Reg RAX, closure)] in
  (* Step 1: Ensure that `closure` is actually a closure. *)
  let closure_check = check_tag (Reg RAX) closure_tag not_a_closure_label in
  (* Step 2: Check the arity. *)
  let call_arity = List.length args in
  let arity_check =
    (* Arity_check will result in an untagged heap ptr in R11. *)
    [ IMov (Reg scratch_reg, Reg RAX);
      untag_snakeval (Reg scratch_reg);
      (* Note that we multiply the caller arity by two, since closures store a snakeval. *)
      ICmp (Sized (QWORD_PTR, RegOffset (0, scratch_reg)), Const (Int64.of_int (2 * call_arity)));
      (* ] @ crash @ [ *)
      IJne (Label err_arity_mismatch_label) ]
  in
  let push_args =
    List.rev_map
      (fun arg ->
        match arg with
        | Sized _ -> IPush arg
        | _ -> IPush (Sized (QWORD_PTR, arg)) )
      args
  in
  let push_closure = [IPush (Sized (QWORD_PTR, closure))] in
  let make_the_call = [untag_snakeval (Reg RAX); ICall (RegOffset (1, RAX))] in
  let teardown =
    if call_arity = 0 then
      []
    else
      [ IInstrComment
          ( IAdd (Reg RSP, Const (Int64.of_int (word_size * (call_arity + 1)))),
            sprintf "Popping %d arguments" call_arity ) ]
  in
  [ILineComment "=== Begin func call ==="]
  @ closure_to_rax (* Move closure into RAX*) @ closure_check (* Don't change RAX *)
  @ arity_check (* Untags RAX *) @ push_args (* *)
  @ push_closure (* Push thre original, TAGGED, closure val. *)
  @ make_the_call (* Calls the code ptr at [RAX+8] *)
  @ teardown (* Moves the stack top down by # args + 1, to account for the closure push *)
;;

(* This function can be used to take the native functions and produce DFuns whose bodies
   simply contain an EApp (with a Native call_type) to that native function.  Then,
   your existing compilation can turn these DFuns into ELambdas, which can then be called
   as in the rest of Fer-De-Lance, but the Native EApps will do the work of actually
   native_calling the runtime-provided functions. *)
let add_native_lambdas (p : sourcespan program) =
  let wrap_native name arity =
    let argnames = List.init arity (fun i -> sprintf "%s_arg_%d" name i) in
    [ DFun
        ( name,
          List.map (fun name -> BName (name, false, dummy_span)) argnames,
          EApp
            ( EId (name, dummy_span),
              List.map (fun name -> EId (name, dummy_span)) argnames,
              Native,
              dummy_span ),
          dummy_span ) ]
  in
  match p with
  | Program (declss, body, tag) ->
      Program
        ( List.fold_left
            (fun declss (name, (_, arity)) -> wrap_native name arity :: declss)
            declss
            (StringMap.bindings native_fun_bindings),
          body,
          tag )
;;

let error_suffix =
  List.fold_left
    (fun asm (label, instrs) -> asm ^ sprintf "%s:%s\n" label instrs)
    "\n"
    [ ( not_a_number_comp_label,
        to_asm (native_call (Label "?error") [Const err_COMP_NOT_NUM; Reg scratch_reg]) );
      ( not_a_number_arith_label,
        to_asm (native_call (Label "?error") [Const err_ARITH_NOT_NUM; Reg scratch_reg]) );
      ( not_a_bool_logic_label,
        to_asm (native_call (Label "?error") [Const err_LOGIC_NOT_BOOL; Reg scratch_reg]) );
      ( not_a_bool_if_label,
        to_asm (native_call (Label "?error") [Const err_IF_NOT_BOOL; Reg scratch_reg]) );
      (overflow_label, to_asm (native_call (Label "?error") [Const err_OVERFLOW; Reg RAX]));
      ( not_a_tuple_access_label,
        to_asm (native_call (Label "?error") [Const err_GET_NOT_TUPLE; Reg scratch_reg]) );
      ( not_a_number_index_label,
        to_asm (native_call (Label "?error") [Const err_INDEX_NOT_NUM; Reg scratch_reg]) );
      ( index_low_label,
        to_asm (native_call (Label "?error") [Const err_GET_LOW_INDEX; Reg scratch_reg]) );
      (index_high_label, to_asm (native_call (Label "?error") [Const err_GET_HIGH_INDEX]));
      (nil_deref_label, to_asm (native_call (Label "?error") [Const err_NIL_DEREF; Reg scratch_reg]));
      ( err_out_of_memory_label,
        to_asm (native_call (Label "?error") [Const err_OUT_OF_MEMORY; Reg scratch_reg]) );
      ( not_a_closure_label,
        to_asm (native_call (Label "?error") [Const err_CALL_NOT_CLOSURE; Reg scratch_reg]) );
      ( err_arity_mismatch_label,
        to_asm (native_call (Label "?error") [Const err_CALL_ARITY_ERR; Reg scratch_reg]) );
      (crash_label, to_asm (native_call (Label "?error") [Const err_CRASH])) ]
;;

let compile_prog (anfed, (env : arg name_envt name_envt)) =
  let prelude =
    "section .text\n\
     extern ?error\n\
     extern ?input\n\
     extern ?print\n\
     extern ?print_stack\n\
     extern ?equal\n\
     extern ?try_gc\n\
     extern ?naive_print_heap\n\
     extern ?HEAP\n\
     extern ?HEAP_END\n\
     extern ?set_stack_bottom\n\
     global " ^ ocsh_name
  in
  let suffix = error_suffix in
  match anfed with
  | AProgram (body, tag) ->
      (* $heap and $size are mock parameter names, just so that compile_fun knows our_code_starts_here takes in 2 parameters *)
      let prologue, comp_main, epilogue =
        (* compile_lambda (CLambda (["$heap"; "$size"] body, 0), [0; 0], Snake, 0) 0 env 2 false ocsh_name *)
        compile_fun ocsh_name ["$heap"; "$size"] body env tag 0 []
      in
      let heap_start =
        [ ILineComment "heap start";
          IInstrComment
            ( IMov (Sized (QWORD_PTR, Reg heap_reg), Reg (List.nth first_six_args_registers 0)),
              "Load heap_reg with our argument, the heap pointer" );
          IInstrComment
            ( IAdd (Sized (QWORD_PTR, Reg heap_reg), Const 15L),
              "Align it to the nearest multiple of 16" );
          IMov (Reg scratch_reg, HexConst 0xFFFFFFFFFFFFFFF0L);
          IInstrComment
            ( IAnd (Sized (QWORD_PTR, Reg heap_reg), Reg scratch_reg),
              "by adding no more than 15 to it" ) ]
      in
      let set_stack_bottom =
        [IMov (Reg R12, Reg RDI)]
        @ native_call (Label "?set_stack_bottom") [Reg RBP]
        @ [IMov (Reg RDI, Reg R12)]
      in
      let main = prologue @ set_stack_bottom @ heap_start @ comp_main @ epilogue in
      sprintf "%s%s%s\n" prelude (to_asm main) suffix
;;

let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

let compile_to_string ?(no_builtins = false) (prog : sourcespan program pipeline) : string pipeline
    =
  prog
  |> add_err_phase well_formed is_well_formed
  |> run_if (not no_builtins) (add_phase add_natives add_native_lambdas)
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase locate_bindings naive_stack_allocation
  |> add_phase result compile_prog
;;
