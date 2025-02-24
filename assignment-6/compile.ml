open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors

type 'a envt = (string * 'a) list

let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1 (_, e, _) -> is_imm e
  | EPrim2 (_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet (binds, body, _) -> List.for_all (fun (_, e, _) -> is_anf e) binds && is_anf body
  | EIf (cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | _ -> is_imm e

and is_imm e =
  match e with
  | ENumber _ -> true
  | EBool _ -> true
  | EId _ -> true
  | _ -> false
;;

let const_true = HexConst 0xFFFFFFFFFFFFFFFFL

let const_false = HexConst 0x7FFFFFFFFFFFFFFFL

let bool_mask = HexConst 0x8000000000000000L

let bool_tag = 0x0000000000000007L

let bool_tag_mask = 0x0000000000000007L

let num_tag = 0x0000000000000000L

let num_tag_mask = 0x0000000000000001L

let err_COMP_NOT_NUM = 1L

let err_ARITH_NOT_NUM = 2L

let err_LOGIC_NOT_BOOL = 3L

let err_IF_NOT_BOOL = 4L

let err_OVERFLOW = 5L

let err_GET_NOT_TUPLE = 6L

let err_GET_LOW_INDEX = 7L

let err_GET_HIGH_INDEX = 8L

let err_NIL_DEREF = 9L

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

let heap_reg = R15

let scratch_reg = R11

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

let rec find_opt ls x =
  match ls with
  | [] -> None
  | (y, v) :: rest ->
      if y = x then
        Some v
      else
        find_opt rest x
;;

let count_vars e =
  let rec helpA e =
    match e with
    | ALet (_, bind, body, _) -> 1 + max (helpC bind) (helpA body)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in
  helpA e
;;

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

type funenvt = call_type envt

let initial_fun_env : funenvt =
  [ (* call_types indicate whether a given function is implemented by something in the runtime,
       as a snake function, as a primop (in case that's useful), or just unknown so far *) ]
;;

let rename_and_tag (p : tag program) : tag program =
  let rec rename (env : string envt) p =
    match p with
    | Program (decls, body, tag) ->
        let rec addToEnv funenv decl =
          match decl with
          | DFun (name, _, _, _) -> (name, Snake) :: funenv
        in
        let initial_funenv = List.map (fun (name, ct) -> (name, ct)) initial_fun_env in
        let funenv = List.fold_left addToEnv initial_funenv decls in
        Program (List.map (helpD funenv env) decls, helpE funenv env body, tag)
  and helpD funenv env decl =
    match decl with
    | DFun (name, args, body, tag) ->
        let newArgs, env' = helpBS env args in
        DFun (name, newArgs, helpE funenv env' body, tag)
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
  and helpBG funenv env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a) :: bindings ->
        let b', env' = helpB env b in
        let e' = helpE funenv env e in
        let bindings', env'' = helpBG funenv env' bindings in
        ((b', e', a) :: bindings', env'')
  and helpE funenv env e =
    match e with
    | ESeq (e1, e2, tag) -> ESeq (helpE funenv env e1, helpE funenv env e2, tag)
    | ETuple (es, tag) -> ETuple (List.map (helpE funenv env) es, tag)
    | EGetItem (e, idx, tag) -> EGetItem (helpE funenv env e, helpE funenv env idx, tag)
    | ESetItem (e, idx, newval, tag) ->
        ESetItem (helpE funenv env e, helpE funenv env idx, helpE funenv env newval, tag)
    | EPrim1 (op, arg, tag) -> EPrim1 (op, helpE funenv env arg, tag)
    | EPrim2 (op, left, right, tag) ->
        EPrim2 (op, helpE funenv env left, helpE funenv env right, tag)
    | EIf (c, t, f, tag) -> EIf (helpE funenv env c, helpE funenv env t, helpE funenv env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId (name, tag) -> ( try EId (find env name, tag) with Not_found -> e )
    | EApp (name, args, native, tag) ->
        let call_type =
          match find_opt funenv name with
          | None -> native
          | Some ct -> ct
        in
        EApp (name, List.map (helpE funenv env) args, call_type, tag)
    | ELet (binds, body, tag) ->
        let binds', env' = helpBG funenv env binds in
        let body' = helpE funenv env' body in
        ELet (binds', body', tag)
  in
  rename [] p
;;

(* Returns the stack-index (in words) of the deepest stack index used for any
   of the variables in this expression *)
let deepest_stack e env =
  let rec helpA e =
    match e with
    | ALet (name, bind, body, _) ->
        List.fold_left max 0 [name_to_offset name; helpC bind; helpA body]
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (c, t, f, _) -> List.fold_left max 0 [helpI c; helpA t; helpA f]
    | CPrim1 (_, i, _) -> helpI i
    | CPrim2 (_, i1, i2, _) -> max (helpI i1) (helpI i2)
    | CApp (_, args, _, _) -> List.fold_left max 0 (List.map helpI args)
    | CTuple (elms, _) -> List.fold_left max 0 (List.map helpI elms)
    | CGetItem (tup, idx, _) -> max (helpI tup) (helpI idx)
    | CSetItem (tup, idx, newval, _) -> List.fold_left max 0 [helpI tup; helpI idx; helpI newval]
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmNil _ -> 0
    | ImmId (name, _) -> name_to_offset name
  and name_to_offset name =
    match find env name with
    | RegOffset (words, RBP) -> words / -1 (* negative because stack direction *)
    | _ -> 0
  in
  max (helpA e) 0 (* if only parameters are used, helpA might return a negative value *)
;;

(* IMPLEMENT EVERYTHING BELOW *)

(* Convert a Let with multiple bindings into multiple Lets with one binding. *)
(* INVARIANT: All `ELet`s have a single binding. *)
let simplify_multi_bindings (Program ((decls : 'a decl list), (body : 'a expr), (a : 'a))) :
    'a program =
  let rec helpE e =
    match e with
    (* Avoid making a new Let if there are no bindings *)
    | ELet (_ :: [], _, _) -> e
    | ELet (binding :: rest_bindings, body, a) ->
        ELet ([binding], helpE (ELet (rest_bindings, body, a)), a)
    | _ -> e
  in
  let helpD d =
    match d with
    | DFun (fname, args, body, a) -> DFun (fname, args, helpE body, a)
  in
  Program (List.map helpD decls, helpE body, a)
;;

(* Let's make this global. *)
let make_gensym _ =
  let next = ref 0 in
  fun name ->
    next := !next + 1;
    sprintf "%s#%d" name !next
;;

(* Convert Tuple bindings in `Let`s into multiple regular bindings. *)
(* This pass has to happen before other passes, because we introduce new bindings. *)
(* INVARIANT: No `ELet` contains a `BTuple` *)
let simplify_tuple_bindings (Program ((decls : 'a decl list), (body : 'a expr), (a : 'a))) :
    'a program =
  let gensym = make_gensym () in
  let rec help_bind ((bind, bound, _) as binding) : 'a binding list =
    match bind with
    | BTuple (sub_binds, alpha) ->
        let temp_name = gensym "temp_tuple_name" in
        let temp_id = EId (temp_name, alpha) in
        (* Check for shadow (later) *)
        (BName (temp_name, false, alpha), bound, alpha)
        :: List.concat
             (List.mapi
                (fun i sub_bind ->
                  let indexer = ENumber (Int64.of_int i, alpha) in
                  match sub_bind with
                  | BName _ | BBlank _ -> [(sub_bind, EGetItem (temp_id, indexer, alpha), alpha)]
                  | BTuple _ -> help_bind (sub_bind, EGetItem (temp_id, indexer, alpha), alpha) )
                sub_binds )
    | _ -> [binding]
  in
  let rec helpE e =
    match e with
    (* Avoid making a new Let if there are no bindings *)
    | ELet ([], _, _) -> e
    | ELet (bindings, body, a) ->
        ELet
          ( List.concat_map (fun ((bind, bound, _) as binding) -> help_bind binding) bindings,
            helpE body,
            a )
    | _ -> e
  in
  let helpD d =
    match d with
    | DFun (fname, args, body, a) -> DFun (fname, args, helpE body, a)
  in
  Program (List.map helpD decls, helpE body, a)
;;

(* Convert all Blank bindings into mangled ids. *)
(* ASSUME: No BTuple bindings *)
(* INVARIANT: All bindings are solely BNames. *)
let eliminate_blank_bindings (Program ((decls : 'a decl list), (body : 'a expr), (a : 'a))) :
    'a program =
  let gensym = make_gensym () in
  let rec helpE e =
    match e with
    (* Avoid making a new Let if there are no bindings *)
    | ELet ([], _, _) -> e
    | ELet (bindings, body, a) ->
        ELet
          ( List.map
              (fun ((bind, bound, alpha) as binding) ->
                match bind with
                (* Look here for shadow-able *)
                | BBlank _ -> (BName (gensym "blank", false, alpha), bound, alpha)
                | BName _ -> binding
                | BTuple _ -> raise (InternalCompilerError "Expected no BTuples at this point") )
              bindings,
            helpE body,
            a )
    | _ -> e
  in
  let helpD d =
    match d with
    | DFun (fname, args, body, a) -> DFun (fname, args, helpE body, a)
  in
  Program (List.map helpD decls, helpE body, a)
;;

let desugar (p : 'a program) : 'a program =
  p |> simplify_tuple_bindings |> eliminate_blank_bindings |> simplify_multi_bindings
;;

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program (decls, body, _) -> AProgram (List.map helpD decls, helpA body, ())
  and helpD (d : tag decl) : unit adecl =
    match d with
    | DFun (name, args, body, _) ->
        let args =
          List.map
            (fun a ->
              match a with
              | BName (a, _, _) -> a
              | _ -> raise (NotYetImplemented "Finish this") )
            args
        in
        ADFun (name, args, helpA body, ())
  and helpC (e : tag expr) : unit cexpr * (string * unit cexpr) list =
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
    | ELet (_ :: _, body, _) -> raise (NotYetImplemented "Finish this")
    (* | ELet(((bind, _, _), exp, _)::rest, body, pos) ->
     *    let (exp_ans, exp_setup) = helpC exp in
     *    let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
     *    (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup) *)
    | EApp (funname, args, ct, _) ->
        let new_args, new_setup = List.split (List.map helpI args) in
        (CApp (funname, new_args, ct, ()), List.concat new_setup)
    (* NOTE: You may need more cases here, for sequences and tuples *)
    | _ ->
        let imm, setup = helpI e in
        (CImmExpr imm, setup)
  and helpI (e : tag expr) : unit immexpr * (string * unit cexpr) list =
    match e with
    | ENumber (n, _) -> (ImmNum (n, ()), [])
    | EBool (b, _) -> (ImmBool (b, ()), [])
    | EId (name, _) -> (ImmId (name, ()), [])
    | EPrim1 (op, arg, tag) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (ImmId (tmp, ()), arg_setup @ [(tmp, CPrim1 (op, arg_imm, ()))])
    | EPrim2 (op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (ImmId (tmp, ()), left_setup @ right_setup @ [(tmp, CPrim2 (op, left_imm, right_imm, ()))])
    | EIf (cond, _then, _else, tag) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        (ImmId (tmp, ()), cond_setup @ [(tmp, CIf (cond_imm, helpA _then, helpA _else, ()))])
    | EApp (funname, args, ct, tag) ->
        let tmp = sprintf "app_%d" tag in
        let new_args, new_setup = List.split (List.map helpI args) in
        (ImmId (tmp, ()), List.concat new_setup @ [(tmp, CApp (funname, new_args, ct, ()))])
    | ELet ([], body, _) -> helpI body
    | ELet (_ :: _, body, _) -> raise (NotYetImplemented "Finish this")
    (* | ELet(((bind, _, _), exp, _)::rest, body, pos) ->
     *    let (exp_ans, exp_setup) = helpC exp in
     *    let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
     *    (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup) *)
    | _ -> raise (NotYetImplemented "Finish the remaining cases")
  and helpA e : unit aexpr =
    let ans, ans_setup = helpC e in
    List.fold_right (fun (bind, exp) body -> ALet (bind, exp, body, ())) ans_setup (ACExpr ans)
  in
  helpP p
;;

let is_well_formed (p : sourcespan program) : sourcespan program fallible =
  let rec wf_E (e : sourcespan expr) (* other parameters may be needed here *) =
    Error [NotYetImplemented "Implement well-formedness checking for expressions"]
  and wf_D (d : sourcespan decl) (* other parameters may be needed here *) =
    Error [NotYetImplemented "Implement well-formedness checking for definitions"]
  and wf_G (g : sourcespan decl list) (* other parameters may be needed here *) =
    Error [NotYetImplemented "Implement well-formedness checking for definition groups"]
  in
  match p with
  | Program (decls, body, _) ->
      Error [NotYetImplemented "Implement well-formedness checking for programs"]
;;

(* let desugar (p : sourcespan program) : sourcespan program =
     let gensym =
       let next = ref 0 in
       fun name ->
         next := !next + 1;
         sprintf "%s_%d" name !next
     in
     let rec helpE (e : sourcespan expr) (* other parameters may be needed here *) =
       Error [NotYetImplemented "Implement desugaring for expressions"]
     and helpD (d : sourcespan decl) (* other parameters may be needed here *) =
       Error [NotYetImplemented "Implement desugaring for definitions"]
     and helpG (g : sourcespan decl list) (* other parameters may be needed here *) =
       Error [NotYetImplemented "Implement desugaring for definition groups"]
     in
     match p with
     | Program (decls, body, _) -> raise (NotYetImplemented "Implement desugaring for programs")
   ;; *)

let naive_stack_allocation (prog : tag aprogram) : tag aprogram * arg envt =
  raise (NotYetImplemented "Implement stack allocation for egg-eater")
;;

(* if you think that this signature is incomplete or incorrect,
   feel free to change it as appropriate and leave a comment explaining why. *)
let rec compile_fun (fun_name : string) (args : string list) (env : arg envt) : instruction list =
  raise (NotYetImplemented "Compile funs not yet implemented")

and compile_aexpr (e : tag aexpr) (env : arg envt) (num_args : int) (is_tail : bool) :
    instruction list =
  raise (NotYetImplemented "Compile aexpr not yet implemented")

and compile_cexpr (e : tag cexpr) (env : arg envt) (num_args : int) (is_tail : bool) =
  raise (NotYetImplemented "Compile cexpr not yet implemented")

and compile_imm e env =
  match e with
  | ImmNum (n, loc) ->
      (* Handle static overflow! *)
      if n > Int64.div Int64.max_int 2L || n < Int64.div Int64.min_int 2L then
        raise (Overflow (n, loc))
      else
        Const (Int64.shift_left n 1)
  | ImmBool (true, _) -> const_true
  | ImmBool (false, _) -> const_false
  | ImmId (x, _) -> find env x
  | ImmNil _ -> raise (NotYetImplemented "Finish this")
;;

let compile_decl (d : tag adecl) (env : arg envt) : instruction list =
  raise (NotYetImplemented "Compile decl not yet implemented")
;;

let compile_prog ((anfed : tag aprogram), (env : arg envt)) : string =
  match anfed with
  | AProgram (decls, body, _) ->
      let comp_decls = raise (NotYetImplemented "... do stuff with decls ...") in
      let body_prologue, comp_body, body_epilogue =
        raise (NotYetImplemented "... do stuff with body ...")
      in
      let heap_start =
        [ ILineComment "heap start";
          IInstrComment
            ( IMov (Reg heap_reg, Reg (List.nth first_six_args_registers 0)),
              "Load heap_reg with our argument, the heap pointer" );
          IInstrComment (IAdd (Reg heap_reg, Const 15L), "Align it to the nearest multiple of 16");
          IInstrComment
            (IAnd (Reg heap_reg, HexConst 0xFFFFFFFFFFFFFFF0L), "by adding no more than 15 to it")
        ]
      in
      let main = to_asm (body_prologue @ heap_start @ comp_body @ body_epilogue) in
      raise
        (NotYetImplemented
           "... combine comp_decls and main with any needed extra setup and error handling ..." )
;;

(* Feel free to add additional phases to your pipeline.
   The final pipeline phase needs to return a string,
   but everything else is up to you. *)

let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

(* Add a desugaring phase somewhere in here *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> add_err_phase well_formed is_well_formed
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase locate_bindings naive_stack_allocation
  |> add_phase result compile_prog
;;
