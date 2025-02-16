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

let not_a_number_comp_label = "error_not_number_comp"

let not_a_number_arith_label = "error_not_number_arith"

let not_a_bool_logic_label = "error_not_bool_logic"

let not_a_bool_if_label = "error_not_bool_if"

let overflow_label = "error_overflow"

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

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
    | CApp (_, args, _) -> List.fold_left max 0 (List.map helpI args)
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmId (name, _) -> name_to_offset name
  and name_to_offset name =
    match find env name with
    | RegOffset (bytes, RBP) -> bytes / (-1 * word_size) (* negative because stack direction *)
    | _ -> 0
  in
  max (helpA e) 0 (* if only parameters are used, helpA might return a negative value *)
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

let rec find_one (l : 'a list) (elt : 'a) (comp : 'a -> 'a -> bool) : bool =
  match l with
  | [] -> false
  | x :: xs -> elt = x || find_one xs elt comp
;;

let rec find_dup (l : 'a list) (comp : 'a -> 'a -> bool) : 'a option =
  match l with
  | [] | [_] -> None
  | x :: xs ->
      if find_one xs x comp then
        Some x
      else
        find_dup xs comp
;;

let rec find_all_dups (l : 'a list) (comp : 'a -> 'a -> bool) : 'a list =
  match l with
  | [] | [_] -> []
  | x :: xs ->
      if find_one xs x comp then
        x :: find_all_dups xs comp
      else
        find_all_dups xs comp
;;

(* Gets a mapping of function names to arity for all functions *)
let get_decl_env (decls : 'a decl list) : (string * int) list =
  List.map
    (fun d ->
      match d with
      | DFun (funname, args, _, _) -> (funname, List.length args) )
    decls
;;

(* IMPLEMENT EVERYTHING BELOW *)

let rec desugar (p : 'a program) : 'a program =
  let rec helpE e =
    match e with
    | ELet (binding :: rest_bindings, body, a) ->
        ELet ([binding], helpE (ELet (rest_bindings, body, a)), a)
    | _ -> e
  in
  let helpD d =
    match d with
    | DFun (fname, args, body, a) -> DFun (fname, args, helpE body, a)
  in
  match p with
  | Program (decls, body, a) -> Program (List.map helpD decls, helpE body, a)
;;

let rename (e : tag program) : tag program =
  let rec rename_bindings (env : (string * string) list) (bindings : tag bind list) :
      (string * string) list * tag bind list =
    List.fold_left
      (fun (new_env, renamed_bindings) (id, bound, t) ->
        let renamed_bound = help new_env bound in
        (* rename e consistently *)
        let renamed_id = sprintf "%s#%d" id t in
        (* create new unique name for x *)
        let renamed_binding = (renamed_id, renamed_bound, t) in
        ((id, renamed_id) :: new_env, renamed_bindings @ [renamed_binding]) )
      (env, []) bindings
  and help (env : (string * string) list) (e : tag expr) =
    match e with
    | EId (x, t) ->
        (* Lookup x in the environment and replace it with the environment's renamed version.
         * Since we only call `rename` *after* scope checking, x is guaranteed to be in env.
         *)
        EId (List.assoc x env, t)
    | ELet (bindings, body, tag) ->
        (* "Extend env by renaming each binding in binds, then rename the expressions and body" *)
        let new_env, renamed_bindings = rename_bindings env bindings in
        let renamed_body = help new_env body in
        ELet (renamed_bindings, renamed_body, tag)
    | EApp (fname, params, t) ->
        (* Should this be renamed, or should it be looked-up? *)
        let renamed_fname = List.assoc fname env in
        (* let renamed_fname = sprintf "%s#%d" fname t in *)
        (* Since this is an _application_, 
         * none of the parameters are within the scope of any other.
         * Ergo, we give them all the same environment to work with. 
         *)
        let renamed_params = List.map (fun p -> help env p) params in
        EApp (renamed_fname, renamed_params, t)
    (* Less interesting cases... *)
    | ENumber (_, _) -> e
    | EPrim1 (op, a, t) -> EPrim1 (op, help env a, t)
    | EPrim2 (op, a, b, t) -> EPrim2 (op, help env a, help env b, t)
    | EIf (c, t, f, ta) -> EIf (help env c, help env t, help env f, ta)
    | EBool _ -> e
  and helpD (env : (string * string) list) (d : tag decl) : tag decl =
    (* Step 1: rename the function by looking it up in the environment *)
    (* Step 2: rename each arg and add them to the env *)
    (* Step 3: rename the body with the arg env *)
    match d with
    | DFun (name, args, body, t) ->
        let renamed_name = List.assoc name env in
        let decl_env, renamed_args =
          List.fold_left
            (fun (acc_env, acc_args) (arg_name, arg_tag) ->
              let renamed_arg = (sprintf "%s#%d" arg_name arg_tag, arg_tag) in
              (acc_env @ [(arg_name, fst renamed_arg)], acc_args @ [renamed_arg]) )
            (env, []) args
        in
        let renamed_body = help decl_env body in
        DFun (renamed_name, renamed_args, renamed_body, t)
  and helpP p =
    (* Step 1: put all function names in the environmnet *)
    (* Step 2: rename each function with that environemt *)
    (* Step 3: Use the base environment (i.e. all fnames) to rename the prog body *)
    match p with
    | Program (decls, body, t) ->
        (* Get the base environment containing all function names. *)
        let decl_env =
          List.map
            (fun d ->
              match d with
              | DFun (name, _, _, t) -> (name, sprintf "%s#%d" name t) )
            decls
        in
        Program (List.map (helpD decl_env) decls, help decl_env body, t)
  in
  helpP e
;;

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program (decls, body, _) -> AProgram (List.map helpD decls, helpA body, ())
  and helpD (d : tag decl) : unit adecl =
    match d with
    | DFun (name, args, body, _) -> ADFun (name, List.map fst args, helpA body, ())
  and helpC (e : tag expr) : unit cexpr * (string * unit cexpr) list =
    match e with
    | EPrim1 (op, arg, _) ->
        let arg_imm, arg_setup = helpI arg in
        (CPrim1 (op, arg_imm, ()), arg_setup)
    | EPrim2 (And, left, right, _) ->
        let left_imm, left_setup = helpI left in
        (CIf (left_imm, helpA right, helpA left, ()), left_setup)
    | EPrim2 (Or, left, right, _) ->
        let left_imm, left_setup = helpI left in
        (CIf (left_imm, helpA left, helpA right, ()), left_setup)
    | EPrim2 (op, left, right, _) ->
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (CPrim2 (op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf (cond, _then, _else, _) ->
        let cond_imm, cond_setup = helpI cond in
        (CIf (cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ELet ([], body, _) -> helpC body
    | ELet ((bind, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    | EApp (funname, args, _) ->
        let args_imm, args_setups = List.split (List.map helpI args) in
        let args_setup = List.fold_left ( @ ) [] args_setups in
        (CApp (funname, args_imm, ()), args_setup)
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
    | EPrim2 (And, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let _, right_setup = helpI right in
        ( ImmId (tmp, ()),
          left_setup @ right_setup @ [(tmp, CIf (left_imm, helpA right, helpA left, ()))] )
    | EPrim2 (Or, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let _, right_setup = helpI right in
        ( ImmId (tmp, ()),
          left_setup @ right_setup @ [(tmp, CIf (left_imm, helpA left, helpA right, ()))] )
    | EPrim2 (op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (ImmId (tmp, ()), left_setup @ right_setup @ [(tmp, CPrim2 (op, left_imm, right_imm, ()))])
    | EIf (cond, _then, _else, tag) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        (ImmId (tmp, ()), cond_setup @ [(tmp, CIf (cond_imm, helpA _then, helpA _else, ()))])
    | EApp (funname, args, tag) ->
        let tmp = sprintf "app_%d" tag in
        let args_imm, args_setups = List.split (List.map helpI args) in
        let args_setup = List.fold_left ( @ ) [] args_setups in
        (ImmId (tmp, ()), args_setup @ [(tmp, CApp (funname, args_imm, ()))])
    | ELet ([], body, _) -> helpI body
    | ELet ((bind, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
  and helpA e : unit aexpr =
    let ans, ans_setup = helpC e in
    List.fold_right (fun (bind, exp) body -> ALet (bind, exp, body, ())) ans_setup (ACExpr ans)
  in
  helpP p
;;

let is_well_formed (p : sourcespan program) : sourcespan program fallible =
  let rec wf_E (e : sourcespan expr) (id_env : string list) (decl_env : (string * int) list) :
      exn list =
    match e with
    | EBool _ -> []
    | ENumber _ -> []
    | EId (x, loc) ->
        if find_one id_env x ( = ) then
          []
        else
          [UnboundId (x, loc)]
    | EPrim1 (_, e, _) -> wf_E e id_env decl_env
    | EPrim2 (_, l, r, _) -> wf_E l id_env decl_env @ wf_E r id_env decl_env
    | EIf (c, t, f, _) -> wf_E c id_env decl_env @ wf_E t id_env decl_env @ wf_E f id_env decl_env
    | ELet (binds, body, _) ->
        (* Pass 1: Check for duplicate bindings *)
        let _, dup_bind_exns =
          List.fold_left
            (fun (seen, exns) ((name, _, loc) as binding) ->
              match List.find_opt (fun (a, _, _) -> a = name) seen with
              | Some (_, _, orig_loc) -> (seen, DuplicateId (name, loc, orig_loc) :: exns)
              | None -> (binding :: seen, exns) )
            ([ (* name, body, loc *) ], [ (* exns *) ])
            binds
        in
        (* Pass 2: Check scope in each binding body *)
        let _, bind_body_exns =
          (* Each bound body is allowed to use the names of  all previous, bindings *)
          List.fold_left
            (fun (let_env, exns) (id, body, _) -> (id :: let_env, wf_E body let_env decl_env @ exns))
            (id_env, []) binds
        in
        (* Pass 3: Check scope in the let body *)
        let let_body_exns = wf_E body (List.map (fun (id, _, _) -> id) binds @ id_env) decl_env in
        dup_bind_exns @ bind_body_exns @ let_body_exns
    | EApp (funname, args, loc) ->
        let unbound_fun_error =
          if find_one (fst @@ List.split @@ decl_env) funname ( = ) then
            []
          else
            [UnboundFun (funname, loc)]
        in
        if unbound_fun_error = [] then
          (* We made sure that the function name is in the `decl_env` above, so `List.assoc` will not error *)
          let expected_arity = List.assoc funname decl_env in
          let given_arity = List.length args in
          if given_arity = expected_arity then
            []
          else
            [Arity (expected_arity, given_arity, loc)]
        else
          []
  and wf_D (ds : 'a decl list) (decl_env : (string * int) list) : exn list =
    (* Pass 1: *)
    (* Duplicate function name *)
    let _, dup_fname_exns =
      List.fold_left
        (fun (seen, exns) (DFun (fname, _, _, loc) as d) ->
          (* Look in the environment. If the function name exists, duplicate that. *)
          let dup = find_decl seen fname in
          match dup with
          | Some (DFun (_, _, _, loc_orig)) -> (seen, DuplicateFun (fname, loc, loc_orig) :: exns)
          | None -> (d :: seen, exns) )
        ([ (* seen decls list *) ], [ (* exns list *) ])
        ds
    in
    let dup_arg_exns =
      List.concat_map
        (fun (DFun (_, args, _, _)) ->
          (* This one has a fold _inside_ of the map, 
           * so we need to discard the irrelevant acc value earlier than the prior case. *)
          snd
            (List.fold_left
               (fun (seen, exns) ((arg_name, arg_loc) as arg) ->
                 match List.find_opt (fun a -> fst a = arg_name) seen with
                 | Some (_, orig_loc) -> (seen, DuplicateId (arg_name, arg_loc, orig_loc) :: exns)
                 | None -> (arg :: seen, exns) )
               ([ (* argname, loc *) ], [ (* exns *) ])
               args ) )
        ds
      (* Pass 2: *)
      (* Check well-formedness of all decl bodies, using the decl environment. *)
    in
    let decl_body_exns =
      List.concat_map (fun (DFun (_, args, body, _)) -> wf_E body (List.map fst args) decl_env) ds
    in
    dup_fname_exns @ dup_arg_exns @ decl_body_exns
  in
  match p with
  | Program (decls, body, _) -> (
      let decl_env = get_decl_env decls in
      let decls_result = wf_D decls decl_env in
      let body_result = wf_E body [] decl_env in
      let total_errors = decls_result @ body_result in
      match total_errors with
      | [] -> Ok p
      | _ -> Error total_errors )
;;

(* ASSUMES that the program has been alpha-renamed and all names are unique *)
let naive_stack_allocation (prog : tag aprogram) : tag aprogram * arg envt =
  raise
    (NotYetImplemented
       "Extract your stack-slot allocation logic from Cobra's compile_expr into here" )
;;

(* In Cobra, you had logic somewhere that tracked the stack index, starting at 1 and incrementing it
   within the bodies of let-bindings.  It built up an environment that mapped each let-bound name to
   a stack index, so that RegOffset(~-8 * stackIndex, RBP) stored the value of that let-binding.
   In this function, you should build up that environment, and return a pair of the already-ANF'ed
   program and that environment, which can then both be passed along to compile_prog to finish compilation.

   Since this environment-building step comes *after* renaming, you may rely on the invariant that every
   name in the program appears bound exactly once, and therefore those names can be used as keys in
   an environment without worry of shadowing errors.
*)

let rec compile_fun (fun_name : string) (args : string list) (env : arg envt) : instruction list =
  raise (NotYetImplemented "Compile funs not yet implemented")

and compile_aexpr (e : tag aexpr) (env : arg envt) (num_args : int) (is_tail : bool) :
    instruction list =
  raise (NotYetImplemented "Compile aexpr not yet implemented")

and compile_cexpr (e : tag cexpr) (env : arg envt) (num_args : int) (is_tail : bool) =
  raise (NotYetImplemented "Compile cexpr not yet implemented")

and compile_imm e (env : arg envt) =
  match e with
  | ImmNum (n, _) -> Const (Int64.shift_left n 1)
  | ImmBool (true, _) -> const_true
  | ImmBool (false, _) -> const_false
  | ImmId (x, _) -> find env x
;;

let compile_decl (d : tag adecl) (env : arg envt) : instruction list =
  raise (NotYetImplemented "Compile decl not yet implemented")
;;

let runtime_errors = 
  List.concat_map (fun (label, err_code) ->
    [
      ILabel label;
      IMov (Reg RDI, Const err_code);
      (* We ended up ignoring this argument in main.c. *)
      IMov (Reg RSI, Reg RAX); 
      ICall "error";
      IRet; (* Theoretically we don't need this `ret`.*)
    ]
    )
  [
    (not_a_number_comp_label, err_COMP_NOT_NUM);
    (not_a_number_arith_label, err_ARITH_NOT_NUM);
    (not_a_bool_logic_label, err_LOGIC_NOT_BOOL);
    (not_a_bool_if_label, err_IF_NOT_BOOL);
    (overflow_label, err_OVERFLOW);

  ];;

let compile_prog ((anfed : tag aprogram), (env : arg envt)) : string =
  raise (NotYetImplemented "Compiling programs not implemented yet")
;;

(* Feel free to add additional phases to your pipeline.
   The final pipeline phase needs to return a string,
   but everything else is up to you. *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> add_err_phase well_formed is_well_formed
  (* uncomment this if you implemented a desugaring pass *)
  |> add_phase desugared desugar
  |> add_phase tagged tag (* screw ye, ya bloody formatter *)
  |> add_phase renamed rename
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase locate_bindings naive_stack_allocation
  |> add_phase result compile_prog
;;
