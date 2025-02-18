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

(* Similar to Racket `split-at`,
 * except that it doesn't raise an error if the list is too short. 
 *)
let rec split_at (lst : 'a list) (pos : int) : 'a list * 'a list =
  match (lst, pos) with
  | [], _ -> ([], [])
  | rest, 0 -> ([], rest)
  | car :: cdr, n ->
      let l, r = split_at cdr (n - 1) in
      (car :: l, r)
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
    (* And and Or are sugary. We turn them into CIfs so that CPrim2s don't need to short-circuit. *)
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
        (CApp (funname, args_imm, ()), (List.concat args_setups))
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

let si_to_arg (si : int) : arg = RegOffset (~-si, RBP)

let remove_dups (lst : 'a list) : 'a list =
  List.fold_right
    (fun x acc ->
      if List.exists (fun e ->( fst e = fst x)) acc then
        acc
      else
        x :: acc )
    lst []
;;

(* ASSUMES that the program has been alpha-renamed and all names are unique *)
let naive_stack_allocation (AProgram (decls, body, t) as prog : tag aprogram) :
    tag aprogram * arg envt =
  (* For the Xexpr helpers:
   * - Immediate values don't care about the env, so we ignore those.
   * - Cexprs are only interesting in the `CIf` case, since this case
   *   contains two Aexprs.
   * - Aexprs are where the main logic happens, since that is where we make new bindings.
       We convert the stack index to a RegOffset, then look at the bound expr, then the body.
       Note that whenever we recursively call helpA, we need to increment the stack index. 
  
   *)
  let rec helpD decls env si =
    (* Every function arg is located at the same place relative to the function.
     * (i.e. either in an arg, or below RBP.)
     * Therefore, we decided to encode these in the environment as well.
     *)
    List.concat_map
      (fun (ADFun (_, args, body, _)) ->
        let body_env = helpA body env (si + 1) in
        let args_env = List.mapi (fun i a -> (a, RegOffset (i + 1, RBP))) args in
        args_env @ body_env)
      decls
  and helpC (cexp : tag cexpr) (env : arg envt) (si : int) : arg envt =
    match cexp with
    | CIf (c, thn, els, _) -> (helpA thn env (si)) @ (helpA els env (si))
    | CPrim1 _ | CPrim2 _ | CApp _ | CImmExpr _ -> env
  and helpA (aexp : tag aexpr) (env : arg envt) (si : int) : arg envt =
    match aexp with
    | ALet (id, bound, body, _) ->
        let offset = (id, si_to_arg si) in
        let bound_offset = helpC bound env si in
        let body_offset = helpA body env (si + 1) in
        (offset :: bound_offset) @ body_offset
    | ACExpr cexp -> helpC cexp env si
  in
  let decls_env = helpD decls [] 0 in
  let body_env= helpA body decls_env 0 in
  (* We were rather sloppy with the process of adding to the environment,
   * so we just remove the duplicates in O(n^2) time at the end.
   *)
  (prog, remove_dups body_env)
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

(* Enforces that the value in RAX is a bool. Goes to the specified label if not. *)
(* We could check a parameterized register, but that creates complexity in reporting the error. *)
(* We opt to hard-code RAX, for more consistency in exchange for some more boiler-plate code. *)
let check_bool (goto : string) : instruction list =
  [IMov (Reg R11, HexConst num_tag_mask); ITest (Reg RAX, Reg R11); IJz goto]
;;

(* Enforces that the value in RAX is a num. Goes to the specified label if not. *)
let check_num (goto : string) : instruction list =
  [IMov (Reg R11, HexConst num_tag_mask); ITest (Reg RAX, Reg R11); IJnz goto]
;;

let check_overflow = IJo overflow_label

(* Helper for numeric comparisons *)
let compare_prim2 (op : prim2) (e1 : arg) (e2 : arg) (t : tag) : instruction list =
  (* Move the first arg into RAX so we can type-check it. *)
  let string_op = "comparison_label" in
  let comp_label = sprintf "%s#%d" string_op t in
  let jump =
    match op with
    | Greater -> IJg comp_label
    | GreaterEq -> IJge comp_label
    | Less -> IJl comp_label
    | LessEq -> IJle comp_label
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
      IMov (Reg R11, e2);
      ICmp (Reg RAX, Reg R11);
      jump;
      IMov (Reg RAX, const_false);
      IJmp comp_done_label;
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
  | Plus -> [IMov (Reg R11, e1); IAdd (Reg RAX, Reg R11); check_overflow]
  (* Make sure to check for overflow BEFORE shifting on multiplication! *)
  | Times -> [IMov (Reg R11, e1); IMul (Reg RAX, Reg R11); check_overflow; ISar (Reg RAX, Const 1L)]
  (* For minus, we need to move e1 back into RAX to compensate for the lack of commutativity, 
   * while also preserving the order in which our arguments will fail a typecheck.
   * So, `false - true` will fail on `false` every time.
   *)
  | Minus -> [IMov (Reg R11, e2); IMov (Reg RAX, e1); ISub (Reg RAX, Reg R11); check_overflow]
  (* Comparison operators *)
  | _ -> raise (InternalCompilerError "Expected arithmetic operator.")
;;

(* Helper for boolean and. *)
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
  @ [IMov (Reg R11, bool_mask); ITest (Reg RAX, Reg R11); IJz false_label; IMov (Reg RAX, e2)]
  @ check_bool not_a_bool_logic_label
  @ [ (* Need to re-set R11 since it gets changed in check_bool.*)
      IMov (Reg R11, bool_mask);
      ITest (Reg RAX, Reg R11);
      IJz false_label;
      ILabel true_label;
      IMov (Reg RAX, const_true);
      IJmp logic_done_label;
      ILabel false_label;
      IMov (Reg RAX, const_false);
      ILabel logic_done_label;
      ILineComment (sprintf "END and#%d   -------------" t) ]
;;

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
  @ [IMov (Reg R11, bool_mask); ITest (Reg RAX, Reg R11); IJnz true_label; IMov (Reg RAX, e2)]
  @ check_bool not_a_bool_logic_label
  @ [ (* Need to re-set R11 since it gets changed in check_bool.*)
      IMov (Reg R11, bool_mask);
      ITest (Reg RAX, Reg R11);
      IJnz true_label;
      ILabel false_label;
      IMov (Reg RAX, const_false);
      IJmp logic_done_label;
      ILabel true_label;
      IMov (Reg RAX, const_true);
      ILabel logic_done_label;
      ILineComment (sprintf "END or#%d   -------------" t) ]
;;

let rec compile_fun (fun_name : string) (args : string list) (env : arg envt) : instruction list = []

and compile_aexpr (e : tag aexpr) (env : arg envt) (num_args : int) (is_tail : bool) :
    instruction list =
  match e with
  | ALet (id, bound, body, t) ->
      let prelude = compile_cexpr bound env num_args (* TODO: Come back to this number *) false in
      let body = compile_aexpr body env num_args (* TODO: Come back to this number *) is_tail in
      prelude @ body
  | ACExpr cexp -> compile_cexpr cexp env num_args is_tail

and compile_cexpr (e : tag cexpr) (env : arg envt) (num_args : int) (is_tail : bool) =
  match e with
  | CImmExpr immexp -> [IMov (Reg R11, compile_imm immexp env); IMov (Reg RAX, Reg R11)]
  | CIf (cond, thn, els, t) ->
      let else_label = sprintf "if_else#%d" t in
      let done_label = sprintf "if_done#%d" t in
      (let cond_reg = compile_imm cond env in
       [ILineComment (sprintf "BEGIN conditional#%d   -------------" t); IMov (Reg RAX, cond_reg)]
       @ check_bool not_a_bool_if_label
       @ [ IMov (Reg R11, bool_mask);
           ITest (Reg RAX, Reg R11);
           IJz else_label;
           ILineComment "  Then case:" ]
       @ compile_aexpr thn env num_args is_tail
       @ [IJmp done_label; ILineComment "  Else case:"; ILabel else_label]
       @ compile_aexpr els env num_args is_tail )
      @ [ILabel done_label; ILineComment (sprintf "END conditional#%d     -------------" t)]
  | CPrim1 (op, e, t) -> (
      let e_reg = compile_imm e env in
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
          @ [IMov (Reg R11, bool_mask); IXor (Reg RAX, Reg R11)]
      | IsBool ->
          let false_label = sprintf "is_bool_false#%d" t in
          let done_label = sprintf "is_bool_done#%d" t in
          [ ILineComment (sprintf "BEGIN is_bool%d -------------" t);
            IMov (Reg RAX, e_reg);
            ITest (Reg RAX, HexConst num_tag_mask);
            IJz false_label;
            IMov (Reg RAX, const_true);
            IJmp done_label;
            ILabel false_label;
            IMov (Reg RAX, const_false);
            ILabel done_label;
            ILineComment (sprintf "END is_bool%d   -------------" t) ]
      | IsNum ->
          let false_label = sprintf "is_num_false#%d" t in
          let done_label = sprintf "is_num_done#%d" t in
          [ ILineComment (sprintf "BEGIN is_num%d -------------" t);
            IMov (Reg RAX, e_reg);
            ITest (Reg RAX, HexConst num_tag_mask);
            (* Jump not zero because this is the inverted case from is_bool *)
            IJnz false_label;
            IMov (Reg RAX, const_true);
            IJmp done_label;
            ILabel false_label;
            IMov (Reg RAX, const_false);
            ILabel done_label;
            ILineComment (sprintf "END is_num%d   -------------" t) ]
      | Print ->
          [ (* Print both passes its value to the external function, and returns it. *)
            IMov (Reg RDI, e_reg);
            ICall "print" (* The answer goes in RAX :) *) ]
      | PrintStack -> raise (NotYetImplemented "Fill in PrintStack here")
      (* TODO *) )
  | CPrim2 (op, e1, e2, t) -> (
      let e1_reg = compile_imm e1 env in
      let e2_reg = compile_imm e2 env in
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
            IMov (Reg R11, e2_reg);
            ICmp (Reg RAX, Reg R11);
            IJe true_label;
            IMov (Reg RAX, const_false);
            IJmp done_label;
            ILabel true_label;
            IMov (Reg RAX, const_true);
            ILabel done_label ] )
  | CApp (fun_name, args, tag) ->
      let arg_regs = List.map (fun a -> compile_imm a env) args in
      (* We need to handle our caller-save registers here, and set up the args. *)
      let m = List.length args in
       List.map (fun a -> IPush a) arg_regs
      @ [ICall fun_name]
      @ [IAdd (Reg RSP, Const (Int64.of_int (8 * m)))]
      (* @ List.map (fun r -> IPop (Reg r)) first_six_args_registers *)

and compile_imm e (env : arg envt) =
  match e with
  | ImmNum (n, _) -> Const (Int64.shift_left n 1)
  | ImmBool (true, _) -> const_true
  | ImmBool (false, _) -> const_false
  | ImmId (x, _) -> find env x
;;

let compile_decl_2 (d : tag adecl) (env : arg envt) : instruction list =
  match d with
  | ADFun (fname, args, body, _) ->
    compile_fun fname args env
    @ compile_aexpr body env (List.length args) false
;;

let compile_decl (ADFun (fname, args, body, _)) (env : arg envt) : instruction list =
  (* Step 1: Set up the stack 
   * Step 2: Map arg names to their locations in registers/on the stack
   *  -> This is handled in `compile_aexpr`.
   * Step 3: Compile the function body
   * Step 4: Clean up the stack
   *)
  let m = List.length args in
  let args_env = List.mapi (fun i a -> (a, RegOffset (i + 1, RBP))) args in
  let vars = deepest_stack body env in
  let new_env = args_env @ env in
  printf "%s: " fname;
  printf "%d\n" vars;
  List.iter (fun (a, b) -> printf "%s => %s\n" a (arg_to_asm b)) new_env;
  let stack_size =
    Int64.of_int
      ( 8
      *
      if vars mod 2 = 1 then
        vars + 1
      else
        vars )
  in
  let stack_size = Int64.add stack_size 100L in
  let stack_setup =
    [ ILabel fname;
      ILineComment "==== Stack set-up ====";
      IPush (Reg RBP);
      IMov (Reg RBP, Reg RSP);
      ISub (Reg RSP, Const stack_size);
      ILineComment "======================" ]
  in
  let stack_cleanup =
    [ ILineComment "=== Stack clean-up ===";
      IAdd (Reg RSP, Const stack_size);
      IMov (Reg RSP, Reg RBP);
      IPop (Reg RBP);
      IRet;
      ILineComment "======================" ]
  in
  stack_setup @ compile_aexpr body env m false @ stack_cleanup
;;

let runtime_errors =
  List.concat_map
    (fun (label, err_code) ->
      [ ILabel label;
        IMov (Reg RDI, Const err_code);
        (* We ended up ignoring this argument in main.c. *)
        IMov (Reg RSI, Reg RAX);
        ICall "error";
        IRet (* Theoretically we don't need this `ret`.*) ] )
    [ (not_a_number_comp_label, err_COMP_NOT_NUM);
      (not_a_number_arith_label, err_ARITH_NOT_NUM);
      (not_a_bool_logic_label, err_LOGIC_NOT_BOOL);
      (not_a_bool_if_label, err_IF_NOT_BOOL);
      (overflow_label, err_OVERFLOW) ]
;;

(* as anfed : tag aprogram *)
let compile_prog (AProgram (decls, body, t), (env : arg envt)) : string =
  (* OCSH is really just a function... *)
  let all_decls = decls @ [ADFun ("our_code_starts_here", [], body, t)] in
  let compiled_decls = List.concat_map (fun d -> compile_decl d env) all_decls in
  let prelude = "section .text\nextern error\nextern print\nglobal our_code_starts_here" in
  let as_assembly_string = to_asm (compiled_decls @ runtime_errors) in
  sprintf "%s%s\n" prelude as_assembly_string
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
