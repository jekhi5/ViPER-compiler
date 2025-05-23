open Printf
open Errors
open Exprs
open Pretty
open Phases
open Assembly

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

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

let check_scope (e : sourcespan expr) : sourcespan expr =
  let rec help e env =
    match e with
    | EBool _ -> ()
    | ENumber _ -> ()
    | EId (x, loc) -> (
      try ignore (List.assoc x env)
      with Not_found ->
        raise
          (BindingError
             (sprintf "The identifier %s, used at <%s>, is not in scope" x
                (string_of_sourcespan loc) ) ) )
    | EPrim1 (_, e, _) -> help e env
    | EPrim2 (_, l, r, _) -> help l env; help r env
    | EIf (c, t, f, _) -> help c env; help t env; help f env
    | ELet (binds, body, _) ->
        let env2, _ =
          List.fold_left
            (fun (scope_env, shadow_env) (x, e, loc) ->
              try
                let existing = List.assoc x shadow_env in
                raise
                  (BindingError
                     (sprintf "The identifier %s, defined at <%s>, shadows one defined at <%s>" x
                        (string_of_sourcespan loc) (string_of_sourcespan existing) ) )
              with Not_found ->
                help e scope_env;
                ((x, loc) :: scope_env, (x, loc) :: shadow_env) )
            (env, []) binds
        in
        help body env2
  in
  help e []; e
;;

let rename (e : tag expr) : tag expr =
  let rec rename_bindings (env : (string * string) list) (bindings : tag bind list) :
      (string * string) list * tag bind list =
    List.fold_left
      (fun (new_env, renamed_bindings) (id, bound, tag) ->
        let renamed_bound = help new_env bound in
        (* rename e consistently *)
        let renamed_id = sprintf "%s#%d" id tag in
        (* create new unique name for x *)
        let renamed_binding = (renamed_id, renamed_bound, tag) in
        ((id, renamed_id) :: new_env, renamed_bindings @ [renamed_binding]) )
      (env, []) bindings
  and help (env : (string * string) list) (e : tag expr) =
    match e with
    | EId (x, tag) ->
        (* Lookup x in the environment and replace it with the environment's renamed version.
         * Since we only call `rename` *after* scope checking, x is guaranteed to be in env.
         *)
        EId (List.assoc x env, tag)
    | ELet (bindings, body, tag) ->
        (* "Extend env by renaming each binding in binds, then rename the expressions and body" *)
        let new_env, renamed_bindings = rename_bindings env bindings in
        let renamed_body = help new_env body in
        ELet (renamed_bindings, renamed_body, tag)
    (* Less interesting cases... *)
    | ENumber (_, _) -> e
    | EPrim1 (op, a, t) -> EPrim1 (op, help env a, t)
    | EPrim2 (op, a, b, t) -> EPrim2 (op, help env a, help env b, t)
    | EIf (c, t, f, ta) -> EIf (help env c, help env t, help env f, ta)
    (* TODO: Write tests for this case *)
    | EBool _ -> e
  in
  help [] e
;;

let tag (e : 'a expr) : tag expr =
  let rec help (e : 'a expr) (num : int) : tag expr * tag =
    match e with
    | EId (x, _) -> (EId (x, num), num + 1)
    | ENumber (n, _) -> (ENumber (n, num), num + 1)
    | EBool (b, _) -> (EBool (b, num), num + 1)
    | EPrim1 (op, e, _) ->
        let tag_e, new_n = help e (num + 1) in
        (EPrim1 (op, tag_e, num), new_n)
    | EPrim2 (op, e1, e2, _) ->
        let tag_e1, num_e1 = help e1 (num + 1) in
        let tag_e2, num_e2 = help e2 num_e1 in
        (EPrim2 (op, tag_e1, tag_e2, num), num_e2)
    | ELet (binds, body, _) ->
        let new_binds, num_binds =
          List.fold_left
            (fun (rev_binds, next_num) (x, b, _) ->
              let tag_b, num_b = help b (next_num + 1) in
              ((x, tag_b, next_num) :: rev_binds, num_b) )
            ([], num + 1)
            binds
        in
        let tag_body, num_body = help body num_binds in
        (ELet (List.rev new_binds, tag_body, num), num_body)
    | EIf (cond, thn, els, _) ->
        let tag_cond, num_cond = help cond (num + 1) in
        let tag_thn, num_thn = help thn num_cond in
        let tag_els, num_els = help els num_thn in
        (EIf (tag_cond, tag_thn, tag_els, num), num_els)
  in
  let ans, _ = help e 1 in
  ans
;;

let rec untag (e : 'a expr) : unit expr =
  match e with
  | EId (x, _) -> EId (x, ())
  | ENumber (n, _) -> ENumber (n, ())
  | EBool (b, _) -> EBool (b, ())
  | EPrim1 (op, e, _) -> EPrim1 (op, untag e, ())
  | EPrim2 (op, e1, e2, _) -> EPrim2 (op, untag e1, untag e2, ())
  | ELet (binds, body, _) ->
      ELet (List.map (fun (x, b, _) -> (x, untag b, ())) binds, untag body, ())
  | EIf (cond, thn, els, _) -> EIf (untag cond, untag thn, untag els, ())
;;

let anf (e : tag expr) : unit expr =
  let rec helpC (e : tag expr) : unit expr * (string * unit expr) list =
    match e with
    | EPrim1 (op, arg, _) ->
        let arg_imm, arg_setup = helpI arg in
        (EPrim1 (op, arg_imm, ()), arg_setup)
    | EPrim2 (op, left, right, _) ->
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (EPrim2 (op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf (cond, _then, _else, _) ->
        let cond_imm, cond_setup = helpI cond in
        (EIf (cond_imm, anf _then, anf _else, ()), cond_setup)
    | ENumber (n, _) -> (ENumber (n, ()), [])
    | EBool (b, _) -> (EBool (b, ()), [])
    | ELet ([], body, _) -> helpC body
    | ELet ((bind, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    | EId (name, _) -> (EId (name, ()), [])
  and helpI (e : tag expr) : unit expr * (string * unit expr) list =
    match e with
    | EPrim1 (op, arg, tag) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (EId (tmp, ()), arg_setup @ [(tmp, EPrim1 (op, arg_imm, ()))])
    | EPrim2 (op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (EId (tmp, ()), left_setup @ right_setup @ [(tmp, EPrim2 (op, left_imm, right_imm, ()))])
    | EIf (cond, _then, _else, tag) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        (EId (tmp, ()), cond_setup @ [(tmp, EIf (cond_imm, anf _then, anf _else, ()))])
    | ENumber (n, _) -> (ENumber (n, ()), [])
    | EBool (b, _) -> (EBool (b, ()), [])
    | ELet ([], body, _) -> helpI body
    | ELet ((bind, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    | EId (name, _) -> (EId (name, ()), [])
  and anf e =
    let ans, ans_setup = helpI e in
    List.fold_right (fun (bind, exp) body -> ELet ([(bind, exp, ())], body, ())) ans_setup ans
  in
  anf e
;;

let rec find (ls : (string * 'a) list) (x : string) : 'a =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y, v) :: rest ->
      if y = x then
        v
      else
        find rest x
;;

(* NOTE: Assumes that e is in ANF *)
let rec count_vars (e : 'a expr) =
  match e with
  | EIf (_, t, f, _) -> max (count_vars t) (count_vars f)
  | ELet ([(_, b, _)], body, _) -> 1 + max (count_vars b) (count_vars body)
  | _ -> 0
;;

let rec replicate (x : 'a) (i : int) : 'a list =
  if i = 0 then
    []
  else
    x :: replicate x (i - 1)
;;

let not_a_number_arith_label = "error_not_number_arith"

let not_a_number_comp_label = "error_not_number_comp"

let not_a_bool_logic_label = "error_not_bool_logic"

let not_a_bool_if_label = "error_not_bool_if"

let overflow_label = "error_overflow"

(* let check_num_arith = [ITest (Reg (RAX), HexConst (num_tag_mask)); IJnz (not_a_number_arith_label)];;
   let check_bool = [ITest (Reg (RAX), HexConst (bool_tag_mask)); IJnz (not_a_bool_label)];; *)

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

let rec compile_expr (e : tag expr) (si : int) (env : (string * int) list) : instruction list =
  match e with
  | ELet ([(id, e, _)], body, _) ->
      let prelude = compile_expr e (si + 1) env in
      let body = compile_expr body (si + 1) ((id, si) :: env) in
      prelude @ [IMov (RegOffset (~-si, RBP), Reg RAX)] @ body
  | EPrim1 (op, e, t) -> (
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
      | PrintStack -> raise (NotYetImplemented "Fill in PrintStack here") )
  | EPrim2 (op, e1, e2, t) -> (
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
  | EIf (cond, thn, els, t) ->
      let else_label = sprintf "if_else#%d" t in
      let done_label = sprintf "if_done#%d" t in
      (let cond_reg = compile_imm cond env in
       [ILineComment (sprintf "BEGIN conditional#%d   -------------" t); IMov (Reg RAX, cond_reg)]
       @ check_bool not_a_bool_if_label
       @ [ IMov (Reg R11, bool_mask);
           ITest (Reg RAX, Reg R11);
           IJz else_label;
           ILineComment "  Then case:" ]
       @ compile_expr thn (si + 1) env
       @ [IJmp done_label; ILineComment "  Else case:"; ILabel else_label]
       @ compile_expr els (si + 1) env )
      @ [ILabel done_label; ILineComment (sprintf "END conditional#%d     -------------" t)]
  | ENumber _ -> [IMov (Reg RAX, compile_imm e env)]
  | EBool _ -> [IMov (Reg RAX, compile_imm e env)]
  | EId _ -> [IMov (Reg RAX, compile_imm e env)]
  | _ -> raise (InternalCompilerError "Impossible: Not in ANF")

and compile_imm (e : tag expr) (env : (string * int) list) : arg =
  match e with
  | ENumber (n, _) ->
      (* Max:  4611686018427387903
       * Min: -4611686018427387904
       *)
      if n > Int64.div Int64.max_int 2L || n < Int64.div Int64.min_int 2L then
        raise (OverflowError ("Integer overflow: " ^ Int64.to_string n))
      else
        Const (Int64.mul n 2L)
  | EBool (true, _) -> const_true
  | EBool (false, _) -> const_false
  | EId (x, _) -> RegOffset (~-(find env x), RBP)
  | _ -> raise (InternalCompilerError "Impossible: not an immediate")
;;

let compile_prog (anfed : tag expr) : string =
  let prelude =
    "section .text\nextern error\nextern print\nglobal our_code_starts_here\nour_code_starts_here:"
  in
  let vars = count_vars anfed in
  (* Keep the stack aligned. *)
  let stack_size =
    Int64.of_int
      ( 8
      *
      if vars mod 2 == 1 then
        vars + 1
      else
        vars )
  in
  let stack_setup =
    [ ILineComment "==== Stack set-up ====";
      IPush (Reg RBP);
      IMov (Reg RBP, Reg RSP);
      ISub (Reg RSP, Const stack_size);
      ILineComment "======================" ]
  in
  let postlude =
    [ (* Stack clean-up *)
      ILineComment "=== Stack clean-up ===";
      IAdd (Reg RSP, Const stack_size);
      IMov (Reg RSP, Reg RBP);
      IPop (Reg RBP);
      ILineComment "======================";
      IRet;
      ILabel not_a_number_arith_label;
      IMov (Reg RDI, Const err_ARITH_NOT_NUM);
      IMov (Reg RSI, Reg RAX);
      ICall "error";
      IRet;
      ILabel not_a_number_comp_label;
      IMov (Reg RDI, Const err_COMP_NOT_NUM);
      IMov (Reg RSI, Reg RAX);
      ICall "error";
      IRet;
      ILabel not_a_bool_logic_label;
      IMov (Reg RDI, Const err_LOGIC_NOT_BOOL);
      IMov (Reg RSI, Reg RAX);
      ICall "error";
      IRet;
      ILabel not_a_bool_if_label;
      IMov (Reg RDI, Const err_IF_NOT_BOOL);
      IMov (Reg RSI, Reg RAX);
      ICall "error";
      IRet;
      ILabel overflow_label;
      IMov (Reg RDI, Const err_OVERFLOW);
      IMov (Reg RSI, Reg RAX);
      ICall "error";
      IRet ]
  in
  let body = compile_expr anfed 1 [] in
  let as_assembly_string = to_asm (stack_setup @ body @ postlude) in
  sprintf "%s%s\n" prelude as_assembly_string
;;

let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog |> add_phase well_formed check_scope |> add_phase tagged tag |> add_phase renamed rename
  |> add_phase anfed (fun p -> tag (anf p))
  |> add_phase result compile_prog
;;
