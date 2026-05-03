open Errors
open Exprs
open Pretty
open Printf


(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;; ANFING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)

type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : sourcespan aprogram =
  let rec helpP (p : tag program) : sourcespan aprogram =
    match p with
    | Program ([], body, _, (_, s)) -> AProgram (helpA body, s)
    | Program _ -> raise (InternalCompilerError "decls should have been desugared away")
  and processBinding (bind, rhs, _) =
    match bind with
    | BName (name, _, _) -> (name, helpC rhs)
    | _ ->
        raise
          (InternalCompilerError
             (sprintf "Encountered a non-simple binding in ANFing a let-rec: %s"
                (string_of_bind bind) ) )
  and helpC (e : tag expr) : sourcespan cexpr * sourcespan anf_bind list =
    match e with
    | EPrim1 (op, arg, (_, s)) ->
        let arg_imm, arg_setup = helpI arg in
        (CPrim1 (op, arg_imm, s), arg_setup)
    | EPrim2 (op, left, right, (_, s)) ->
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (CPrim2 (op, left_imm, right_imm, s), left_setup @ right_setup)
    | EIf (cond, _then, _else, (_, s)) ->
        let cond_imm, cond_setup = helpI cond in
        (CIf (cond_imm, helpA _then, helpA _else, s), cond_setup)
    | ELet ([], body, _) -> helpC body
    | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELet ((BName (bind, _, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELetRec ([binding], body, _) ->
        let name, new_bind_setup = processBinding binding in
        let _, bound_setup = new_bind_setup in
        let lambda =
          match bound_setup with
          | [BLet (_, lambda)] -> lambda
          | _ -> raise (InternalCompilerError "LetRec of non-lambda")
        in
        let body_ans, body_setup = helpC body in
        (body_ans, BLetRec [(name, lambda)] :: body_setup)
    | ELetRec _ -> raise (NotYetImplemented "Mutual recursion")
    | ELambda (args, body, (a, s)) ->
        let processBind bind =
          match bind with
          | BName (name, _, _) -> name
          | _ ->
              raise
                (InternalCompilerError
                   (sprintf "Encountered a non-simple binding in ANFing a lambda: %s"
                      (string_of_bind bind) ) )
        in
        let new_clambda = CLambda (List.map processBind args, helpA body, s) in
        let name = sprintf "lam_%d" a in
        let imm_id = ImmId (name, s) in
        (CImmExpr imm_id, [BLet (name, new_clambda)])
    | ELet ((BTuple (_, _), _, _) :: _, _, _) ->
        raise (InternalCompilerError "Tuple bindings should have been desugared away")
    | EApp (func, args, native, (_, s)) ->
        let func_ans, func_setup = helpI func in
        let new_args, new_setup = List.split (List.map helpI args) in
        (CApp (func_ans, new_args, native, s), func_setup @ List.concat new_setup)
    | ESeq (e1, e2, _) ->
        let e1_ans, e1_setup = helpC e1 in
        let e2_ans, e2_setup = helpC e2 in
        (e2_ans, e1_setup @ [BSeq e1_ans] @ e2_setup)
    | ETuple (args, (_, s)) ->
        let new_args, new_setup = List.split (List.map helpI args) in
        (CTuple (new_args, s), List.concat new_setup)
    | EGetItem (tup, idx, (_, s)) ->
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        (CGetItem (tup_imm, idx_imm, s), tup_setup @ idx_setup)
    | ESetItem (tup, idx, newval, (_, s)) ->
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let new_imm, new_setup = helpI newval in
        (CSetItem (tup_imm, idx_imm, new_imm, s), tup_setup @ idx_setup @ new_setup)
    | ETryCatch (t, _, EException (except, _), c, (_, s)) ->
        let t_imm, t_setup = helpI t in
        let c_imm, c_setup = helpI c in
        (CTryCatch (t_imm, except, c_imm, s), t_setup @ c_setup)
    | ETryCatch _ ->
        raise (InternalCompilerError "Violated invatiant: Tried to catch a non-exception")
    | ECheck (checks, (_, s)) ->
        let new_checks, checks_setup = List.split (List.map helpI checks) in
        (CCheck (new_checks, s), List.concat checks_setup)
    | ETestOp1 (e1, e2, negation, (_, s)) ->
        let e1_imm, e1_setup = helpI e1 in
        let e2_imm, e2_setup = helpI e2 in
        (CTestOp1 (e1_imm, e2_imm, negation, s), e1_setup @ e2_setup)
    | ETestOp2 (e1, e2, tt, negation, (_, s)) ->
        let e1_imm, e1_setup = helpI e1 in
        let e2_imm, e2_setup = helpI e2 in
        (CTestOp2 (e1_imm, e2_imm, tt, negation, s), e1_setup @ e2_setup)
    | ETestOp2Pred (e1, e2, pred, negation, (_, s)) ->
        let e1_imm, e1_setup = helpI e1 in
        let e2_imm, e2_setup = helpI e2 in
        let pred_imm, pred_setup = helpI pred in
        (CTestOp2Pred (e1_imm, e2_imm, pred_imm, negation, s), e1_setup @ e2_setup @ pred_setup)
    | _ ->
        let imm, setup = helpI e in
        (CImmExpr imm, setup)
  and helpI (e : tag expr) : sourcespan immexpr * sourcespan anf_bind list =
    match e with
    | ENumber (n, (_, s)) -> (ImmNum (n, s), [])
    | EBool (b, (_, s)) -> (ImmBool (b, s), [])
    | EId (name, (_, s)) -> (ImmId (name, s), [])
    | ENil (_, s) -> (ImmNil s, [])
    | ESeq (e1, e2, _) ->
        let _, e1_setup = helpI e1 in
        let e2_imm, e2_setup = helpI e2 in
        (e2_imm, e1_setup @ e2_setup)
    | ETuple (args, (tag, s)) ->
        let tmp = sprintf "tup_%d" tag in
        let new_args, new_setup = List.split (List.map helpI args) in
        (ImmId (tmp, s), List.concat new_setup @ [BLet (tmp, CTuple (new_args, s))])
    | EGetItem (tup, idx, (tag, s)) ->
        let tmp = sprintf "get_%d" tag in
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        (ImmId (tmp, s), tup_setup @ idx_setup @ [BLet (tmp, CGetItem (tup_imm, idx_imm, s))])
    | ESetItem (tup, idx, newval, (tag, s)) ->
        let tmp = sprintf "set_%d" tag in
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let new_imm, new_setup = helpI newval in
        ( ImmId (tmp, s),
          tup_setup @ idx_setup @ new_setup @ [BLet (tmp, CSetItem (tup_imm, idx_imm, new_imm, s))]
        )
    | EPrim1 (op, arg, (tag, s)) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (ImmId (tmp, s), arg_setup @ [BLet (tmp, CPrim1 (op, arg_imm, s))])
    | EPrim2 (op, left, right, (tag, s)) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        ( ImmId (tmp, s),
          left_setup @ right_setup @ [BLet (tmp, CPrim2 (op, left_imm, right_imm, s))] )
    | EIf (cond, _then, _else, (tag, s)) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        (ImmId (tmp, s), cond_setup @ [BLet (tmp, CIf (cond_imm, helpA _then, helpA _else, s))])
    | EApp (func, args, native, (tag, s)) ->
        let tmp = sprintf "app_%d" tag in
        let new_func, func_setup = helpI func in
        let new_args, new_setup = List.split (List.map helpI args) in
        ( ImmId (tmp, s),
          func_setup @ List.concat new_setup @ [BLet (tmp, CApp (new_func, new_args, native, s))] )
    | ELet ([], body, _) -> helpI body
    | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELetRec (binds, body, (tag, s)) ->
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
        ( ImmId (tmp, s),
          List.concat new_setup
          @ [BLetRec (List.combine names new_binds)]
          @ body_setup
          @ [BLet (tmp, body_ans)] )
    | ELambda (args, body, (tag, s)) ->
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
        (ImmId (tmp, s), [BLet (tmp, CLambda (List.map processBind args, helpA body, s))])
    | ELet ((BName (bind, _, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELet ((BTuple (_, _), _, _) :: _, _, _) ->
        raise (InternalCompilerError "Tuple bindings should have been desugared away")
    | EException (ex, (_, s)) -> (ImmExcept (ex, s), [])
    | ETryCatch (t, _, EException (except, _), c, (tag, s)) ->
        let tmp = sprintf "try_catch_%d" tag in
        let new_t, t_setup = helpI t in
        let new_c, c_setup = helpI c in
        (ImmId (tmp, s), t_setup @ c_setup @ [BLet (tmp, CTryCatch (new_t, except, new_c, s))])
    | ETryCatch _ ->
        raise (InternalCompilerError "Violated invariant. Tried to catch a non-exception")
    | ECheck (checks, (tag, s)) ->
        let tmp = sprintf "check_%d" tag in
        let new_checks, new_setup = List.split (List.map helpI checks) in
        (ImmId (tmp, s), List.concat new_setup @ [BLet (tmp, CCheck (new_checks, s))])
    | ETestOp1 (e1, e2, negation, (tag, s)) ->
        let tmp = sprintf "testop1_%d" tag in
        let e1_ans, e1_setup = helpI e1 in
        let e2_ans, e2_setup = helpI e2 in
        (ImmId (tmp, s), e1_setup @ e2_setup @ [BLet (tmp, CTestOp1 (e1_ans, e2_ans, negation, s))])
    | ETestOp2 (e1, e2, tt, negation, (tag, s)) ->
        let tmp = sprintf "testop2_%d" tag in
        let e1_ans, e1_setup = helpI e1 in
        let e2_ans, e2_setup = helpI e2 in
        ( ImmId (tmp, s),
          e1_setup @ e2_setup @ [BLet (tmp, CTestOp2 (e1_ans, e2_ans, tt, negation, s))] )
    | ETestOp2Pred (e1, e2, pred, negation, (tag, s)) ->
        let tmp = sprintf "testop2pred_%d" tag in
        let e1_ans, e1_setup = helpI e1 in
        let e2_ans, e2_setup = helpI e2 in
        let pred_ans, pred_setup = helpI pred in
        ( ImmId (tmp, s),
          e1_setup @ e2_setup @ pred_setup
          @ [BLet (tmp, CTestOp2Pred (e1_ans, e2_ans, pred_ans, negation, s))] )
  and helpA (e : tag expr) : sourcespan aexpr =
    let ans, ans_setup = helpC e in
    List.fold_right
      (fun bind body ->
        match bind with
        | BSeq exp -> ASeq (exp, body, get_tag_A body)
        | BLet (name, exp) -> ALet (name, exp, body, get_tag_A body)
        | BLetRec names -> ALetRec (names, body, get_tag_A body) )
      ans_setup (ACExpr ans)
  in
  helpP p
;;
