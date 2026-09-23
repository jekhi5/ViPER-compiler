open Printf
open Pretty
open Phases
open Exprs
open Errors
open Constants
open Env
open Util

(* ASSUMES desugaring is complete *)
let rename_and_tag (p : tag program) : tag program =
  let rec rename env p =
    match p with
    (* decls and checks have been sugared away *)
    | Program ([], body, [], tag) -> Program ([], helpE env body, [], tag)
    | Program _ ->
        raise (InternalCompilerError "decls should have been desugared away") [@coverage off]
  and helpB env (b : tag bind) =
    match b with
    | BBlank _ -> (b, env)
    | BName (name, allow_shadow, tag) ->
        let name' = sprintf "%s_%d" name (fst tag) in
        (BName (name', allow_shadow, tag), (name, name') :: env)
    | BTuple _ ->
        raise (InternalCompilerError "Tuple bindings should have been desugared away")
        [@coverage off]
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
        let call_type =
          match func with
          | EId (name, _) when StringMap.mem name initial_fun_env -> Native
          | _ -> Snake
        in
        let func = helpE env func in
        EApp (func, List.map (helpE env) args, call_type, tag)
    | ELet (bindings, body, tag) ->
        let bindings', env' = helpBG env bindings in
        let body' = helpE env' body in
        ELet (bindings', body', tag)
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
    | EException _ -> e
    (* We do NOT extend the environment for the catch block here because in desugar we wrapped
     * it in an ELet with the binding
     *)
    | ETryCatch (t, bind, excptn, c, tag) -> ETryCatch (helpE env t, bind, excptn, helpE env c, tag)
    | ECheck _ ->
        raise (InternalCompilerError "ECheck should have been desugared away") [@coverage off]
    | ETestOp1 _ ->
        raise (InternalCompilerError "ETestOp1 should have been desugared away") [@coverage off]
    | ETestOp2 _ ->
        raise (InternalCompilerError "ETestOp2 should have been desugared away") [@coverage off]
  in
  rename [] p
;;
