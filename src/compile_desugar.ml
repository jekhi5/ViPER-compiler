open Compile_constants
open Compile_utils
open Errors
open Exprs
open Pretty

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;; DESUGARING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)

let desugar (p : sourcespan program) : sourcespan program =
  let rec helpP (p : sourcespan program) =
    match p with
    | Program (decls, body, checks, tag) ->
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
        Program ([], List.fold_right wrap_G decls (helpCh checks (helpE body)), [], tag)
  (* Condense all checkblocks into a single sequence. Prepend this to the body. *)
  and helpCh checkblocks next =
    (*
     * let decls in (t1; t2; t3; nil); (t4; t5; nil); body
     *
     * TODO: Foldr or foldl?
     *)
    List.fold_right (fun e acc -> ESeq (helpE e, acc, get_tag_E e)) checkblocks next
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
    | EException _ -> e
    | ETryCatch (t, bind, excptn, c, tag) ->
        let try_fun = ELambda ([], t, tag) in
        let blank_name = gensym "blank_exn" in
        let new_bind =
          match bind with
          | BBlank btag -> BName (blank_name, false, btag)
          | _ -> bind
        in
        let excptn_id =
          match new_bind with
          | BName (name, _, _) -> EId (name, tag)
          | BBlank _ -> EId (gensym "blank_exn", tag)
          | _ -> raise (InternalCompilerError "Found non-bname in a try catch")
        in
        let excptn_check =
          EIf (EPrim2 (Eq, excptn, excptn_id, tag), c, EPrim1 (Raise, excptn_id, tag), tag)
        in
        let catch_fun = ELambda ([new_bind], excptn_check, tag) in
        ETryCatch (helpE try_fun, new_bind, excptn, helpE catch_fun, tag)
    (* Unroll a check block into a bunch of concurrent tests *)
    | ECheck ([], tag) -> ENil tag (* Dummy value *)
    | ECheck (test :: rest, tag) -> ESeq (helpE test, helpE (ECheck (rest, tag)), tag)
    | ETestOp1 (e1, pred, negation, tag) ->
        let negated x =
          if negation then
            EPrim1 (Not, x, tag)
          else
            x
        in
        let given = BName ("_given", false, tag) in
        let given_id = EId ("_given", tag) in
        let predicate = BName ("_pred", false, tag) in
        let predicate_id = EId ("_pred", tag) in
        let applied = BName ("_applied", false, tag) in
        let applied_id = EId ("_applied", tag) in
        let report_result_pass = EPrim1 (ReportTestPass, ENil tag, tag) in
        let report_result_fail_mismatch =
          EPrim2 (ReportTestFailMismatch, applied_id, negated (EBool (true, tag)), tag)
        in
        let report_result_fail_exception = EPrim1 (ReportTestFailException, ENil tag, tag) in
        helpE
          (ETryCatch
             ( ETryCatch
                 ( ELet
                     ( [ (given, e1, tag);
                         (predicate, pred, tag);
                         (applied, EApp (predicate_id, [given_id], Snake, tag), tag) ],
                       EIf
                         ( EPrim1 (IsBool, applied_id, tag),
                           EIf
                             ( negated applied_id,
                               report_result_pass,
                               report_result_fail_mismatch,
                               tag ),
                           (* TODO: Augment this with a fail due to not a predicate *)
                           report_result_fail_exception,
                           tag ),
                       tag ),
                   BBlank tag,
                   EException (Runtime, tag),
                   report_result_fail_exception,
                   tag ),
               BBlank tag,
               EException (Value, tag),
               report_result_fail_exception,
               tag ) )
    | ETestOp2 (e1, excptn, Raises, _, tag) ->
        let given_name = "_given" in
        let expected_name = "_expected" in
        let given = BName (given_name, false, tag) in
        let given_id = EId (given_name, tag) in
        let expected_id = EId (expected_name, tag) in
        let report_result_pass = EPrim1 (ReportTestPass, ENil tag, tag) in
        let report_result_fail_mismatch = EPrim2 (ReportTestFailMismatch, given_id, excptn, tag) in
        let report_result_fail_exception = EPrim1 (ReportTestFailException, given_id, tag) in
        helpE
          (ETryCatch
             ( ETryCatch
                 ( ETryCatch
                     ( ELet ([(given, e1, tag)], report_result_fail_exception, tag),
                       BBlank tag,
                       excptn,
                       report_result_pass,
                       tag ),
                   BBlank tag,
                   EException (Runtime, tag),
                   EPrim2
                     ( ReportTestFailMismatch,
                       EException (Runtime, tag),
                       EException (Value, tag),
                       tag ),
                   tag ),
               BBlank tag,
               EException (Value, tag),
               EPrim2
                 (ReportTestFailMismatch, EException (Runtime, tag), EException (Value, tag), tag),
               tag ) )
    | ETestOp2 (e1, e2, tt, negation, tag) ->
        let given_name = "_given" in
        let expected_name = "_expected" in
        let given = BName (given_name, false, tag) in
        let given_id = EId (given_name, tag) in
        let expected = BName (expected_name, false, tag) in
        let expected_id = EId (expected_name, tag) in
        let report_result_pass = EPrim1 (ReportTestPass, ENil tag, tag) in
        let report_result_fail_mismatch =
          EPrim2 (ReportTestFailMismatch, given_id, expected_id, tag)
        in
        let report_result_fail_exception = EPrim1 (ReportTestFailException, ENil tag, tag) in
        let negated x =
          if negation then
            EPrim1 (Not, x, tag)
          else
            x
        in
        let test_operator =
          match tt with
          | ShallowEq ->
              ELambda ([given; expected], negated (EPrim2 (Eq, given_id, expected_id, tag)), tag)
          | DeepEq ->
              ELambda
                ( [given; expected],
                  negated (EApp (EId ("equal", tag), [given_id; expected_id], Snake, tag)),
                  tag )
          | _ -> raise (NotYetImplemented ("unimplemented test type: " ^ string_of_test_type tt))
        in
        helpE
          (ETryCatch
             ( ETryCatch
                 ( ELet
                     ( [(given, e1, tag); (expected, e2, tag)],
                       EIf
                         ( EApp (test_operator, [given_id; expected_id], Snake, tag),
                           report_result_pass,
                           report_result_fail_mismatch,
                           tag ),
                       tag ),
                   BBlank tag,
                   EException (Runtime, tag),
                   report_result_fail_exception,
                   tag ),
               BBlank tag,
               EException (Value, tag),
               report_result_fail_exception,
               tag ) )
    | ETestOp2Pred (e1, e2, pred, negation, tag) ->
        ETestOp2Pred (helpE e1, helpE e2, helpE pred, negation, tag)
  in
  helpP p
;;
