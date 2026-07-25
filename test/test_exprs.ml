open Test_funcs
open Exprs
open OUnit2

(* Tests for the exprs functions for ViPER *)

let square = fun x -> x * x

let ss1 = (make_pos "test" 1 0 5, make_pos "test" 1 0 10)

let tag42 : tag = (42, ss1)

(* Leaves tagged with ss1, used as inputs to map_tag_E / untagE, and their
   mapped ((42, ss1)-tagged) / untagged (()-tagged) counterparts. *)
let numE = ENumber (1L, ss1)

let numM = ENumber (1L, tag42)

let numU = ENumber (1L, ())

let boolE = EBool (true, ss1)

let boolM = EBool (true, tag42)

let boolU = EBool (true, ())

let idE = EId ("x", ss1)

let idM = EId ("x", tag42)

let idU = EId ("x", ())

(* debug_printf reads the mutable show_debug_print ref, so its two branches are exercised by
   toggling that ref immediately before each call. Both calls happen here, at list-construction
   time (tae's args are eager), so the ref is restored to its original value right after -
   before OUnit runs anything - to avoid leaking state into other tests. *)
let original_show_debug_print = !show_debug_print

let () = show_debug_print := false

let debug_printf_disabled_result = debug_printf "debug %d" 1

let () = show_debug_print := true

let debug_printf_enabled_result = debug_printf "debug %d" 1

let () = show_debug_print := original_show_debug_print

let test_suite =
  [ (* --- debug_printf --- *)
    tae "debugPrintfDisabled" () debug_printf_disabled_result;
    tae "debugPrintfEnabled" () debug_printf_enabled_result;
    (* --- map_opt --- *)
    tae "mapOptNone" None (Exprs.map_opt (fun _ -> false) None);
    tae "mapOptSquare" (Some 9) (Exprs.map_opt square (Some 3));
    (* --- get_tag_E --- *)
    tae "get_tag_ELet" (Some true) (Exprs.get_tag_E (ELet ([], ENumber (1L, None), Some true)));
    tae "get_tag_ELetRec" (Some true)
      (Exprs.get_tag_E (ELetRec ([], ENumber (1L, None), Some true)));
    tae "get_tag_EPrim1" (Some true)
      (Exprs.get_tag_E (EPrim1 (Add1, ENumber (1L, None), Some true)));
    tae "get_tag_EPrim2" (Some true)
      (Exprs.get_tag_E (EPrim2 (Plus, ENumber (1L, None), ENumber (1L, None), Some true)));
    tae "get_tag_EIf" (Some true)
      (Exprs.get_tag_E
         (EIf (EBool (true, None), ENumber (1L, None), ENumber (1L, None), Some true)) );
    tae "get_tag_ENil" (Some true) (Exprs.get_tag_E (ENil (Some true)));
    tae "get_tag_ENumber" (Some true) (Exprs.get_tag_E (ENumber (1L, Some true)));
    tae "get_tag_EBool" (Some true) (Exprs.get_tag_E (EBool (true, Some true)));
    tae "get_tag_EId" (Some true) (Exprs.get_tag_E (EId ("x", Some true)));
    tae "get_tag_EApp" (Some true)
      (Exprs.get_tag_E (EApp (ENumber (1L, None), [], Unknown, Some true)));
    tae "get_tag_ETuple" (Some true) (Exprs.get_tag_E (ETuple ([], Some true)));
    tae "get_tag_EGetItem" (Some true)
      (Exprs.get_tag_E (EGetItem (ENumber (1L, None), ENumber (1L, None), Some true)));
    tae "get_tag_ESetItem" (Some true)
      (Exprs.get_tag_E
         (ESetItem (ENumber (1L, None), ENumber (1L, None), ENumber (1L, None), Some true)) );
    tae "get_tag_ESeq" (Some true)
      (Exprs.get_tag_E (ESeq (ENumber (1L, None), ENumber (1L, None), Some true)));
    tae "get_tag_ELambda" (Some true)
      (Exprs.get_tag_E (ELambda ([], ENumber (1L, None), Some true)));
    tae "get_tag_EException" (Some true) (Exprs.get_tag_E (EException (Runtime, Some true)));
    tae "get_tag_ETryCatch" (Some true)
      (Exprs.get_tag_E
         (ETryCatch
            (ENumber (1L, None), BBlank None, ENumber (1L, None), ENumber (1L, None), Some true) ) );
    tae "get_tag_ECheck" (Some true) (Exprs.get_tag_E (ECheck ([], Some true)));
    tae "get_tag_ETestOp1" (Some true)
      (Exprs.get_tag_E (ETestOp1 (ENumber (1L, None), ENumber (1L, None), false, Some true)));
    tae "get_tag_ETestOp2" (Some true)
      (Exprs.get_tag_E (ETestOp2 (ENumber (1L, None), ENumber (1L, None), Pred, false, Some true)));
    tae "get_tag_ETestOp2Pred" (Some true)
      (Exprs.get_tag_E
         (ETestOp2Pred (ENumber (1L, None), ENumber (1L, None), ENumber (1L, None), false, Some true)
         ) );
    (* --- get_tag_I --- *)
    tae "get_tag_ImmNum" (Some true) (get_tag_I (ImmNum (1L, Some true)));
    tae "get_tag_ImmBool" (Some true) (get_tag_I (ImmBool (true, Some true)));
    tae "get_tag_ImmId" (Some true) (get_tag_I (ImmId ("x", Some true)));
    tae "get_tag_ImmNil" (Some true) (get_tag_I (ImmNil (Some true)));
    tae "get_tag_ImmExcept" (Some true) (get_tag_I (ImmExcept (Runtime, Some true)));
    (* --- get_tag_C --- *)
    tae "get_tag_CImmExpr" (Some true) (get_tag_C (CImmExpr (ImmNum (1L, Some true))));
    tae "get_tag_CApp" (Some true) (get_tag_C (CApp (ImmNum (1L, None), [], Unknown, Some true)));
    tae "get_tag_CCheck" (Some true) (get_tag_C (CCheck ([], Some true)));
    tae "get_tag_CGetItem" (Some true)
      (get_tag_C (CGetItem (ImmNum (1L, None), ImmNum (1L, None), Some true)));
    tae "get_tag_CIf" (Some true)
      (get_tag_C
         (CIf
            ( ImmBool (true, None),
              ACExpr (CImmExpr (ImmNum (1L, None))),
              ACExpr (CImmExpr (ImmNum (1L, None))),
              Some true ) ) );
    tae "get_tag_CLambda" (Some true)
      (get_tag_C (CLambda ([], ACExpr (CImmExpr (ImmNum (1L, None))), Some true)));
    tae "get_tag_CPrim1" (Some true) (get_tag_C (CPrim1 (Add1, ImmNum (1L, None), Some true)));
    tae "get_tag_CPrim2" (Some true)
      (get_tag_C (CPrim2 (Plus, ImmNum (1L, None), ImmNum (1L, None), Some true)));
    tae "get_tag_CSetItem" (Some true)
      (get_tag_C (CSetItem (ImmNum (1L, None), ImmNum (1L, None), ImmNum (1L, None), Some true)));
    tae "get_tag_CTestOp1" (Some true)
      (get_tag_C (CTestOp1 (ImmNum (1L, None), ImmNum (1L, None), false, Some true)));
    tae "get_tag_CTestOp2" (Some true)
      (get_tag_C (CTestOp2 (ImmNum (1L, None), ImmNum (1L, None), Pred, false, Some true)));
    tae "get_tag_CTestOp2Pred" (Some true)
      (get_tag_C
         (CTestOp2Pred (ImmNum (1L, None), ImmNum (1L, None), ImmNum (1L, None), false, Some true)) );
    tae "get_tag_CTryCatch" (Some true)
      (get_tag_C (CTryCatch (ImmNum (1L, None), Runtime, ImmNum (1L, None), Some true)));
    tae "get_tag_CTuple" (Some true) (get_tag_C (CTuple ([], Some true)));
    (* --- get_tag_A --- *)
    tae "get_tag_ACExpr" (Some true) (get_tag_A (ACExpr (CImmExpr (ImmNum (1L, Some true)))));
    tae "get_tag_ALet" (Some true)
      (get_tag_A
         (ALet ("x", CImmExpr (ImmNum (1L, None)), ACExpr (CImmExpr (ImmNum (1L, None))), Some true)) );
    tae "get_tag_ALetRec" (Some true)
      (get_tag_A (ALetRec ([], ACExpr (CImmExpr (ImmNum (1L, None))), Some true)));
    tae "get_tag_ASeq" (Some true)
      (get_tag_A
         (ASeq (CImmExpr (ImmNum (1L, None)), ACExpr (CImmExpr (ImmNum (1L, None))), Some true)) );
    (* --- get_tag_D --- *)
    tae "get_tag_DFun" (Some true) (get_tag_D (DFun ("f", [], ENumber (1L, None), Some true)));
    (* --- map_tag_E --- *)
    tae "map_tag_ESeq"
      (ESeq (numM, boolM, tag42))
      (map_tag_E (fun _ -> 42) (ESeq (numE, boolE, ss1)));
    tae "map_tag_ETuple"
      (ETuple ([numM; boolM; idM], tag42))
      (map_tag_E (fun _ -> 42) (ETuple ([numE; boolE; idE], ss1)));
    tae "map_tag_EGetItem"
      (EGetItem (numM, idM, tag42))
      (map_tag_E (fun _ -> 42) (EGetItem (numE, idE, ss1)));
    tae "map_tag_ESetItem"
      (ESetItem (numM, idM, boolM, tag42))
      (map_tag_E (fun _ -> 42) (ESetItem (numE, idE, boolE, ss1)));
    tae "map_tag_EId" (EId ("y", tag42)) (map_tag_E (fun _ -> 42) (EId ("y", ss1)));
    tae "map_tag_ENumber" (ENumber (5L, tag42)) (map_tag_E (fun _ -> 42) (ENumber (5L, ss1)));
    tae "map_tag_EBool" (EBool (false, tag42)) (map_tag_E (fun _ -> 42) (EBool (false, ss1)));
    tae "map_tag_ENil" (ENil tag42) (map_tag_E (fun _ -> 42) (ENil ss1));
    tae "map_tag_EPrim1"
      (EPrim1 (Add1, numM, tag42))
      (map_tag_E (fun _ -> 42) (EPrim1 (Add1, numE, ss1)));
    tae "map_tag_EPrim2"
      (EPrim2 (Plus, numM, boolM, tag42))
      (map_tag_E (fun _ -> 42) (EPrim2 (Plus, numE, boolE, ss1)));
    tae "map_tag_ELet"
      (ELet ([(BName ("z", false, tag42), numM, tag42)], boolM, tag42))
      (map_tag_E (fun _ -> 42) (ELet ([(BName ("z", false, ss1), numE, ss1)], boolE, ss1)));
    tae "map_tag_ELetRec"
      (ELetRec ([(BName ("g", true, tag42), numM, tag42)], boolM, tag42))
      (map_tag_E (fun _ -> 42) (ELetRec ([(BName ("g", true, ss1), numE, ss1)], boolE, ss1)));
    tae "map_tag_EIf"
      (EIf (boolM, numM, idM, tag42))
      (map_tag_E (fun _ -> 42) (EIf (boolE, numE, idE, ss1)));
    tae "map_tag_EApp"
      (EApp (idM, [numM; boolM], Snake, tag42))
      (map_tag_E (fun _ -> 42) (EApp (idE, [numE; boolE], Snake, ss1)));
    tae "map_tag_ELambda"
      (ELambda ([BName ("a", false, tag42)], numM, tag42))
      (map_tag_E (fun _ -> 42) (ELambda ([BName ("a", false, ss1)], numE, ss1)));
    tae "map_tag_EException"
      (EException (Value, tag42))
      (map_tag_E (fun _ -> 42) (EException (Value, ss1)));
    tae "map_tag_ETryCatch"
      (ETryCatch (numM, BName ("e", false, tag42), boolM, idM, tag42))
      (map_tag_E (fun _ -> 42) (ETryCatch (numE, BName ("e", false, ss1), boolE, idE, ss1)));
    tae "map_tag_ECheck"
      (ECheck ([numM; boolM], tag42))
      (map_tag_E (fun _ -> 42) (ECheck ([numE; boolE], ss1)));
    tae "map_tag_ETestOp1"
      (ETestOp1 (numM, boolM, true, tag42))
      (map_tag_E (fun _ -> 42) (ETestOp1 (numE, boolE, true, ss1)));
    tae "map_tag_ETestOp2"
      (ETestOp2 (numM, boolM, DeepEq, false, tag42))
      (map_tag_E (fun _ -> 42) (ETestOp2 (numE, boolE, DeepEq, false, ss1)));
    tae "map_tag_ETestOp2Pred"
      (ETestOp2Pred (numM, boolM, idM, true, tag42))
      (map_tag_E (fun _ -> 42) (ETestOp2Pred (numE, boolE, idE, true, ss1)));
    (* --- map_tag_B --- *)
    tae "map_tag_BBlank" (BBlank tag42) (map_tag_B (fun _ -> 42) (BBlank ss1));
    tae "map_tag_BName"
      (BName ("v", false, tag42))
      (map_tag_B (fun _ -> 42) (BName ("v", false, ss1)));
    tae "map_tag_BTuple"
      (BTuple ([BBlank tag42; BName ("w", true, tag42)], tag42))
      (map_tag_B (fun _ -> 42) (BTuple ([BBlank ss1; BName ("w", true, ss1)], ss1)));
    (* --- map_tag_D --- *)
    tae "map_tag_DFun"
      (DFun ("f", [BName ("x", false, tag42)], numM, tag42))
      (map_tag_D (fun _ -> 42) (DFun ("f", [BName ("x", false, ss1)], numE, ss1)));
    (* --- map_tag_P --- *)
    tae "map_tag_PProgram"
      (Program ([[DFun ("f", [BName ("x", false, tag42)], numM, tag42)]], boolM, [idM], tag42))
      (map_tag_P
         (fun _ -> 42)
         (Program ([[DFun ("f", [BName ("x", false, ss1)], numE, ss1)]], boolE, [idE], ss1)) );
    (* --- tag --- *)
    tae "tagProgram"
      (Program ([], ENumber (5L, (2, ss1)), [], (1, ss1)))
      (tag (Program ([], ENumber (5L, ss1), [], ss1)));
    (* --- untagE --- *)
    tae "untagESeq" (ESeq (numU, boolU, ())) (untagE (ESeq (numE, boolE, ss1)));
    tae "untagETuple" (ETuple ([numU; boolU; idU], ())) (untagE (ETuple ([numE; boolE; idE], ss1)));
    tae "untagEGetItem" (EGetItem (numU, idU, ())) (untagE (EGetItem (numE, idE, ss1)));
    tae "untagESetItem"
      (ESetItem (numU, idU, boolU, ()))
      (untagE (ESetItem (numE, idE, boolE, ss1)));
    tae "untagEId" (EId ("y", ())) (untagE (EId ("y", ss1)));
    tae "untagENumber" (ENumber (5L, ())) (untagE (ENumber (5L, ss1)));
    tae "untagEBool" (EBool (false, ())) (untagE (EBool (false, ss1)));
    tae "untagENil" (ENil ()) (untagE (ENil ss1));
    tae "untagEPrim1" (EPrim1 (Add1, numU, ())) (untagE (EPrim1 (Add1, numE, ss1)));
    tae "untagEPrim2" (EPrim2 (Plus, numU, boolU, ())) (untagE (EPrim2 (Plus, numE, boolE, ss1)));
    tae "untagELet"
      (ELet ([(BName ("z", false, ()), numU, ())], boolU, ()))
      (untagE (ELet ([(BName ("z", false, ss1), numE, ss1)], boolE, ss1)));
    tae "untagELetRec"
      (ELetRec ([(BName ("g", true, ()), numU, ())], boolU, ()))
      (untagE (ELetRec ([(BName ("g", true, ss1), numE, ss1)], boolE, ss1)));
    tae "untagEIf" (EIf (boolU, numU, idU, ())) (untagE (EIf (boolE, numE, idE, ss1)));
    tae "untagEApp"
      (EApp (idU, [numU; boolU], Snake, ()))
      (untagE (EApp (idE, [numE; boolE], Snake, ss1)));
    tae "untagELambda"
      (ELambda ([BName ("a", false, ())], numU, ()))
      (untagE (ELambda ([BName ("a", false, ss1)], numE, ss1)));
    tae "untagEException" (EException (Value, ())) (untagE (EException (Value, ss1)));
    tae "untagETryCatch"
      (ETryCatch (numU, BName ("e", false, ()), boolU, idU, ()))
      (untagE (ETryCatch (numE, BName ("e", false, ss1), boolE, idE, ss1)));
    tae "untagECheck" (ECheck ([numU; boolU], ())) (untagE (ECheck ([numE; boolE], ss1)));
    tae "untagETestOp1"
      (ETestOp1 (numU, boolU, true, ()))
      (untagE (ETestOp1 (numE, boolE, true, ss1)));
    tae "untagETestOp2"
      (ETestOp2 (numU, boolU, DeepEq, false, ()))
      (untagE (ETestOp2 (numE, boolE, DeepEq, false, ss1)));
    tae "untagETestOp2Pred"
      (ETestOp2Pred (numU, boolU, idU, true, ()))
      (untagE (ETestOp2Pred (numE, boolE, idE, true, ss1)));
    (* --- untagB --- *)
    tae "untagBBlank" (BBlank ()) (untagB (BBlank ss1));
    tae "untagBName" (BName ("v", false, ())) (untagB (BName ("v", false, ss1)));
    tae "untagBTuple"
      (BTuple ([BBlank (); BName ("w", true, ())], ()))
      (untagB (BTuple ([BBlank ss1; BName ("w", true, ss1)], ss1)));
    (* --- untagD --- *)
    tae "untagDFun"
      (DFun ("f", [BName ("x", false, ())], numU, ()))
      (untagD (DFun ("f", [BName ("x", false, ss1)], numE, ss1)));
    (* --- untagP --- *)
    tae "untagPProgram"
      (Program ([[DFun ("f", [BName ("x", false, ())], numU, ())]], boolU, [idU], ()))
      (untagP (Program ([[DFun ("f", [BName ("x", false, ss1)], numE, ss1)]], boolE, [idE], ss1)));
    (* --- atag --- *)
    tae "atagCImmExprImmNum"
      (AProgram (ACExpr (CImmExpr (ImmNum (5L, (1, ss1)))), (0, ss1)))
      (atag (AProgram (ACExpr (CImmExpr (ImmNum (5L, ss1))), ss1)));
    tae "atagImmNil"
      (AProgram (ACExpr (CImmExpr (ImmNil (1, ss1))), (0, ss1)))
      (atag (AProgram (ACExpr (CImmExpr (ImmNil ss1)), ss1)));
    tae "atagImmBool"
      (AProgram (ACExpr (CImmExpr (ImmBool (true, (1, ss1)))), (0, ss1)))
      (atag (AProgram (ACExpr (CImmExpr (ImmBool (true, ss1))), ss1)));
    tae "atagImmId"
      (AProgram (ACExpr (CImmExpr (ImmId ("x", (1, ss1)))), (0, ss1)))
      (atag (AProgram (ACExpr (CImmExpr (ImmId ("x", ss1))), ss1)));
    tae "atagImmExcept"
      (AProgram (ACExpr (CImmExpr (ImmExcept (Runtime, (1, ss1)))), (0, ss1)))
      (atag (AProgram (ACExpr (CImmExpr (ImmExcept (Runtime, ss1))), ss1)));
    tae "atagCPrim1"
      (AProgram (ACExpr (CPrim1 (Add1, ImmNum (1L, (2, ss1)), (1, ss1))), (0, ss1)))
      (atag (AProgram (ACExpr (CPrim1 (Add1, ImmNum (1L, ss1), ss1)), ss1)));
    tae "atagCPrim2"
      (AProgram
         (ACExpr (CPrim2 (Plus, ImmNum (1L, (3, ss1)), ImmNum (2L, (2, ss1)), (1, ss1))), (0, ss1))
      )
      (atag (AProgram (ACExpr (CPrim2 (Plus, ImmNum (1L, ss1), ImmNum (2L, ss1), ss1)), ss1)));
    tae "atagCIf"
      (AProgram
         ( ACExpr
             (CIf
                ( ImmNum (1L, (4, ss1)),
                  ACExpr (CImmExpr (ImmNum (2L, (3, ss1)))),
                  ACExpr (CImmExpr (ImmNum (3L, (2, ss1)))),
                  (1, ss1) ) ),
           (0, ss1) ) )
      (atag
         (AProgram
            ( ACExpr
                (CIf
                   ( ImmNum (1L, ss1),
                     ACExpr (CImmExpr (ImmNum (2L, ss1))),
                     ACExpr (CImmExpr (ImmNum (3L, ss1))),
                     ss1 ) ),
              ss1 ) ) );
    tae "atagCApp"
      (AProgram
         ( ACExpr
             (CApp
                ( ImmNum (1L, (4, ss1)),
                  [ImmNum (2L, (2, ss1)); ImmNum (3L, (3, ss1))],
                  Snake,
                  (1, ss1) ) ),
           (0, ss1) ) )
      (atag
         (AProgram
            (ACExpr (CApp (ImmNum (1L, ss1), [ImmNum (2L, ss1); ImmNum (3L, ss1)], Snake, ss1)), ss1)
         ) );
    tae "atagCTuple"
      (AProgram
         ( ACExpr
             (CTuple
                ([ImmNum (1L, (2, ss1)); ImmNum (2L, (3, ss1)); ImmNum (3L, (4, ss1))], (1, ss1)) ),
           (0, ss1) ) )
      (atag
         (AProgram
            (ACExpr (CTuple ([ImmNum (1L, ss1); ImmNum (2L, ss1); ImmNum (3L, ss1)], ss1)), ss1) ) );
    tae "atagCGetItem"
      (AProgram
         (ACExpr (CGetItem (ImmNum (1L, (3, ss1)), ImmNum (2L, (2, ss1)), (1, ss1))), (0, ss1)) )
      (atag (AProgram (ACExpr (CGetItem (ImmNum (1L, ss1), ImmNum (2L, ss1), ss1)), ss1)));
    tae "atagCSetItem"
      (AProgram
         ( ACExpr
             (CSetItem
                (ImmNum (1L, (4, ss1)), ImmNum (2L, (3, ss1)), ImmNum (3L, (2, ss1)), (1, ss1)) ),
           (0, ss1) ) )
      (atag
         (AProgram
            (ACExpr (CSetItem (ImmNum (1L, ss1), ImmNum (2L, ss1), ImmNum (3L, ss1), ss1)), ss1) ) );
    tae "atagCLambda"
      (AProgram
         (ACExpr (CLambda (["x"], ACExpr (CImmExpr (ImmNum (1L, (2, ss1)))), (1, ss1))), (0, ss1))
      )
      (atag (AProgram (ACExpr (CLambda (["x"], ACExpr (CImmExpr (ImmNum (1L, ss1))), ss1)), ss1)));
    tae "atagCTryCatch"
      (AProgram
         ( ACExpr (CTryCatch (ImmNum (1L, (3, ss1)), Runtime, ImmNum (2L, (2, ss1)), (1, ss1))),
           (0, ss1) ) )
      (atag (AProgram (ACExpr (CTryCatch (ImmNum (1L, ss1), Runtime, ImmNum (2L, ss1), ss1)), ss1)));
    tae "atagCCheck"
      (AProgram
         ( ACExpr
             (CCheck
                ([ImmNum (1L, (2, ss1)); ImmNum (2L, (3, ss1)); ImmNum (3L, (4, ss1))], (1, ss1)) ),
           (0, ss1) ) )
      (atag
         (AProgram
            (ACExpr (CCheck ([ImmNum (1L, ss1); ImmNum (2L, ss1); ImmNum (3L, ss1)], ss1)), ss1) ) );
    tae "atagCTestOp1"
      (AProgram
         (ACExpr (CTestOp1 (ImmNum (1L, (3, ss1)), ImmNum (2L, (2, ss1)), true, (1, ss1))), (0, ss1))
      )
      (atag (AProgram (ACExpr (CTestOp1 (ImmNum (1L, ss1), ImmNum (2L, ss1), true, ss1)), ss1)));
    tae "atagCTestOp2"
      (AProgram
         ( ACExpr (CTestOp2 (ImmNum (1L, (3, ss1)), ImmNum (2L, (2, ss1)), Pred, false, (1, ss1))),
           (0, ss1) ) )
      (atag
         (AProgram (ACExpr (CTestOp2 (ImmNum (1L, ss1), ImmNum (2L, ss1), Pred, false, ss1)), ss1)) );
    tae "atagCTestOp2Pred"
      (AProgram
         ( ACExpr
             (CTestOp2Pred
                (ImmNum (1L, (4, ss1)), ImmNum (2L, (3, ss1)), ImmNum (3L, (2, ss1)), true, (1, ss1))
             ),
           (0, ss1) ) )
      (atag
         (AProgram
            ( ACExpr (CTestOp2Pred (ImmNum (1L, ss1), ImmNum (2L, ss1), ImmNum (3L, ss1), true, ss1)),
              ss1 ) ) );
    tae "atagASeq"
      (AProgram
         ( ASeq
             (CImmExpr (ImmNum (1L, (3, ss1))), ACExpr (CImmExpr (ImmNum (2L, (2, ss1)))), (1, ss1)),
           (0, ss1) ) )
      (atag
         (AProgram
            (ASeq (CImmExpr (ImmNum (1L, ss1)), ACExpr (CImmExpr (ImmNum (2L, ss1))), ss1), ss1) ) );
    tae "atagALet"
      (AProgram
         ( ALet
             ( "x",
               CImmExpr (ImmNum (1L, (3, ss1))),
               ACExpr (CImmExpr (ImmNum (2L, (2, ss1)))),
               (1, ss1) ),
           (0, ss1) ) )
      (atag
         (AProgram
            (ALet ("x", CImmExpr (ImmNum (1L, ss1)), ACExpr (CImmExpr (ImmNum (2L, ss1))), ss1), ss1)
         ) );
    tae "atagALetRec"
      (AProgram
         ( ALetRec
             ( [("f", CImmExpr (ImmNum (1L, (3, ss1)))); ("g", CImmExpr (ImmNum (2L, (4, ss1))))],
               ACExpr (CImmExpr (ImmNum (3L, (2, ss1)))),
               (1, ss1) ),
           (0, ss1) ) )
      (atag
         (AProgram
            ( ALetRec
                ( [("f", CImmExpr (ImmNum (1L, ss1))); ("g", CImmExpr (ImmNum (2L, ss1)))],
                  ACExpr (CImmExpr (ImmNum (3L, ss1))),
                  ss1 ),
              ss1 ) ) ) ]
;;

module Suite : TestSuite = struct
  let suite = test_suite
end
