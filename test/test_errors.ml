open Test_funcs
open Errors
open Exprs
open Printf
open OUnit2

(* Tests for the error functions for ViPER *)

let make_pos fname lnum bol cnum =
  {Lexing.pos_fname= fname; pos_lnum= lnum; pos_bol= bol; pos_cnum= cnum}
;;

let span1 = (make_pos "test" 1 0 5, make_pos "test" 1 0 10)

(* sprintf "%s, %d:%d-%d:%d" "test" 1 5 1 10 *)
let ss1 = "test, 1:5-1:10"

let span2 = (make_pos "src" 3 20 25, make_pos "src" 3 20 30)

(* sprintf "%s, %d:%d-%d:%d" "src" 3 5 3 10 *)
let ss2 = "src, 3:5-3:10"

let test_suite =
  [ (* known_compiletime_exn: all listed variants return true *)
    tae "knownParseError" true (known_compiletime_exn (ParseError "msg"));
    tae "knownNotYetImplemented" true (known_compiletime_exn (NotYetImplemented "msg"));
    tae "knownInternalCompilerError" true (known_compiletime_exn (InternalCompilerError "msg"));
    tae "knownUnboundId" true (known_compiletime_exn (UnboundId ("x", span1)));
    tae "knownUnboundFun" true (known_compiletime_exn (UnboundFun ("f", span1)));
    tae "knownShadowId" true (known_compiletime_exn (ShadowId ("x", span1, span2)));
    tae "knownDuplicateId" true (known_compiletime_exn (DuplicateId ("x", span1, span2)));
    tae "knownDuplicateFun" true (known_compiletime_exn (DuplicateFun ("f", span1, span2)));
    tae "knownOverflow" true (known_compiletime_exn (Overflow (4611686018427387904L, span1)));
    tae "knownDeclArity" true (known_compiletime_exn (DeclArity ("f", 2, 1, span1)));
    tae "knownShouldBeFunction" true (known_compiletime_exn (ShouldBeFunction ("g", span1)));
    tae "knownLetRecNonFunction" true
      (known_compiletime_exn (LetRecNonFunction (BBlank span1, span1)));
    tae "knownUnsupported" true (known_compiletime_exn (Unsupported ("op", span1)));
    tae "knownArity" true (known_compiletime_exn (Arity (2, 3, span1)));
    (* known_compiletime_exn: unknown exceptions return false *)
    tae "knownUnknownNotFound" false (known_compiletime_exn Not_found);
    tae "knownUnknownExit" false (known_compiletime_exn Exit);
    (* print_error: ParseError returns the message verbatim *)
    tae "printParseError" "parse failed" (print_error (ParseError "parse failed"));
    (* print_error: NotYetImplemented prefixes "Not yet implemented: " *)
    tae "printNotYetImplemented" "Not yet implemented: feature X"
      (print_error (NotYetImplemented "feature X"));
    (* print_error: InternalCompilerError prefixes "Internal Compiler Error: " *)
    tae "printInternalCompilerError" "Internal Compiler Error: bad state"
      (print_error (InternalCompilerError "bad state"));
    (* print_error: Unsupported includes message and location *)
    tae "printUnsupported"
      (sprintf "Unsupported: op at <%s>" ss1)
      (print_error (Unsupported ("op", span1)));
    (* print_error: UnboundId includes identifier name and location *)
    tae "printUnboundId"
      (sprintf "The identifier x, used at <%s>, is not in scope" ss1)
      (print_error (UnboundId ("x", span1)));
    (* print_error: UnboundFun includes function name and location *)
    tae "printUnboundFun"
      (sprintf "The function name f, used at <%s>, is not in scope" ss1)
      (print_error (UnboundFun ("f", span1)));
    (* print_error: ShadowId includes name, use site, and definition site *)
    tae "printShadowId"
      (sprintf "The identifier x, defined at <%s>, shadows one defined at <%s>" ss1 ss2)
      (print_error (ShadowId ("x", span1, span2)));
    (* print_error: DuplicateId includes name, redef site, and original site *)
    tae "printDuplicateId"
      (sprintf "The identifier x, redefined at <%s>, duplicates one at <%s>" ss1 ss2)
      (print_error (DuplicateId ("x", span1, span2)));
    (* print_error: DuplicateFun includes name, redef site, and original site *)
    tae "printDuplicateFun"
      (sprintf "The function name f, redefined at <%s>, duplicates one at <%s>" ss1 ss2)
      (print_error (DuplicateFun ("f", span1, span2)));
    (* print_error: Overflow includes the literal value and location *)
    tae "printOverflow"
      (sprintf "The number literal %Ld, used at <%s>, is not supported in this language"
         4611686018427387904L ss1 )
      (print_error (Overflow (4611686018427387904L, span1)));
    (* print_error: Arity includes location, expected, and actual counts *)
    tae "printArity"
      (sprintf "The function called at <%s> expected an arity of 2, but received 3 arguments" ss1)
      (print_error (Arity (2, 3, span1)));
    (* print_error: DeclArity includes function name, location, arg count, and type count *)
    tae "printDeclArity"
      (sprintf "The function f, defined at %s, has 3 arguments but only 2 types provided" ss1)
      (print_error (DeclArity ("f", 3, 2, span1)));
    (* print_error: ShouldBeFunction includes function name and location *)
    tae "printShouldBeFunction"
      (sprintf "The function g, at %s, should be function" ss1)
      (print_error (ShouldBeFunction ("g", span1)));
    (* print_error: LetRecNonFunction with BBlank bind *)
    tae "printLetRecNonFunctionBBlank"
      (sprintf "Binding error at %s: Let-rec expected a name binding to a lambda; got _" ss1)
      (print_error (LetRecNonFunction (BBlank span1, span1)));
    (* print_error: LetRecNonFunction with BName bind *)
    tae "printLetRecNonFunctionBName"
      (sprintf "Binding error at %s: Let-rec expected a name binding to a lambda; got x" ss1)
      (print_error (LetRecNonFunction (BName ("x", false, span1), span1)));
    (* print_error: LetRecNonFunction with BTuple bind *)
    tae "printLetRecNonFunctionBTuple"
      (sprintf "Binding error at %s: Let-rec expected a name binding to a lambda; got (a, b)" ss1)
      (print_error
         (LetRecNonFunction
            (BTuple ([BName ("a", false, span1); BName ("b", false, span1)], span1), span1) ) );
    (* print_error: unknown exception falls through to Printexc.to_string *)
    tae "printUnknownExn" "Not_found" (print_error Not_found);
    (* print_errors: maps print_error over an exception list *)
    tae "printErrorsEmpty" [] (print_errors []);
    tae "printErrorsSingleton" ["parse failed"] (print_errors [ParseError "parse failed"]);
    tae "printErrorsMultiple"
      ["Internal Compiler Error: bad"; "Not yet implemented: foo"]
      (print_errors [InternalCompilerError "bad"; NotYetImplemented "foo"]) ]
;;

module Suite : TestSuite = struct
  let suite = test_suite
end
