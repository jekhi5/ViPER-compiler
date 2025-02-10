open Printf
open Exprs
open Pretty

(* TODO: Define any additional exceptions you want *)
exception ParseError of string (* parse-error message *)

exception UnboundId of string * sourcespan (* name, where used *)

exception UnboundFun of string * sourcespan (* name of fun, where used *)

exception DuplicateId of string * sourcespan * sourcespan (* name, where used, where defined *)

exception DuplicateFun of string * sourcespan * sourcespan (* name, where used, where defined *)

exception Overflow of int64 * sourcespan (* value, where used *)

exception Arity of int * int * sourcespan (* intended arity, actual arity, where called *)

exception NotYetImplemented of string (* TODO: Message to show *)

exception InternalCompilerError of string (* Major failure: message to show *)

let known_compiletime_exn exn =
  match exn with
  | ParseError _
   |NotYetImplemented _
   |InternalCompilerError _
   |UnboundId _
   |UnboundFun _
   |DuplicateId _
   |DuplicateFun _
   |Overflow _
   |Arity _ -> true
  | _ -> false
;;

let print_error exn =
  match exn with
  | ParseError msg -> msg
  | NotYetImplemented msg -> "Not yet implemented: " ^ msg
  | InternalCompilerError msg -> "Internal Compiler Error: " ^ msg
  | UnboundId (x, loc) ->
      sprintf "The identifier %s, used at <%s>, is not in scope" x (string_of_sourcespan loc)
  | UnboundFun (x, loc) ->
      sprintf "The function name %s, used at <%s>, is not in scope" x (string_of_sourcespan loc)
  | DuplicateId (x, loc, existing) ->
      sprintf "The identifier %s, redefined at <%s>, duplicates one at <%s>" x
        (string_of_sourcespan loc) (string_of_sourcespan existing)
  | DuplicateFun (x, loc, existing) ->
      sprintf "The function name %s, redefined at <%s>, duplicates one at <%s>" x
        (string_of_sourcespan loc) (string_of_sourcespan existing)
  | Overflow (num, loc) ->
      sprintf "The number literal %Ld, used at <%s>, is not supported in this language" num
        (string_of_sourcespan loc)
  | Arity (expected, actual, loc) ->
      sprintf "The function called at <%s> expected an arity of %d, but received %d arguments"
        (string_of_sourcespan loc) expected actual
  | _ -> sprintf "%s" (Printexc.to_string exn)
;;

(* Stringifies a list of compilation errors *)
let print_errors (exns : exn list) : string list = List.map print_error exns
