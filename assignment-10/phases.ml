open Printf
open Exprs
open Errors
open Pretty
open Assembly
module StringMap = Map.Make (String)
module TagMap = Map.Make (Int)

type 'a name_envt = 'a StringMap.t

type 'a tag_envt = 'a TagMap.t

(* There are lots of ways to work with pipelines of functions that "can fail
   at any point". They all have various drawbacks, though.  See
   http://keleshev.com/composable-error-handling-in-ocaml for a decent writeup
   of some of the techniques.  Since we haven't introduced all of the OCaml
   concepts mentioned there, this file uses a variation on the ideas shown in
   that blog post. *)

(* Describes individual phases of compilation.
   Feel free to add additional constructors here, and
   add a "helper" function just afterward. *)
type phase =
  | Source of string
  | Parsed of sourcespan program
  | WellFormed of sourcespan program
  | Renamed of tag program
  | Desugared of sourcespan program
  | AddedNatives of sourcespan program
  | Tagged of tag program
  | ANFed of tag aprogram
  | Located of tag aprogram * arg name_envt name_envt
  | Result of string

(* These functions simply apply a phase constructor, because OCaml
   doesn't allow you to pass data-constructors as first-class values *)
let source s = Source s

let parsed p = Parsed p

let well_formed p = WellFormed p

let renamed p = Renamed p

let desugared p = Desugared p

let tagged p = Tagged p

let anfed p = ANFed p

let add_natives p = AddedNatives p

let locate_bindings (p, e) = Located (p, e)

let result s = Result s

(* When a stage of the compiler fails, return all the errors that occured,
   along with whatever phases of the compiler successfully completed *)
type failure = exn list * phase list

(* An individual function might fail sometimes, and either return a value
   or a bunch of errors *)
type 'a fallible = ('a, exn list) result

(* An overall pipeline returns either a final result (of type 'a) and
   a list of prior phases, or it returns a failure as above *)
type 'a pipeline = ('a * phase list, failure) result

(* Adds another phase to the growing pipeline, using a function that might fail.
   If the function returns an Error full of exns, then the pipeline dies right there.
   If the function *throws* an exception, the pipeline dies right there.
   If the function succeeds, then the pipeline grows (using log to add the result
   onto the pipeline).
   NOTE: Executing add_err_phase will never throw any exceptions.
*)
let add_err_phase (log : 'b -> phase) (next : 'a -> 'b fallible) (cur_pipeline : 'a pipeline) :
    'b pipeline =
  match cur_pipeline with
  | Error (errs, trace) -> Error (errs, trace)
  | Ok (cur_val, trace) -> (
    try
      match next cur_val with
      | Error errs -> Error (errs, trace)
      | Ok new_val -> Ok (new_val, log new_val :: trace)
    with
    | Failure s -> Error ([Failure ("Compile error: " ^ s)], trace)
    | err ->
        if known_compiletime_exn err then
          Error ([Failure (print_error err)], trace)
        else
          Error ([Failure ("Unexpected compile error: " ^ Printexc.to_string err)], trace) )
;;

(* Adds another phase to the growing pipeline, using a function that should never fail.
   If the function *throws* an exception, the pipeline dies right there.
   Otherwise, the pipeline grows (using log to add the result onto the pipeline).
   NOTE: Executing add_phase will never throw any exceptions.
*)
let add_phase (log : 'b -> phase) (next : 'a -> 'b) (cur_pipeline : 'a pipeline) : 'b pipeline =
  match cur_pipeline with
  | Error (errs, trace) -> Error (errs, trace)
  | Ok (cur_val, trace) -> (
    try
      let new_val = next cur_val in
      Ok (new_val, log new_val :: trace)
    with
    | Failure s -> Error ([Failure ("Compile error: " ^ s)], trace)
    | err ->
        if known_compiletime_exn err then
          Error ([Failure (print_error err)], trace)
        else
          Error ([Failure ("Unexpected compile error: " ^ Printexc.to_string err)], trace) )
;;

let no_op_phase (cur_pipeline : 'a pipeline) = cur_pipeline

let string_of_name_envt_envt e =
  ExtString.String.join "\n"
            (List.map
               (fun (name, env) ->
                 name
                 ^ ":\n\t"
                 ^ ExtString.String.join "\n\t"
                     (List.map (fun (name, arg) -> name ^ "=>" ^ arg_to_asm arg) (StringMap.bindings env)) )
               (StringMap.bindings e)) ^ "\n" 

(* Stringifies a list of phases, for debug printing purposes *)
let print_trace (trace : phase list) : string list =
  let phase_name p =
    match p with
    | Source _ -> "Source"
    | Parsed _ -> "Parsed"
    | WellFormed _ -> "Well-formed"
    | Renamed _ -> "Renamed"
    | Desugared _ -> "Desugared"
    | AddedNatives _ -> "Natives Added"
    | Tagged _ -> "Tagged"
    | ANFed _ -> "ANF'ed"
    | Located _ -> "Located"
    | Result _ -> "Result"
  in
  let string_of_phase p =
    match p with
    | Source s -> s
    | Parsed p | WellFormed p -> string_of_program p
    | Renamed p -> string_of_program p
    | Desugared p -> string_of_program p
    | AddedNatives p -> string_of_program p
    | Tagged p -> string_of_program_with 1000 (fun tag -> sprintf "@%d" tag) p
    | ANFed p -> string_of_aprogram_with 1000 (fun tag -> sprintf "@%d" tag) p
    | Located (p, e) ->
      string_of_aprogram_with 1000 (fun tag -> sprintf "@%d" tag) p
      ^ "\nEnvs:\n"
      ^ (string_of_name_envt_envt e)
    | Result s -> s
  in
  List.mapi
    (fun n p -> sprintf "Phase %d (%s):\n%s" n (phase_name p) (string_of_phase p))
    (List.rev trace)
;;
