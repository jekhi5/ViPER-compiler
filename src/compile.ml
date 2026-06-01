open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
open Graph

(* Re-export extracted modules so that callers (runner.ml, test.ml) that
   `open Compile` continue to see every name. Keep these in dependency order. *)
include Util
include Constants
include Env
include Well_formed
include Desugar
include Rename
include Anf
include Free_vars
include Naive_alloc
include Liveness
include Register_alloc
open Codegen (* to call `compile_prog` *)

(* This function can be used to take the native functions and produce DFuns whose bodies
   simply contain an EApp (with a Native call_type) to that native function.  Then,
   your existing compilation can turn these DFuns into ELambdas, which can then be called
   as in the rest of Fer-De-Lance, but the Native EApps will do the work of actually
   native_calling the runtime-provided functions. *)
let add_native_lambdas (p : sourcespan program) =
  let wrap_native name arity =
    let argnames = List.init arity (fun i -> sprintf "%s_arg_%d" name i) in
    [ DFun
        ( name,
          List.map (fun name -> BName (name, false, dummy_span)) argnames,
          EApp
            ( EId (name, dummy_span),
              List.map (fun name -> EId (name, dummy_span)) argnames,
              Native,
              dummy_span ),
          dummy_span ) ]
  in
  match p with
  | Program (declss, body, checks, tag) ->
      Program
        ( StringMap.fold
            (fun name (_, arity, _) declss ->
              match arity with
              | Some a -> wrap_native name a :: declss
              | _ -> raise (InternalCompilerError "All native functions require arity") )
            native_fun_bindings declss,
          body,
          checks,
          tag )
;;

let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

let pick_alloc_strategy (strat : alloc_strategy) =
  match strat with
  | Naive -> naive_stack_allocation
  | Register -> register_allocation
;;

let compile_to_string
    ?(no_builtins = false)
    (alloc_strat : alloc_strategy)
    (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> add_err_phase well_formed is_well_formed
  |> run_if (not no_builtins) (add_phase add_natives add_native_lambdas)
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase locate_bindings (pick_alloc_strategy alloc_strat)
  |> add_phase result compile_prog
;;
