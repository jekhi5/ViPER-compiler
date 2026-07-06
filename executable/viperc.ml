open Sys
open Unix
open Filename
open Runner
open Register_alloc
open Printf
open Config
open Exprs

(*
  Interface for compiling Viper programs from the command line.
*)

let halt_after_compile = ref false

let halt_after_assemble = ref false

let halt_after_build = ref false

let keep_intermediate_files = ref false

let filename_set = ref false

let filename : string ref = ref ""

let output : string ref = ref ""

let show_trace = ref false

let no_builtins = ref false

let alloc_strat = ref Naive

let verbose = ref false

let set_strategy s =
  match s with
  | "naive" -> alloc_strat := Naive
  | "register" -> alloc_strat := Register
  | _ ->
      raise
        (Arg.Bad (sprintf "'%s' is not an allocation strategy, use either 'naive' or 'register'" s))
;;

let filename_handler (name : string) : unit =
  (* Revisit here when adding the ability to compile multiple viper files. *)
  if !filename_set then
    raise (Arg.Bad "Cannot compile more than one file name")
  else (
    filename_set := true;
    filename := name
  )
;;

(** Returns the output directory and file basename, based on the provided options. * If no output
    was provided, use the same directory and basename as the input file. * If the provided output is
    a directory, use the same basename as the input file. * If the provided output is a file, use
    its dirname and basename. *)
let output_name () : string * string =
  match !output with
  | "" -> (dirname !filename, remove_extension (basename !filename))
  | output_name ->
      let bare_name = remove_extension output_name in
      if String.equal bare_name output_name then
        (output_name, remove_extension (basename !filename))
      else
        (dirname output_name, basename bare_name)
;;

(** A generalized process for a step in building a viper program. Arguments:
    - [label]: the name of the phase, for error messages.
    - [process_name]: the name of the process in which this phase will run.
    - [command]: the command to execute to run this phase.
    - [out]: The output filename for this phase, WITHOUT the file extension.
    - [std_input]: The contents of std_in for this step. Usually empty. *)
let run_build_phase
    (label : string)
    (process_name : string)
    (command : string list)
    (out : string)
    (std_input : string) : (string, string) result =
  let stdout, stdout_name, stderr, stderr_name, stdin = make_tmpfiles "link" std_input in
  let pid = Unix.create_process process_name (Array.of_list command) stdin stdout stderr in
  Fun.protect
    ~finally:(fun () ->
      List.iter close [stdout; stderr; stdin];
      List.iter unlink [stdout_name; stderr_name] )
    (fun () ->
      let _, link_status = waitpid [] pid in
      match link_status with
      | WEXITED 0 -> Ok (string_of_file stdout_name)
      | WEXITED _ ->
          Error
            (sprintf "Finished with error during %s phase for %s:\nStderr:\n%s\nStdout:\n%s" label
               out (string_of_file stderr_name) (string_of_file stdout_name) )
      | WSIGNALED n -> Error (sprintf "Signalled with %d during %s phase for %s." n label out)
      | WSTOPPED n -> Error (sprintf "Stopped with signal %d during %s phase for %s." n label out) )
;;

let run_assemble (out : string) (std_input : string) : (string, string) result =
  run_build_phase "assembly" "nasm"
    ["nasm"; "-f"; nasm_format; "-o"; out ^ ".o"; out ^ ".s"]
    out std_input
;;

let run_build (out : string) (std_input : string) : (string, string) result =
  run_build_phase "build" "clang"
    ( ["clang"]
    @ String.split_on_char ' ' clang_flags
    @ ["-o"; out ^ ".run"; runtime_dir ^ "/main.c"; runtime_dir ^ "/gc.c"; out ^ ".o"] )
    out std_input
;;

let run_viper (out : string) (std_input : string) : (string, string) result =
  run_build_phase "execution" (out ^ ".run") [Filename.concat "." (out ^ ".run")] out std_input
;;

let cleanup (out : string) : unit =
  let files_to_remove =
    if !keep_intermediate_files || !halt_after_compile then
      []
    else if !halt_after_assemble then
      [out ^ ".s"]
    else if !halt_after_build then
      [out ^ ".s"; out ^ ".o"]
    else
      [out ^ ".s"; out ^ ".o"; out ^ ".run"]
  in
  List.iter unlink files_to_remove
;;

let get_phases () : (string -> string -> (string, string) result) list =
  if !halt_after_compile then
    []
  else if !halt_after_assemble then
    [run_assemble]
  else if !halt_after_build then
    [run_assemble; run_build]
  else
    [run_assemble; run_build; run_viper]
;;

let sep = "\n=================\n"

let run_phases (out : string) (std_input : string) : (string, string) result =
  if !halt_after_compile then
    Ok (sprintf "Successfully compiled %s." out)
  else
    match run_assemble out "" with
    | Error _ as err -> err
    | Ok assemble_msg as ok -> (
        if !verbose && not !halt_after_assemble then
          printf "%s" assemble_msg
        else
          ();
        if !halt_after_assemble then
          ok
        else
          match run_build out "" with
          | Error _ as err -> err
          | Ok build_msg as ok ->
              if !verbose && not !halt_after_build then
                printf "%s" build_msg
              else
                ();
              if !halt_after_build then
                ok
              else
                run_viper out std_input )
;;

let compile_viper (std_input : string) : unit =
  let out_dirname, out_filename = output_name () in
  let out = Filename.concat out_dirname out_filename in
  let maybe_asm_string =
    compile_file_to_string ~no_builtins:!no_builtins !alloc_strat !filename !filename
  in
  match maybe_asm_string with
  | Error (errs, trace) ->
      if !show_trace then
        eprintf "%s%s" (ExtString.String.join sep (Phases.print_trace trace)) sep
      else
        ();
      printf "%s" (ExtString.String.join "\n" (Errors.print_errors errs))
  | Ok (asm_string, trace) ->
      if !show_trace then
        eprintf "%s%s" (ExtString.String.join sep (Phases.print_trace trace)) sep
      else
        ();
      Fun.protect
        ~finally:(fun () -> cleanup out)
        (fun () ->
          let asm_file = openfile (out ^ ".s") [O_WRONLY; O_CREAT] 0o640 in
          ignore (write_substring asm_file asm_string 0 (String.length asm_string));
          close asm_file;
          match run_phases out "" with
          | Ok msg | Error msg -> printf "%s" msg )
;;

let validate_args () =
  if
    1
    < List.length
        (List.filter (fun x -> x) [!halt_after_compile; !halt_after_assemble; !halt_after_build])
  then
    raise (Arg.Bad "The -c, -a, and -b flags are mutually exclusive!")
  else
    ()
;;

let () =
  let speclist =
    [ ( "-c",
        Arg.Set halt_after_compile,
        "Halt immediately after compilation, leaving behind the assembly file." );
      ( "-a",
        Arg.Set halt_after_assemble,
        "Halt immediately after assembly, leaving behind the object file." );
      ( "-b",
        Arg.Set halt_after_build,
        "Halt immediately after building, leaving behind the binary file." );
      ("--keep-files", Arg.Set keep_intermediate_files, "Keep all output files.");
      ( "-o",
        Arg.Set_string output,
        "Output file name. If -k is also set, -o ./dir/file will result in intermediate files \
         being saved to ./dir/." );
      ("-t", Arg.Set show_trace, "Display the trace of compilation");
      ("-no-builtins", Arg.Set no_builtins, "Leave out all built-in functions");
      ("-d", Arg.Set show_debug_print, "Enable debug printing");
      ("-alloc", Arg.String set_strategy, "Use register stack allocation");
      ("-v", Arg.Set verbose, "Print output of assembling and linking to stdout.") ]
  in
  Arg.parse speclist filename_handler "viperc usage:";
  validate_args ();
  compile_viper ""
;;
