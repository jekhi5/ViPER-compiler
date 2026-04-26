open Unix
open Filename
open Compile
open Printf
open OUnit2
open ExtLib
open Sexp

let result_printer (e : (string, string) result) : string =
  match e with
  | Error v -> sprintf "Error: %s\n" v
  | Ok v -> v
;;

(* Read a file into a string *)
let string_of_file (file_name : string) : string =
  let inchan = open_in file_name in
  let ans = really_input_string inchan (in_channel_length inchan) in
  close_in inchan; ans
;;

let parse_string (s : string) : pos expr = Compile.expr_of_sexp (Sexp.parse s)

let compile_string_to_string (s : string) : string =
  let input_program = parse_string s in
  compile_to_string input_program
;;

let compile_file_to_string (input_file : string) : string =
  compile_string_to_string (string_of_file input_file)
;;

type tempfiles =
  Unix.file_descr
  * string (* stdout file and name *)
  * Unix.file_descr
  * string (* stderr file and name *)
  * Unix.file_descr (* stdin file *)

let make_tmpfiles (name : string) (std_input : string) : tempfiles =
  let stdin_read, stdin_write = pipe () in
  let stdout_name = temp_file ("stdout_" ^ name) ".out" in
  let stderr_name = temp_file ("stderr_" ^ name) ".err" in
  ignore (Unix.write_substring stdin_write std_input 0 (String.length std_input));
  Unix.close stdin_write;
  ( openfile stdout_name [O_RDWR] 0o600,
    stdout_name,
    openfile stderr_name [O_RDWR] 0o600,
    stderr_name,
    stdin_read )
;;

let run_no_vg (program_name : string) args std_input : (string, string) result =
  let rstdout, rstdout_name, rstderr, rstderr_name, rstdin = make_tmpfiles "run" std_input in
  let ran_pid =
    Unix.create_process (program_name ^ ".run")
      (Array.of_list ([program_name ^ ".run"] @ args))
      rstdin rstdout rstderr
  in
  let _, status = waitpid [] ran_pid in
  let result =
    match status with
    | WEXITED 0 -> Ok (string_of_file rstdout_name)
    | WEXITED n -> Error (sprintf "Error %d: %s" n (string_of_file rstderr_name))
    | WSIGNALED n -> Error (sprintf "Signalled with %d while running %s." n program_name)
    | WSTOPPED n -> Error (sprintf "Stopped with signal %d while running %s." n program_name)
  in
  List.iter close [rstdout; rstderr; rstdin];
  List.iter unlink [rstdout_name; rstderr_name];
  result
;;

let run_asm
    (asm_string : string)
    (out : string)
    (runner : string -> string list -> string -> (string, string) result)
    args
    (std_input : string) =
  let outfile = open_out (out ^ ".s") in
  fprintf outfile "%s" asm_string;
  close_out outfile;
  let bstdout, bstdout_name, bstderr, bstderr_name, bstdin = make_tmpfiles "build" "" in
  let built_pid =
    Unix.create_process "make" (Array.of_list ["make"; out ^ ".run"]) bstdin bstdout bstderr
  in
  let _, status = waitpid [] built_pid in
  let try_running =
    match status with
    | WEXITED 0 -> Ok (string_of_file bstdout_name)
    | WEXITED _ ->
        Error
          (sprintf "Finished with error while building %s:\nStderr:\n%s\nStdout:\n%s" out
             (string_of_file bstderr_name) (string_of_file bstdout_name) )
    | WSIGNALED n -> Error (sprintf "Signalled with %d while building %s." n out)
    | WSTOPPED n -> Error (sprintf "Stopped with signal %d while building %s." n out)
  in
  let result =
    match try_running with
    | Error _ -> try_running
    | Ok _ -> runner out args std_input
  in
  List.iter close [bstdout; bstderr; bstdin];
  List.iter unlink [bstdout_name; bstderr_name];
  result
;;

let run p out runner args std_input =
  let maybe_asm_string = try Ok (compile_to_string p) with err -> Error err in
  match maybe_asm_string with
  | Error err -> Error (Printexc.to_string err)
  | Ok asm_string -> run_asm asm_string out runner args std_input
;;

let test_run (program_str : string) (outfile : string) (expected : string) (_ : OUnit2.test_ctxt) :
    unit =
  let full_outfile = "output/" ^ outfile in
  let program = parse_string program_str in
  let result = run program full_outfile run_no_vg [] "" in
  assert_equal (Ok (expected ^ "\n")) result ~printer:result_printer
;;

let test_err (program_str : string) (outfile : string) (errmsg : string) (_ : OUnit2.test_ctxt) :
    unit =
  let result =
    try
      let full_outfile = "output/" ^ outfile in
      let program = parse_string program_str in
      run program full_outfile run_no_vg [] ""
    with
    | Failure s -> Error s
    | err -> Error (Printexc.to_string err)
  in
  assert_equal (Error errmsg) result ~printer:result_printer ~cmp:(fun check result ->
      match (check, result) with
      | Error expect_msg, Error actual_message -> String.exists actual_message ~sub:expect_msg
      | _ -> false )
;;

let test_run_input filename expected test_ctxt =
  test_run (string_of_file ("input/" ^ filename)) filename expected test_ctxt
;;

let test_err_input filename expected test_ctxt =
  test_err (string_of_file ("input/" ^ filename)) filename expected test_ctxt
;;
