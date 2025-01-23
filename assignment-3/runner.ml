open Unix
open Filename
open Compile
open Printf
open OUnit2
open ExtLib
open Lexing
open Exprs

let result_printer (e : (string, string) result) : string =
  match e with
  | Error v -> sprintf "Error: %s\n" v
  | Ok v -> v
;;

exception ParseError of string (* parse-error message *)

let string_of_position (p : Lexing.position) : string =
  sprintf "%s:line %d, col %d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol)
;;

let parse (name : string) lexbuf : (Lexing.position * Lexing.position) expr =
  try
    lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname= name};
    Parser.program Lexer.token lexbuf
  with
  | Failure msg as exn ->
      if msg = "lexing: empty token" then
        raise (ParseError (sprintf "Lexical error at %s" (string_of_position lexbuf.lex_curr_p)))
      else
        let bt = Printexc.get_raw_backtrace () in
        Printexc.raise_with_backtrace exn bt (* make sure we throw with the same stack trace *)
  | Parsing.Parse_error ->
      let curr = lexbuf.Lexing.lex_curr_p in
      let line = curr.Lexing.pos_lnum in
      let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      let tok = Lexing.lexeme lexbuf in
      raise (ParseError (sprintf "Parse error at line %d, col %d: token `%s`" line cnum tok))
;;

(* Read a file into a string *)
let string_of_file (file_name : string) : string =
  let inchan = open_in file_name in
  let ans = really_input_string inchan (in_channel_length inchan) in
  close_in inchan; ans
;;

let parse_string (name : string) (s : string) : (Lexing.position * Lexing.position) expr =
  let lexbuf = Lexing.from_string s in
  parse name lexbuf
;;

let parse_file (name : string) input_file : (Lexing.position * Lexing.position) expr =
  let lexbuf = Lexing.from_channel input_file in
  parse name lexbuf
;;

let compile_string_to_string (name : string) (input : string) : string =
  compile_to_string (parse_string name input)
;;

let compile_file_to_string (name : string) (input_file : string) : string =
  compile_string_to_string name (string_of_file input_file)
;;

let make_tmpfiles (name : string) (std_input : string) =
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

let run_vg (program_name : string) args std_input : (string, string) result =
  let rstdout, rstdout_name, rstderr, rstderr_name, rstdin = make_tmpfiles "run" std_input in
  let ran_pid =
    Unix.create_process "valgrind"
      (Array.of_list (["valgrind"; program_name ^ ".run"] @ args))
      rstdin rstdout rstderr
  in
  let _, status = waitpid [] ran_pid in
  let vg_str = string_of_file rstderr_name in
  let vg_ok = String.exists vg_str ~sub:"0 errors from 0 contexts" in
  let result =
    match (status, vg_ok) with
    | WEXITED 0, true -> Ok (string_of_file rstdout_name)
    | WEXITED 0, false ->
        Error ("Stdout: " ^ string_of_file rstdout_name ^ "\n" ^ "Valgrind: \n" ^ vg_str)
    | WEXITED n, _ -> Error (sprintf "Error %d: %s" n vg_str)
    | WSIGNALED n, _ -> Error (sprintf "Signalled with %d while running %s." n program_name)
    | WSTOPPED n, _ -> Error (sprintf "Stopped with signal %d while running %s." n program_name)
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
          (sprintf "Finished with error while building %s:\n%s" out (string_of_file bstderr_name))
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
  try
    let asm_string = compile_to_string p in
    run_asm asm_string out runner args std_input
  with err -> Error (Printexc.to_string err)
;;

let run_anf p out runner args std_input =
  let maybe_asm_string =
    try Ok (compile_anf_to_string p) with
    | Failure s -> Error [Failure ("Compile error: " ^ s)]
    | err -> Error [Failure ("Unexpected compile error: " ^ Printexc.to_string err)]
  in
  match maybe_asm_string with
  | Error errs -> Error (ExtString.String.join "\n" (List.map Printexc.to_string errs))
  | Ok asm_string -> run_asm asm_string out runner args std_input
;;

let test_run ?(args = []) ?(std_input = "") program_str outfile expected _test_ctxt =
  let full_outfile = "output/" ^ outfile in
  let result =
    try
      let program = parse_string outfile program_str in
      run program full_outfile run_no_vg args std_input
    with err -> Error (Printexc.to_string err)
  in
  assert_equal (Ok (expected ^ "\n")) result ~printer:result_printer
;;

let test_run_anf ?(args = []) ?(std_input = "") program_anf outfile expected _test_ctxt =
  let full_outfile = "output/" ^ outfile in
  let result = run_anf program_anf full_outfile run_no_vg args std_input in
  assert_equal (Ok (expected ^ "\n")) result ~printer:result_printer
;;

let test_run_valgrind ?(args = []) ?(std_input = "") program_str outfile expected _test_ctxt =
  let full_outfile = "output/" ^ outfile in
  let result =
    try
      let program = parse_string outfile program_str in
      run program full_outfile run_vg args std_input
    with err -> Error (Printexc.to_string err)
  in
  assert_equal (Ok (expected ^ "\n")) result ~printer:result_printer
;;

let test_err ?(args = []) ?(std_input = "") program_str outfile errmsg _test_ctxt =
  let full_outfile = "output/" ^ outfile in
  let result =
    try
      let program = parse_string outfile program_str in
      run program full_outfile run_no_vg args std_input
    with err -> Error (Printexc.to_string err)
  in
  assert_equal (Error errmsg) result ~printer:result_printer ~cmp:(fun check result ->
      match (check, result) with
      | Error expect_msg, Error actual_message -> String.exists actual_message ~sub:expect_msg
      | _ -> false )
;;

let test_run_input filename ?(args = []) expected test_ctxt =
  test_run ~args ~std_input:"" (string_of_file ("input/" ^ filename)) filename expected test_ctxt
;;

let test_err_input filename ?(args = []) expected test_ctxt =
  test_err ~args ~std_input:"" (string_of_file ("input/" ^ filename)) filename expected test_ctxt
;;
