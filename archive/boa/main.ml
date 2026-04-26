open Runner
open Printf

let () =
  let file_name = Sys.argv.(1) in
  let program = compile_file_to_string file_name file_name in
  printf "%s\n" program
;;
