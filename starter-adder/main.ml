open Runner
open Printf

let () =
  let name = Sys.argv.(1) in
  let program = compile_file_to_string name in
  printf "%s\n" program
;;
