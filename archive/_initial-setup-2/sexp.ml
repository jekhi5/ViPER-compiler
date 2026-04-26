open Str
open List

type 'a tok =
  | LPAREN of 'a
  | RPAREN of 'a
  | TSym of string * 'a
  | TInt of int * 'a
  | TBool of bool * 'a

let tok_info t =
  match t with
  | LPAREN x -> x
  | RPAREN x -> x
  | TSym (_, x) -> x
  | TInt (_, x) -> x
  | TBool (_, x) -> x
;;

(* startline, startcol, endline, endcol *)
type pos = int * int * int * int

let pos_to_string (startline, startcol, endline, endcol) range =
  if range then
    Printf.sprintf "line %d, col %d--line %d, col %d" startline startcol endline endcol
  else
    Printf.sprintf "line %d, col %d" startline startcol
;;

(*

This function appears to move through a string by character identifying tokens and 
storing their location in the code in the form of a line and column number, 
which are ultimately "returned" as a list. The function uses List.fold_left as it
is important to accumulate the tokens starting from the left, not only because that's 
the order we see the inputs, but also because it's same direction the positions are 
being counted from. The code correctly identifies what kind of delimiter or text is present and 
stores the location of that token while also checking to see if it's a valid form of text 
(if it is actually text). As this happens, the current line and column numbers are updated in 
logical ways (IE: when there is a parenthesis character, the column increments by one, but when
there is a newline character the line is incremented by one and the column count is reset).
The text appears to only have booleans and numbers as acceptable text in the language. 
The function checks if it's a valid boolean, and if not then it is hopefully a number. 
The try/with ensures this by trying to convert the non-boolean text to a number, and raises 
an exception with a (hopefully) useful error message including the location if it fails. 
The call to `regexp` is in the argument for the list being passed into the fold. This call 
probably splits the input string by the delimiters: `(`, `)`, `\n`, `\t`, ` `, and the resulting list 
is passed into the fold. Finally, since the fold_left is going to create a list with the 
tokens in the opposite order, the final call reverses the order of the list so that the 
parser can move through the tokens in the proper order.
*)

let tokenize (str : string) : pos tok list =
  let toks, _, _ =
    List.fold_left
      (fun ((toks : pos tok list), (line : int), (col : int)) (tok : Str.split_result) ->
        match tok with
        | Delim t ->
            if t = " " then
              (toks, line, col + 1)
            else if t = "\t" then
              (toks, line, col + 1)
            else if t = "\n" then
              (toks, line + 1, 0)
            else if t = "(" then
              (LPAREN (line, col, line, col + 1) :: toks, line, col + 1)
            else if t = ")" then
              (RPAREN (line, col, line, col + 1) :: toks, line, col + 1)
            else
              let tLen = String.length t in
              (TSym (t, (line, col, line, col + tLen)) :: toks, line, col + tLen)
        | Text t -> (
            if t = "true" then
              (TBool (true, (line, col, line, col + 4)) :: toks, line, col + 4)
            else if t = "false" then
              (TBool (false, (line, col, line, col + 5)) :: toks, line, col + 5)
            else
              let tLen = String.length t in
              try (TInt (int_of_string t, (line, col, line, col + tLen)) :: toks, line, col + tLen)
              with Failure _ -> (TSym (t, (line, col, line, col + tLen)) :: toks, line, col + tLen)
            ) )
      ([], 0, 0)
      (full_split (regexp "[()\n\t ]") str)
  in
  List.rev toks
;;

type 'a sexp =
  | Sym of string * 'a
  | Int of int * 'a
  | Bool of bool * 'a
  | Nest of 'a sexp list * 'a

let sexp_info s =
  match s with
  | Sym (_, x) -> x
  | Int (_, x) -> x
  | Bool (_, x) -> x
  | Nest (_, x) -> x
;;

let parse_toks (toks : pos tok list) : (pos sexp list, string) result =
  let rec parse_toks_helper (toks : pos tok list) (paren_stack : pos list) (acc : pos sexp list) :
      (pos sexp list, string) result =
    match toks with
    | [] ->
        if is_empty paren_stack then
          Ok acc
        else
          Error ("Unmatched left paren at " ^ pos_to_string (List.hd paren_stack) false)
    | cur_tok :: rest -> (
      match cur_tok with
      | TSym (sym, pos) -> parse_toks_helper rest paren_stack (Sym (sym, pos) :: acc)
      | TInt (int, pos) -> parse_toks_helper rest paren_stack (Int (int, pos) :: acc)
      | TBool (bool, pos) -> parse_toks_helper rest paren_stack (Bool (bool, pos) :: acc)
      | LPAREN pos -> (
        match parse_toks_helper rest (pos :: paren_stack) acc with
        | Ok x -> Ok x
        | Error msg -> Error msg )
      | RPAREN pos ->
          if not (is_empty paren_stack) then
            parse_toks_helper rest (tl paren_stack) acc
          else
            Error ("Illegal closing paren at " ^ pos_to_string pos false) )
  in
  try parse_toks_helper toks [] []
  with e ->
    let message = Printexc.to_string e in
    Error message
;;

let parse str = parse_toks (tokenize str)
