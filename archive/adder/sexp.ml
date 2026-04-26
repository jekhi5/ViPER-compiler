open Str
(* open Printf *)

type 'a tok =
  | LPAREN of 'a
  | RPAREN of 'a
  | TSym of string * 'a
  | TInt of int64 * 'a
  | TBool of bool * 'a

let tok_info (t : 'a tok) : 'a =
  match t with
  | LPAREN x -> x
  | RPAREN x -> x
  | TSym (_, x) -> x
  | TInt (_, x) -> x
  | TBool (_, x) -> x
;;

(* startline, startcol, endline, endcol *)
type pos = int * int * int * int

let pos_to_string ((startline, startcol, endline, endcol) : pos) (range : bool) : string =
  if range then
    Printf.sprintf "line %d, col %d--line %d, col %d" startline startcol endline endcol
  else
    Printf.sprintf "line %d, col %d" startline startcol
;;

let tokenize (str : string) : pos tok list =
  let toks, _, _ =
    List.fold_left
      (fun ((toks : pos tok list), (line : int), (col : int)) (tok : Str.split_result) ->
        match tok with
        (* This could have also been written as
            | Delim " " -> ...
            | Delim "\t" -> ...
           but for _this assignment's starter code_, we follow the
           "template" more strictly as a demonstration; you need not
           abide by the template this strictly. *)
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
              try (TInt (Int64.of_string t, (line, col, line, col + tLen)) :: toks, line, col + tLen)
              with Failure _ -> (TSym (t, (line, col, line, col + tLen)) :: toks, line, col + tLen)
            ) )
      ([], 0, 0)
      (full_split (regexp "[()\n\t ]") str)
  in
  List.rev toks
;;

type 'a sexp =
  | Sym of string * 'a
  | Int of int64 * 'a
  | Bool of bool * 'a
  | Nest of 'a sexp list * 'a

let sexp_info s =
  match s with
  | Sym (_, x) -> x
  | Int (_, x) -> x
  | Bool (_, x) -> x
  | Nest (_, x) -> x
;;

exception SexpParseFailure of string

let parse_toks (toks : pos tok list) : pos sexp list =
  (* Combines two source positions into one larger one. *)
  let concat_pos (sl1, sc1, _, _) (_, _, el2, ec2) = (sl1, sc1, el2, ec2) in
  (* Takes a token list and produces a single sexp, along with any leftover tokens *)
  let rec parse_one toks : pos sexp * pos tok list =
    match toks with
    | [] -> raise (SexpParseFailure "No tokens to parse")
    | TSym (t, p) :: rest -> (Sym (t, p), rest)
    | TInt (i, p) :: rest -> (Int (i, p), rest)
    | TBool (b, p) :: rest -> (Bool (b, p), rest)
    | LPAREN p1 :: rest -> (
      match parse_many rest with
      | sexps, RPAREN p2 :: tail -> (Nest (sexps, concat_pos p1 p2), tail)
      | _ ->
          raise
            (SexpParseFailure (Printf.sprintf "Unmatched left paren at %s" (pos_to_string p1 false)))
      )
    (* By prefixing an identifier's name with `_`, we can give an unused variable a more
       descriptive name, and the compiler will not give a warning about it being unused *)
    | RPAREN p :: _rest ->
        raise
          (SexpParseFailure (Printf.sprintf "Unmatched right paren at %s" (pos_to_string p false)))
  (* Takes a token list and produces as many sexps as it can, along with any leftover tokens *)
  and parse_many (toks : pos tok list) : pos sexp list * pos tok list =
    match toks with
    | [] -> ([], [])
    | RPAREN _ :: _ -> ([], toks)
    | _t_non_paren :: _ ->
        let sexp, rest = parse_one toks in
        let sexps, tail = parse_many rest in
        (sexp :: sexps, tail)
  in
  match parse_many toks with
  | sexps, [] -> sexps
  | _sexps, t_leftover :: _ ->
      raise
        (SexpParseFailure
           (Printf.sprintf "Incomplete sexpression beginning at %s"
              (pos_to_string (tok_info t_leftover) false) ) )
;;

let parse (str : string) : pos sexp =
  match parse_toks (tokenize str) with
  | [p] -> p
  | _ -> raise (SexpParseFailure "Multiple top-level s-expressions found")
;;
