open Exprs
open Format
open Lexing

let rec intersperse (elts : 'a list) (sep : 'a) : 'a list =
  match elts with
  | [] -> []
  | [elt] -> [elt]
  | elt :: rest -> elt :: sep :: intersperse rest sep
;;

let string_of_op1 op =
  match op with
  | Add1 -> "add1"
  | Sub1 -> "sub1"
;;

let string_of_op2 op =
  match op with
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
;;

let rec string_of_expr (e : 'a expr) : string =
  match e with
  | ENumber (n, _) -> Int64.to_string n
  | EId (x, _) -> x
  | EPrim1 (op, e, _) -> sprintf "%s(%s)" (string_of_op1 op) (string_of_expr e)
  | EPrim2 (op, left, right, _) ->
      sprintf "(%s %s %s)" (string_of_expr left) (string_of_op2 op) (string_of_expr right)
  | ELet (binds, body, _) ->
      let binds_strs = List.map (fun (x, e, _) -> sprintf "%s = %s" x (string_of_expr e)) binds in
      let binds_str = List.fold_left ( ^ ) "" (intersperse binds_strs ", ") in
      sprintf "(let %s in %s)" binds_str (string_of_expr body)
  | EIf (cond, thn, els, _) ->
      sprintf "(if %s: %s else: %s)" (string_of_expr cond) (string_of_expr thn) (string_of_expr els)
;;

let string_of_pos ((pstart, pend) : Lexing.position * Lexing.position) : string =
  sprintf "%s, %d:%d-%d:%d" pstart.pos_fname pstart.pos_lnum
    (pstart.pos_cnum - pstart.pos_bol)
    pend.pos_lnum (pend.pos_cnum - pend.pos_bol)
;;

let format_expr (e : 'a expr) (print_a : 'a -> string) : string =
  let maybe_a a =
    let astr = print_a a in
    if astr = "" then
      ""
    else
      "<" ^ astr ^ ">"
  in
  let indent = 2 in
  let print_list fmt p_item items p_sep =
    match items with
    | [] -> ()
    | [item] -> p_item fmt item
    | first :: rest ->
        p_item fmt first;
        List.iter (fun item -> p_sep fmt; p_item fmt item) rest
  in
  let print_comma_sep fmt = pp_print_string fmt ","; pp_print_space fmt () in
  let open_label fmt label a =
    pp_open_hvbox fmt indent;
    pp_print_string fmt label;
    pp_print_string fmt (maybe_a a);
    pp_print_string fmt "(";
    pp_print_cut fmt ()
  in
  let open_paren fmt = pp_open_box fmt 2; pp_print_string fmt "("; pp_print_cut fmt () in
  let close_paren fmt =
    pp_print_break fmt 0 ~-indent; pp_close_box fmt (); pp_print_string fmt ")"
  in
  let quote x = "\"" ^ x ^ "\"" in
  let rec help e fmt =
    match e with
    | ENumber (n, a) ->
        open_label fmt "ENumber" a;
        pp_print_string fmt (Int64.to_string n);
        close_paren fmt
    | EId (x, a) ->
        open_label fmt "EId" a;
        pp_print_string fmt (quote x);
        close_paren fmt
    | EPrim1 (op, e, a) ->
        open_label fmt "EPrim1" a;
        pp_print_string fmt
          ( match op with
          | Add1 -> "Add1"
          | Sub1 -> "Sub1" );
        print_comma_sep fmt;
        help e fmt;
        close_paren fmt
    | EPrim2 (op, e1, e2, a) ->
        open_label fmt "EPrim2" a;
        pp_print_string fmt
          ( match op with
          | Plus -> "Plus"
          | Minus -> "Minus"
          | Times -> "Times" );
        print_comma_sep fmt;
        help e1 fmt;
        print_comma_sep fmt;
        help e2 fmt;
        close_paren fmt
    | EIf (cond, thn, els, a) ->
        open_label fmt "EIf" a;
        help cond fmt;
        print_comma_sep fmt;
        help thn fmt;
        print_comma_sep fmt;
        help els fmt;
        close_paren fmt
    | ELet (binds, body, a) ->
        let print_item fmt (x, b, a) =
          open_paren fmt;
          pp_print_string fmt (" " ^ quote x);
          pp_print_string fmt (maybe_a a);
          print_comma_sep fmt;
          help b fmt;
          close_paren fmt
        in
        open_label fmt "ELet" a;
        open_paren fmt;
        print_list fmt print_item binds print_comma_sep;
        close_paren fmt;
        print_comma_sep fmt;
        help body fmt;
        close_paren fmt
  in
  help e str_formatter; flush_str_formatter ()
;;

let ast_of_pos_expr (e : (Lexing.position * Lexing.position) expr) : string =
  format_expr e string_of_pos
;;

let ast_of_expr (e : 'a expr) : string = format_expr e (fun _ -> "")
