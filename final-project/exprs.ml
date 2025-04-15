open Printf

let show_debug_print = ref false

let debug_printf fmt =
  if !show_debug_print then
    printf fmt
  else
    ifprintf stdout fmt
;;

type tag = int

type sourcespan = Lexing.position * Lexing.position

type prim1 =
  | Add1
  | Sub1
  | Print
  | IsBool
  | IsNum
  | IsTuple
  | Not
  | PrintStack
  | Crash

type prim2 =
  | Plus
  | Minus
  | Times
  | And
  | Or
  | Greater
  | GreaterEq
  | Less
  | LessEq
  | Eq
  | CheckSize

and 'a bind =
  | BBlank of 'a
  | BName of string * bool * 'a
  | BTuple of 'a bind list * 'a

and 'a binding = 'a bind * 'a expr * 'a

and call_type =
  | Native
  | Snake
  | Prim
  | Unknown

and 'a expr =
  | ESeq of 'a expr * 'a expr * 'a
  | ETuple of 'a expr list * 'a
  | EGetItem of 'a expr * 'a expr * 'a
  | ESetItem of 'a expr * 'a expr * 'a expr * 'a
  | ELet of 'a binding list * 'a expr * 'a
  | EPrim1 of prim1 * 'a expr * 'a
  | EPrim2 of prim2 * 'a expr * 'a expr * 'a
  | EIf of 'a expr * 'a expr * 'a expr * 'a
  | ENumber of int64 * 'a
  | EBool of bool * 'a
  | ENil of 'a
  | EId of string * 'a
  | EApp of 'a expr * 'a expr list * call_type * 'a
  | ELambda of 'a bind list * 'a expr * 'a
  | ELetRec of 'a binding list * 'a expr * 'a
  | ECheckSpits of 'a expr * 'a expr * 'a

type 'a decl = DFun of string * 'a bind list * 'a expr * 'a

type 'a program = Program of 'a decl list list * 'a expr * 'a

type 'a immexpr =
  (* immediate expressions *)
  | ImmNum of int64 * 'a
  | ImmBool of bool * 'a
  | ImmId of string * 'a
  | ImmNil of 'a

and 'a cexpr =
  (* compound expressions *)
  | CIf of 'a immexpr * 'a aexpr * 'a aexpr * 'a
  | CPrim1 of prim1 * 'a immexpr * 'a
  | CPrim2 of prim2 * 'a immexpr * 'a immexpr * 'a
  | CApp of 'a immexpr * 'a immexpr list * call_type * 'a
  | CImmExpr of 'a immexpr (* for when you just need an immediate value *)
  | CTuple of 'a immexpr list * 'a
  | CGetItem of 'a immexpr * 'a immexpr * 'a
  | CSetItem of 'a immexpr * 'a immexpr * 'a immexpr * 'a
  | CLambda of string list * 'a aexpr * 'a
  | CCheckSpits of 'a immexpr * 'a immexpr * 'a

and 'a aexpr =
  (* anf expressions *)
  | ASeq of 'a cexpr * 'a aexpr * 'a
  | ALet of string * 'a cexpr * 'a aexpr * 'a
  | ALetRec of (string * 'a cexpr) list * 'a aexpr * 'a
  | ACExpr of 'a cexpr

and 'a aprogram = AProgram of 'a aexpr * 'a

type alloc_strategy =
  | Register
  | Naive

let map_opt f v =
  match v with
  | None -> None
  | Some v -> Some (f v)
;;

let get_tag_E e =
  match e with
  | ELet (_, _, t) -> t
  | ELetRec (_, _, t) -> t
  | EPrim1 (_, _, t) -> t
  | EPrim2 (_, _, _, t) -> t
  | EIf (_, _, _, t) -> t
  | ENil t -> t
  | ENumber (_, t) -> t
  | EBool (_, t) -> t
  | EId (_, t) -> t
  | EApp (_, _, _, t) -> t
  | ETuple (_, t) -> t
  | EGetItem (_, _, t) -> t
  | ESetItem (_, _, _, t) -> t
  | ESeq (_, _, t) -> t
  | ELambda (_, _, t) -> t
  | ECheckSpits (_, _, t) -> t
;;

let get_tag_D d =
  match d with
  | DFun (_, _, _, t) -> t
;;

let rec map_tag_E (f : 'a -> 'b) (e : 'a expr) =
  match e with
  | ESeq (e1, e2, a) -> ESeq (map_tag_E f e1, map_tag_E f e2, f a)
  | ETuple (exprs, a) -> ETuple (List.map (map_tag_E f) exprs, f a)
  | EGetItem (e, idx, a) -> EGetItem (map_tag_E f e, map_tag_E f idx, f a)
  | ESetItem (e, idx, newval, a) ->
      ESetItem (map_tag_E f e, map_tag_E f idx, map_tag_E f newval, f a)
  | EId (x, a) -> EId (x, f a)
  | ENumber (n, a) -> ENumber (n, f a)
  | EBool (b, a) -> EBool (b, f a)
  | ENil a -> ENil (f a)
  | EPrim1 (op, e, a) ->
      let tag_prim = f a in
      EPrim1 (op, map_tag_E f e, tag_prim)
  | EPrim2 (op, e1, e2, a) ->
      let tag_prim = f a in
      let tag_e1 = map_tag_E f e1 in
      let tag_e2 = map_tag_E f e2 in
      EPrim2 (op, tag_e1, tag_e2, tag_prim)
  | ELet (binds, body, a) ->
      let tag_let = f a in
      let tag_binding (b, e, t) =
        let tag_bind = f t in
        let tag_b = map_tag_B f b in
        let tag_e = map_tag_E f e in
        (tag_b, tag_e, tag_bind)
      in
      let tag_binds = List.map tag_binding binds in
      let tag_body = map_tag_E f body in
      ELet (tag_binds, tag_body, tag_let)
  | ELetRec (binds, body, a) ->
      let tag_let = f a in
      let tag_binding (b, e, t) =
        let tag_bind = f t in
        let tag_b = map_tag_B f b in
        let tag_e = map_tag_E f e in
        (tag_b, tag_e, tag_bind)
      in
      let tag_binds = List.map tag_binding binds in
      let tag_body = map_tag_E f body in
      ELetRec (tag_binds, tag_body, tag_let)
  | EIf (cond, thn, els, a) ->
      let tag_if = f a in
      let tag_cond = map_tag_E f cond in
      let tag_thn = map_tag_E f thn in
      let tag_els = map_tag_E f els in
      EIf (tag_cond, tag_thn, tag_els, tag_if)
  | EApp (func, args, native, a) ->
      let tag_app = f a in
      EApp (map_tag_E f func, List.map (map_tag_E f) args, native, tag_app)
  | ELambda (binds, body, a) ->
      let tag_lam = f a in
      ELambda (List.map (map_tag_B f) binds, map_tag_E f body, tag_lam)
  | ECheckSpits (result, expected, a) ->
      let tag_result = map_tag_E f result in
      let tag_expected = map_tag_E f expected in
      ECheckSpits (tag_result, tag_expected, f a)

and map_tag_B (f : 'a -> 'b) b =
  match b with
  | BBlank tag -> BBlank (f tag)
  | BName (x, allow_shadow, ax) ->
      let tag_ax = f ax in
      BName (x, allow_shadow, tag_ax)
  | BTuple (binds, t) ->
      let tag_tup = f t in
      BTuple (List.map (map_tag_B f) binds, tag_tup)

and map_tag_D (f : 'a -> 'b) d =
  match d with
  | DFun (name, args, body, a) ->
      let tag_fun = f a in
      let tag_args = List.map (map_tag_B f) args in
      let tag_body = map_tag_E f body in
      DFun (name, tag_args, tag_body, tag_fun)

and map_tag_P (f : 'a -> 'b) p =
  match p with
  | Program (declgroups, body, a) ->
      let tag_a = f a in
      let tag_decls = List.map (fun group -> List.map (map_tag_D f) group) declgroups in
      let tag_body = map_tag_E f body in
      Program (tag_decls, tag_body, tag_a)
;;

let tag (p : 'a program) : tag program =
  let next = ref 0 in
  let tag _ =
    next := !next + 1;
    !next
  in
  map_tag_P tag p
;;

let combine_tags (f1 : 'a -> 'b) (f2 : 'a -> 'c) (p : 'a program) : ('b * 'c) program =
  map_tag_P (fun a -> (f1 a, f2 a)) p
;;

let tag_and_map (f : 'a -> 'b) (p : 'a program) : ('a * 'b) program =
  map_tag_P (fun a -> (a, f a)) p
;;

let prog_and_tag (p : 'a program) : ('a * tag) program =
  let next = ref 0 in
  let tag _ =
    next := !next + 1;
    !next
  in
  tag_and_map tag p
;;

let rec untagP (p : 'a program) : unit program =
  match p with
  | Program (decls, body, _) ->
      Program (List.map (fun group -> List.map untagD group) decls, untagE body, ())

and untagE e =
  match e with
  | ESeq (e1, e2, _) -> ESeq (untagE e1, untagE e2, ())
  | ETuple (exprs, _) -> ETuple (List.map untagE exprs, ())
  | EGetItem (e, idx, _) -> EGetItem (untagE e, untagE idx, ())
  | ESetItem (e, idx, newval, _) -> ESetItem (untagE e, untagE idx, untagE newval, ())
  | EId (x, _) -> EId (x, ())
  | ENumber (n, _) -> ENumber (n, ())
  | EBool (b, _) -> EBool (b, ())
  | ENil _ -> ENil ()
  | EPrim1 (op, e, _) -> EPrim1 (op, untagE e, ())
  | EPrim2 (op, e1, e2, _) -> EPrim2 (op, untagE e1, untagE e2, ())
  | ELet (binds, body, _) ->
      ELet (List.map (fun (b, e, _) -> (untagB b, untagE e, ())) binds, untagE body, ())
  | EIf (cond, thn, els, _) -> EIf (untagE cond, untagE thn, untagE els, ())
  | EApp (func, args, native, _) -> EApp (untagE func, List.map untagE args, native, ())
  | ELetRec (binds, body, _) ->
      ELetRec (List.map (fun (b, e, _) -> (untagB b, untagE e, ())) binds, untagE body, ())
  | ELambda (binds, body, _) -> ELambda (List.map untagB binds, untagE body, ())
  | ECheckSpits (result, expected, _) -> ECheckSpits (untagE result, untagE expected, ())

and untagB b =
  match b with
  | BBlank _ -> BBlank ()
  | BName (x, allow_shadow, _) -> BName (x, allow_shadow, ())
  | BTuple (binds, _) -> BTuple (List.map untagB binds, ())

and untagD d =
  match d with
  | DFun (name, args, body, _) -> DFun (name, List.map untagB args, untagE body, ())
;;

let atag (p : 'a aprogram) : tag aprogram =
  let next = ref 0 in
  let tag () =
    next := !next + 1;
    !next
  in
  let rec helpA (e : 'a aexpr) : tag aexpr =
    match e with
    | ASeq (e1, e2, _) ->
        let seq_tag = tag () in
        ASeq (helpC e1, helpA e2, seq_tag)
    | ALet (x, c, b, _) ->
        let let_tag = tag () in
        ALet (x, helpC c, helpA b, let_tag)
    | ALetRec (xcs, b, _) ->
        let let_tag = tag () in
        ALetRec (List.map (fun (x, c) -> (x, helpC c)) xcs, helpA b, let_tag)
    | ACExpr c -> ACExpr (helpC c)
  and helpC (c : 'a cexpr) : tag cexpr =
    match c with
    | CPrim1 (op, e, _) ->
        let prim_tag = tag () in
        CPrim1 (op, helpI e, prim_tag)
    | CPrim2 (op, e1, e2, _) ->
        let prim_tag = tag () in
        CPrim2 (op, helpI e1, helpI e2, prim_tag)
    | CIf (cond, thn, els, _) ->
        let if_tag = tag () in
        CIf (helpI cond, helpA thn, helpA els, if_tag)
    | CApp (func, args, native, _) ->
        let app_tag = tag () in
        CApp (helpI func, List.map helpI args, native, app_tag)
    | CImmExpr i -> CImmExpr (helpI i)
    | CTuple (es, _) ->
        let tup_tag = tag () in
        CTuple (List.map helpI es, tup_tag)
    | CGetItem (e, idx, _) ->
        let get_tag = tag () in
        CGetItem (helpI e, helpI idx, get_tag)
    | CSetItem (e, idx, newval, _) ->
        let set_tag = tag () in
        CSetItem (helpI e, helpI idx, helpI newval, set_tag)
    | CLambda (args, body, _) ->
        let lam_tag = tag () in
        CLambda (args, helpA body, lam_tag)
    | CCheckSpits (result, expected, _) ->
        let check_tag = tag () in
        CCheckSpits (helpI result, helpI expected, check_tag)
  and helpI (i : 'a immexpr) : tag immexpr =
    match i with
    | ImmNil _ -> ImmNil (tag ())
    | ImmId (x, _) -> ImmId (x, tag ())
    | ImmNum (n, _) -> ImmNum (n, tag ())
    | ImmBool (b, _) -> ImmBool (b, tag ())
  and helpP p =
    match p with
    | AProgram (body, _) -> AProgram (helpA body, 0)
  in
  helpP p
;;
