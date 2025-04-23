open Printf

let show_debug_print = ref false

let debug_printf fmt =
  if !show_debug_print then
    printf fmt
  else
    ifprintf stdout fmt
;;

type sourcespan = Lexing.position * Lexing.position

type tag = int * sourcespan

type except =
  | Runtime
  | Value

type test_type =
  | DeepEq
  | ShallowEq
  | Pred
  | Raises

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
  | Raise
  | ReportTestPass
  | ReportTestFailException

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
  | ReportTestFailMismatch

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
  | EException of except * 'a
  (* try () catch RuntimeExcexption as e in () *)
  | ETryCatch of 'a expr * 'a bind * 'a expr * 'a expr * 'a
  | ECheck of 'a expr list * 'a
  | ETestOp1 of 'a expr * 'a expr * bool * 'a
  | ETestOp2 of 'a expr * 'a expr * test_type * bool * 'a
  | ETestOp2Pred of 'a expr * 'a expr * 'a expr * bool * 'a

type 'a decl = DFun of string * 'a bind list * 'a expr * 'a

type 'a program = Program of 'a decl list list * 'a expr * 'a expr list * 'a

type 'a immexpr =
  (* immediate expressions *)
  | ImmNum of int64 * 'a
  | ImmBool of bool * 'a
  | ImmId of string * 'a
  | ImmNil of 'a
  | ImmExcept of except * 'a (* This will need to change if we add more data... *)

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
  (* The CTryCatch does not have a `bind` anymore because it was desugared away *)
  | CTryCatch of 'a immexpr * except * 'a immexpr * 'a
  | CCheck of 'a immexpr list * 'a
  | CTestOp1 of 'a immexpr * 'a immexpr * bool * 'a
  | CTestOp2 of 'a immexpr * 'a immexpr * test_type * bool * 'a
  | CTestOp2Pred of 'a immexpr * 'a immexpr * 'a immexpr * bool * 'a

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
  | ELet (_, _, t)
   |ELetRec (_, _, t)
   |EPrim1 (_, _, t)
   |EPrim2 (_, _, _, t)
   |EIf (_, _, _, t)
   |ENil t
   |ENumber (_, t)
   |EBool (_, t)
   |EId (_, t)
   |EApp (_, _, _, t)
   |ETuple (_, t)
   |EGetItem (_, _, t)
   |ESetItem (_, _, _, t)
   |ESeq (_, _, t)
   |ELambda (_, _, t)
   |EException (_, t)
   |ETryCatch (_, _, _, _, t)
   |ECheck (_, t)
   |ETestOp1 (_, _, _, t)
   |ETestOp2 (_, _, _, _, t)
   |ETestOp2Pred (_, _, _, _, t) -> t
;;

let get_tag_I (e : 'a immexpr) =
  match e with
  | ImmBool (_, t) | ImmNil t | ImmExcept (_, t) | ImmId (_, t) | ImmNum (_, t) -> t
;;

let get_tag_C (e : 'a cexpr) =
  match e with
  | CImmExpr i -> get_tag_I i
  | CApp (_, _, _, t)
   |CCheck (_, t)
   |CGetItem (_, _, t)
   |CIf (_, _, _, t)
   |CLambda (_, _, t)
   |CPrim1 (_, _, t)
   |CPrim2 (_, _, _, t)
   |CSetItem (_, _, _, t)
   |CTestOp1 (_, _, _, t)
   |CTestOp2 (_, _, _, _, t)
   |CTestOp2Pred (_, _, _, _, t)
   |CTryCatch (_, _, _, t)
   |CTuple (_, t) -> t
;;

let get_tag_A (e : 'a aexpr) =
  match e with
  | ACExpr c -> get_tag_C c
  | ALet (_, _, _, t) | ALetRec (_, _, t) | ASeq (_, _, t) -> t
;;

let get_tag_D d =
  match d with
  | DFun (_, _, _, t) -> t
;;

let rec map_tag_E (f : 'a -> 'b) (e : sourcespan expr) : ('b * 'c) expr =
  match e with
  | ESeq (e1, e2, s) -> ESeq (map_tag_E f e1, map_tag_E f e2, (f s, s))
  | ETuple (exprs, s) -> ETuple (List.map (map_tag_E f) exprs, (f s, s))
  | EGetItem (e, idx, s) -> EGetItem (map_tag_E f e, map_tag_E f idx, (f s, s))
  | ESetItem (e, idx, newval, s) ->
      ESetItem (map_tag_E f e, map_tag_E f idx, map_tag_E f newval, (f s, s))
  | EId (x, s) -> EId (x, (f s, s))
  | ENumber (n, s) -> ENumber (n, (f s, s))
  | EBool (b, s) -> EBool (b, (f s, s))
  | ENil s -> ENil (f s, s)
  | EPrim1 (op, e, s) ->
      let tag_prim = (f s, s) in
      EPrim1 (op, map_tag_E f e, tag_prim)
  | EPrim2 (op, e1, e2, s) ->
      let tag_prim = (f s, s) in
      let tag_e1 = map_tag_E f e1 in
      let tag_e2 = map_tag_E f e2 in
      EPrim2 (op, tag_e1, tag_e2, tag_prim)
  | ELet (binds, body, s) ->
      let tag_let = (f s, s) in
      let tag_binding (b, e, s2) =
        let tag_bind = (f s2, s2) in
        let tag_b = map_tag_B f b in
        let tag_e = map_tag_E f e in
        (tag_b, tag_e, tag_bind)
      in
      let tag_binds = List.map tag_binding binds in
      let tag_body = map_tag_E f body in
      ELet (tag_binds, tag_body, tag_let)
  | ELetRec (binds, body, s) ->
      let tag_let = (f s, s) in
      let tag_binding (b, e, s2) =
        let tag_bind = (f s2, s2) in
        let tag_b = map_tag_B f b in
        let tag_e = map_tag_E f e in
        (tag_b, tag_e, tag_bind)
      in
      let tag_binds = List.map tag_binding binds in
      let tag_body = map_tag_E f body in
      ELetRec (tag_binds, tag_body, tag_let)
  | EIf (cond, thn, els, s) ->
      let tag_if = (f s, s) in
      let tag_cond = map_tag_E f cond in
      let tag_thn = map_tag_E f thn in
      let tag_els = map_tag_E f els in
      EIf (tag_cond, tag_thn, tag_els, tag_if)
  | EApp (func, args, native, s) ->
      let tag_app = (f s, s) in
      EApp (map_tag_E f func, List.map (map_tag_E f) args, native, tag_app)
  | ELambda (binds, body, s) ->
      let tag_lam = (f s, s) in
      ELambda (List.map (map_tag_B f) binds, map_tag_E f body, tag_lam)
  | EException (e, s) -> EException (e, (f s, s))
  | ETryCatch (t, bind, excptn, c, s) ->
      let tag_try_catch = (f s, s) in
      let tag_try = map_tag_E f t in
      let tag_catch = map_tag_E f c in
      let tag_bind = map_tag_B f bind in
      let tag_exception = map_tag_E f excptn in
      ETryCatch (tag_try, tag_bind, tag_exception, tag_catch, tag_try_catch)
  | ECheck (exprs, s) -> ECheck (List.map (map_tag_E f) exprs, (f s, s))
  | ETestOp1 (e1, e2, n, s) -> ETestOp1 (map_tag_E f e1, map_tag_E f e2, n, (f s, s))
  | ETestOp2 (e1, e2, tt, n, s) -> ETestOp2 (map_tag_E f e1, map_tag_E f e2, tt, n, (f s, s))
  | ETestOp2Pred (e1, e2, e3, n, s) ->
      ETestOp2Pred (map_tag_E f e1, map_tag_E f e2, map_tag_E f e3, n, (f s, s))

and map_tag_B (f : 'a -> int) (b : sourcespan bind) : tag bind =
  match b with
  | BBlank s -> BBlank (f s, s)
  | BName (x, allow_shadow, s) ->
      let tag_ax = (f s, s) in
      BName (x, allow_shadow, tag_ax)
  | BTuple (binds, s) ->
      let tag_tup = (f s, s) in
      BTuple (List.map (map_tag_B f) binds, tag_tup)

and map_tag_D (f : 'a -> 'b) d : ('b * 'c) decl =
  match d with
  | DFun (name, args, body, s) ->
      let tag_fun = (f s, s) in
      let tag_args = List.map (map_tag_B f) args in
      let tag_body = map_tag_E f body in
      DFun (name, tag_args, tag_body, tag_fun)

and map_tag_P (f : 'a -> 'b) (p : sourcespan program) : tag program =
  match p with
  | Program (declgroups, body, checks, s) ->
      let tag_a = (f s, s) in
      let tag_decls = List.map (fun group -> List.map (map_tag_D f) group) declgroups in
      let tag_body = map_tag_E f body in
      let tag_checks = List.map (map_tag_E f) checks in
      Program (tag_decls, tag_body, tag_checks, tag_a)
;;

let tag (p : sourcespan program) : tag program =
  let next = ref 0 in
  let tag _ =
    next := !next + 1;
    !next
  in
  map_tag_P tag p
;;

(* let combine_tags (f1 : 'a -> 'b) (f2 : 'a -> 'c) (p : 'a program) : ('b * 'c) program =
  map_tag_P (fun (a, b) -> ((f1 a), f2 a)) p
;; *)

let rec untagP (p : 'a program) : unit program =
  match p with
  | Program (decls, body, checks, _) ->
      Program
        ( List.map (fun group -> List.map untagD group) decls,
          untagE body,
          List.map untagE checks,
          () )

and untagE (e : 'a expr) =
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
  | EException (ex, _) -> EException (ex, ())
  | ETryCatch (t, bind, excptn, c, _) ->
      ETryCatch (untagE t, untagB bind, untagE excptn, untagE c, ())
  | ECheck (ops, _) -> ECheck (List.map untagE ops, ())
  | ETestOp1 (e1, e2, n, _) -> ETestOp1 (untagE e1, untagE e2, n, ())
  | ETestOp2 (e1, e2, tt, n, _) -> ETestOp2 (untagE e1, untagE e2, tt, n, ())
  | ETestOp2Pred (e1, e2, e3, n, _) -> ETestOp2Pred (untagE e1, untagE e2, untagE e3, n, ())

and untagB (b : 'a bind) =
  match b with
  | BBlank _ -> BBlank ()
  | BName (x, allow_shadow, _) -> BName (x, allow_shadow, ())
  | BTuple (binds, _) -> BTuple (List.map untagB binds, ())

and untagD (d : 'a decl) =
  match d with
  | DFun (name, args, body, _) -> DFun (name, List.map untagB args, untagE body, ())
;;

let atag (p : sourcespan aprogram) : tag aprogram =
  let next = ref 0 in
  let tag () =
    next := !next + 1;
    !next
  in
  let rec helpA (e : 'a aexpr) : tag aexpr =
    match e with
    | ASeq (e1, e2, s) ->
        let seq_tag = tag () in
        ASeq (helpC e1, helpA e2, (seq_tag, s))
    | ALet (x, c, b, s) ->
        let let_tag = tag () in
        ALet (x, helpC c, helpA b, (let_tag, s))
    | ALetRec (xcs, b, s) ->
        let let_tag = tag () in
        ALetRec (List.map (fun (x, c) -> (x, helpC c)) xcs, helpA b, (let_tag, s))
    | ACExpr c -> ACExpr (helpC c)
  and helpC (c : sourcespan cexpr) : tag cexpr =
    match c with
    | CPrim1 (op, e, s) ->
        let prim_tag = tag () in
        CPrim1 (op, helpI e, (prim_tag, s))
    | CPrim2 (op, e1, e2, s) ->
        let prim_tag = tag () in
        CPrim2 (op, helpI e1, helpI e2, (prim_tag, s))
    | CIf (cond, thn, els, s) ->
        let if_tag = tag () in
        CIf (helpI cond, helpA thn, helpA els, (if_tag, s))
    | CApp (func, args, native, s) ->
        let app_tag = tag () in
        CApp (helpI func, List.map helpI args, native, (app_tag, s))
    | CImmExpr i -> CImmExpr (helpI i)
    | CTuple (es, s) ->
        let tup_tag = tag () in
        CTuple (List.map helpI es, (tup_tag, s))
    | CGetItem (e, idx, s) ->
        let get_tag = tag () in
        CGetItem (helpI e, helpI idx, (get_tag, s))
    | CSetItem (e, idx, newval, s) ->
        let set_tag = tag () in
        CSetItem (helpI e, helpI idx, helpI newval, (set_tag, s))
    | CLambda (args, body, s) ->
        let lam_tag = tag () in
        CLambda (args, helpA body, (lam_tag, s))
    | CTryCatch (t, except, c, s) ->
        let try_catch_tag = tag () in
        CTryCatch (helpI t, except, helpI c, (try_catch_tag, s))
    | CCheck (ops, s) ->
        let catch_tag = tag () in
        CCheck (List.map helpI ops, (catch_tag, s))
    | CTestOp1 (e1, e2, n, s) ->
        let test_op_1_tag = tag () in
        CTestOp1 (helpI e1, helpI e2, n, (test_op_1_tag, s))
    | CTestOp2 (e1, e2, tt, n, s) ->
        let test_op_2_tag = tag () in
        CTestOp2 (helpI e1, helpI e2, tt, n, (test_op_2_tag, s))
    | CTestOp2Pred (e1, e2, e3, n, s) ->
        let test_op_2_pred_tag = tag () in
        CTestOp2Pred (helpI e1, helpI e2, helpI e3, n, (test_op_2_pred_tag, s))
  and helpI (i : 'a immexpr) : tag immexpr =
    match i with
    | ImmNil s -> ImmNil (tag (), s)
    | ImmId (x, s) -> ImmId (x, (tag (), s))
    | ImmNum (n, s) -> ImmNum (n, (tag (), s))
    | ImmBool (b, s) -> ImmBool (b, (tag (), s))
    | ImmExcept (e, s) -> ImmExcept (e, (tag (), s))
  and helpP p =
    match p with
    | AProgram (body, s) -> AProgram (helpA body, (0, s))
  in
  helpP p
;;
