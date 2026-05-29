open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
open Graph

(* Re-export extracted modules so that callers (runner.ml, test.ml) that
   `open Compile` continue to see every name. Keep these in dependency order. *)
include Util
include Constants
include Env
include Well_formed
include Desugar
include Rename
include Anf
include Free_vars
include Naive_alloc
include Liveness

(* Consumes an AExpr tagged with sets of live variables *)
let interfere (e : livevars aexpr) : grapht =
  let rec helpA e g =
    match e with
    | ASeq (_, next, l) ->
        let g' = add_nodes g (StringSet.to_list l) in
        helpA next (connect_set l g')
    | ALet (x, _, b, l) ->
        let g' = add_node g x in
        let g' = add_nodes g' (StringSet.to_list l) in
        let connected = connect_set l g' in
        helpA b (connect x l connected)
    | ALetRec (bindings, b, l) ->
        let names, _ = List.split bindings in
        let g' = add_nodes g names in
        let g' = add_nodes g' (StringSet.to_list l) in
        let names = StringSet.of_list names in
        let connected_names = connect_set names g' in
        let connected_set = connect_set l connected_names in
        let all_connected = connect2 names l connected_set in
        helpA b all_connected
    | ACExpr (CIf (_, thn, els, l)) ->
        let g' = add_nodes g (StringSet.to_list l) in
        helpA thn (helpA els (connect_set l g'))
    | _ -> g
  in
  helpA e Graph.empty
;;

(* We got rid of the scratch registers because they were too important... *)
let colors = List.map (fun x -> Reg x) [R12; R13; R14; RBX]

let color_graph ?(colors = colors) (g : grapht) (init_env : arg name_envt) : arg name_envt =
  (* Get the node with the smallest degree. *)
  let rec worklist (gw : grapht) (stack : string list) : string list =
    match smallest_degree gw with
    | None -> stack
    | Some node -> worklist (remove_node gw node) (node :: stack)
  in
  let next_color (nodes : neighborst) (mapping : arg name_envt) : arg =
    let allocated =
      List.filter_map (fun node -> StringMap.find_opt node mapping) (NeighborSet.to_list nodes)
    in
    let next_offset =
      (* Remember to use -1 and `min` because the offsets grow downward. *)
      ~-1
      + List.fold_left
          (fun acc arg ->
            match arg with
            | RegOffset (n, _) -> min n acc
            | _ -> acc )
          0 allocated
    in
    let next_register = List.find_opt (fun color -> not (List.mem color allocated)) colors in
    match next_register with
    | None -> RegOffset (next_offset, RBP)
    | Some arg -> arg
  in
  let color_nodes (stack : string list) (mapping : arg name_envt) : arg name_envt =
    List.fold_right
      (fun node mapping' ->
        let neighbors = Graph.find node g in
        let color = next_color neighbors mapping' in
        StringMap.add node color mapping' )
      stack mapping
  in
  color_nodes (worklist g []) init_env
;;

let register_allocation (prog : tag aprogram) : tag aprogram * arg name_envt name_envt =
  let rec helpC (e : freevars cexpr) (env_name : string) (env_env : arg name_envt name_envt) :
      arg name_envt name_envt =
    match e with
    | CPrim1 _
     |CPrim2 _
     |CApp _
     |CImmExpr _
     |CTuple _
     |CGetItem _
     |CSetItem _
     |CTryCatch _
     |CCheck _
     |CTestOp1 _
     |CTestOp2 _
     |CTestOp2Pred _ -> env_env
    | CIf (_, thn, els, _) ->
        let thn_env = helpA thn env_name env_env in
        helpA els env_name thn_env
    | CLambda (ids, body, _) ->
        let args_locs = List.mapi (fun index id -> (id, RegOffset (index + 3, RBP))) ids in
        let args_env =
          List.fold_left
            (fun envt_envt (id, location) -> update_envt_envt env_name id location envt_envt)
            env_env args_locs
        in
        helpA body env_name args_env
  (* helper for ANF expressions *)
  and helpA (e : freevars aexpr) (env_name : string) (env_env : arg name_envt name_envt) :
      arg name_envt name_envt =
    match e with
    | ACExpr cexp -> helpC cexp env_name env_env
    | ALetRec ([], body, _) -> helpA body env_name env_env
    | ALet (id, (CLambda _ as lambda), body, _) ->
        let add_base_env_for_lambda = StringMap.add id StringMap.empty env_env in
        let lambda_color_map = color_graph (interfere e) (safe_find_opt env_name env_env) in
        let lambda_offset = helpC lambda id add_base_env_for_lambda in
        let body_offset = helpA body env_name lambda_offset in
        let offset =
          safe_find_opt id lambda_color_map
            ~callee_tag:("ALet of lambda\n" ^ string_of_name_envt lambda_color_map)
        in
        let cur_envt = update_envt_envt env_name id offset body_offset in
        cur_envt
    | ALetRec ([(id, (CLambda _ as lambda))], body, _) ->
        let add_base_env_for_lambda = StringMap.add id StringMap.empty env_env in
        let lambda_color_map = color_graph (interfere e) (safe_find_opt env_name env_env) in
        let lambda_offset = helpC lambda id add_base_env_for_lambda in
        let body_offset = helpA body env_name lambda_offset in
        let offset =
          safe_find_opt id lambda_color_map
            ~callee_tag:("ALet of lambda\n" ^ string_of_name_envt lambda_color_map)
        in
        let cur_envt = update_envt_envt env_name id offset body_offset in
        cur_envt
    | ALet (_, bound, body, _) ->
        let cur_env = safe_find_opt env_name env_env in
        let colored = color_graph (interfere e) cur_env in
        let env_new = StringMap.add env_name colored env_env in
        let assign_env = helpC bound env_name env_new in
        helpA body env_name assign_env
    | ALetRec ([(_, bound)], body, _) ->
        (* LetRec is not yet truly implemented, since we can't handle mutual recursion. *)
        let bound_env = helpC bound env_name env_env in
        helpA body env_name bound_env
    | ASeq (first, next, _) ->
        let cur_env = safe_find_opt env_name env_env in
        let seq_env = color_graph (interfere e) cur_env in
        let env_new = StringMap.add env_name seq_env env_env in
        let fst_env = helpC first env_name env_new in
        helpA next env_name fst_env
    | _ -> raise (NotYetImplemented "lol")
  in
  let (AProgram (body, _)) = free_vars_cache prog in
  let initial_env = assoc_to_map [(ocsh_name, StringMap.empty)] in
  let body_env = helpA body ocsh_name initial_env in
  (prog, body_env)
;;

(*  ==================================================================================== *)
(*  Code-gen utilities *)
(*  ==================================================================================== *)

let decompose_sourcespan ((pstart, pend) : sourcespan) : int * int * int * int =
  (pstart.pos_lnum, pstart.pos_cnum - pstart.pos_bol, pend.pos_lnum, pend.pos_cnum - pend.pos_bol)
;;

let load_sourcespan s regs =
  let first_four = take regs 4 in
  (* These are not SNAKEVALs! *)
  let sl, sc, el, ec = decompose_sourcespan s in
  List.map2
    (fun reg n -> IMov (Sized (QWORD_PTR, Reg reg), Const (Int64.of_int n)))
    first_four [sl; sc; el; ec]
;;

let check_memory size =
  [ IMov (Reg scratch_reg, Const size);
    IAdd (Reg scratch_reg, Reg heap_reg);
    IMov (Reg scratch_reg2, RelLabel heap_end_label);
    ICmp (Reg scratch_reg, Reg scratch_reg2);
    IJge (Label err_out_of_memory_label) ]
;;

let check_tag value tag err_label =
  [ IMov (Reg scratch_reg, value);
    IAnd (Reg scratch_reg, Const 0x7L);
    (* 0x7 = 0...01111, i.e. the tag bits.*)
    ICmp (Reg scratch_reg, Const tag);
    IJne (Label err_label) ]
;;

let move_with_scratch arg1 arg2 = [IMov (Reg scratch_reg, arg2); IMov (arg1, Reg scratch_reg)]

(* Sets the last four bits of the value in thze given location to 0. *)
let untag_snakeval arg = IAnd (arg, HexConst 0xFFFFFFF8L)

let crash = [IJmp (Label index_high_label)]

(* Enforces that the value in RAX is a bool. Goes to the specified label if not. *)
(* We could check a parameterized register, but that creates complexity in reporting the error. *)
(* We opt to hard-code RAX, for more consistency in exchange for some more boiler-plate code. *)
let check_bool (goto : string) : instruction list =
  let end_label = gensym "bool_check" in
  (* This specifically checks for the enumerated bool values
   * because we used some of the bool values for other stuff
   *)
  [ IMov (Reg scratch_reg2, Reg RAX);
    IMov (Reg scratch_reg, const_false);
    ICmp (Reg scratch_reg2, Reg scratch_reg);
    IJz (Label end_label);
    IMov (Reg scratch_reg, const_true);
    ICmp (Reg scratch_reg2, Reg scratch_reg);
    IJnz (Label goto);
    ILabel end_label ]
;;

let check_exception (goto : string) : instruction list =
  [ IMov (Reg scratch_reg2, Reg RAX);
    IMov (Reg scratch_reg, const_false);
    ICmp (Reg scratch_reg2, Reg scratch_reg);
    IJz (Label goto);
    IMov (Reg scratch_reg, const_true);
    ICmp (Reg scratch_reg2, Reg scratch_reg);
    IJz (Label goto);
    IMov (Reg scratch_reg, HexConst bool_tag_mask);
    IAnd (Reg scratch_reg2, Reg scratch_reg);
    ICmp (Reg scratch_reg2, HexConst bool_tag);
    IJnz (Label goto) ]
;;

(* Enforces that the value in RAX is a num. Goes to the specified label if not. *)
let check_num (goto : string) : instruction list =
  [ IMov (Reg scratch_reg, Reg RAX);
    IMov (Reg scratch_reg2, HexConst num_tag_mask);
    ITest (Reg scratch_reg, Reg scratch_reg2);
    IJnz (Label goto) ]
;;

(* Enforces that the value in RAX is a tuple. Goes to the specified label if not. *)
let check_tuple (goto : string) : instruction list =
  (* This mangles RAX, btw.
     We must either reset rax after this,
     or use a temp register here.
  *)
  [ IMov (Reg scratch_reg2, Reg RAX);
    IAnd (Reg scratch_reg2, HexConst tuple_tag_mask);
    IMov (Reg scratch_reg, HexConst tuple_tag);
    ICmp (Reg scratch_reg2, Reg scratch_reg);
    IJnz (Label goto) ]
;;

(* Enforces that the value in RAX is not nil. Goes to the specified label if it is. *)
let check_not_nil (goto : string) : instruction list =
  [IMov (Reg scratch_reg, HexConst tuple_tag); ICmp (Reg RAX, Reg scratch_reg); IJz (Label goto)]
;;

let check_overflow = IJo (Label overflow_label)

(* Checks that the value in the given location ends in 0x5 (the closure tag).
 * With this and `check_arity`, we make sure not to edit the original register.
 * We need to preserve the tag!
 *)
let check_function =
  [ IMov (Reg scratch_reg, Reg RAX);
    IAnd (Reg scratch_reg, Const closure_tag_mask);
    (* put the checked value into RAX before potentially jumping.*)
    ICmp (Reg scratch_reg, Const closure_tag);
    IJne (Label err_call_not_closure_label) ]
;;

(* Helper for numeric comparisons *)
let compare_prim2 (op : prim2) (e1 : arg) (e2 : arg) ((t, _) : tag) : instruction list =
  (* Move the first arg into RAX so we can type-check it. *)
  let string_op = "comparison_label" in
  let comp_label = sprintf "%s#%d" string_op t in
  let jump =
    match op with
    | Greater -> IJg (Label comp_label)
    | GreaterEq -> IJge (Label comp_label)
    | Less -> IJl (Label comp_label)
    | LessEq -> IJle (Label comp_label)
    | _ -> raise (InternalCompilerError "Expected comparison operator.")
  in
  let comp_done_label = sprintf "%s_done#%d" string_op t in
  [IMov (Reg RAX, e1)]
  @ check_num not_a_number_comp_label
  @ [IMov (Reg RAX, e2)]
  @ check_num not_a_number_comp_label
  @ [ ILineComment (sprintf "BEGIN %s#%d -------------" string_op t);
      IMov (Reg RAX, e1);
      (* cmp is weird and breaks if we don't use a temp register... *)
      IMov (Reg scratch_reg, e2);
      ICmp (Reg RAX, Reg scratch_reg);
      jump;
      IMov (Reg RAX, const_false);
      IJmp (Label comp_done_label);
      ILabel comp_label;
      IMov (Reg RAX, const_true);
      ILabel comp_done_label;
      ILineComment (sprintf "END %s#%d   -------------" string_op t) ]
;;

(* Helper for arithmetic operations *)
let arithmetic_prim2 (op : prim2) (e1 : arg) (e2 : arg) : instruction list =
  (* Move the first arg into RAX so we can type-check it. *)
  [IMov (Reg RAX, e1)]
  @ check_num not_a_number_arith_label
  @ [IMov (Reg RAX, e2)]
  @ check_num not_a_number_arith_label
  @
  match op with
  (* Arithmetic operators *)
  | Plus -> [IMov (Reg scratch_reg, e1); IAdd (Reg RAX, Reg scratch_reg); check_overflow]
  (* Make sure to check for overflow BEFORE shifting on multiplication! *)
  | Times ->
      [ IMov (Reg scratch_reg, e1);
        IMul (Reg RAX, Reg scratch_reg);
        check_overflow;
        ISar (Reg RAX, Const 1L) ]
  (* For minus, we need to move e1 back into RAX to compensate for the lack of commutativity, 
   * while also preserving the order in which our arguments will fail a typecheck.
   * So, `false - true` will fail on `false` every time.
   *)
  | Minus ->
      [ IMov (Reg scratch_reg, e2);
        IMov (Reg RAX, e1);
        ISub (Reg RAX, Reg scratch_reg);
        check_overflow ]
  (* Comparison operators *)
  | _ -> raise (InternalCompilerError "Expected arithmetic operator.")
;;

(* Helper for boolean and *)
let and_prim2 (e1 : arg) (e2 : arg) ((t, _) : tag) : instruction list =
  let true_label = sprintf "true#%d" t in
  let false_label = sprintf "false#%d" t in
  let logic_done_label = sprintf "and_done#%d" t in
  [ ILineComment (sprintf "BEGIN and#%d -------------" t);
    (* Move the first arg into RAX so we can type-check it. *)
    IMov (Reg RAX, e1) ]
  @ check_bool not_a_bool_logic_label
    (* In order to handle short-circuiting, we don't look at the second arg until later.
     * This means that `false and 5` will NOT raise a type error.
     *)
  @ [ IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJz (Label false_label);
      IMov (Reg RAX, e2) ]
  @ check_bool not_a_bool_logic_label
  @ [ (* Need to re-set scratch_reg since it gets changed in check_bool.*)
      IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJz (Label false_label);
      ILabel true_label;
      IMov (Reg RAX, const_true);
      IJmp (Label logic_done_label);
      ILabel false_label;
      IMov (Reg RAX, const_false);
      ILabel logic_done_label;
      ILineComment (sprintf "END and#%d   -------------" t) ]
;;

(* Helper for boolean or *)
let or_prim2 (e1 : arg) (e2 : arg) ((t, _) : tag) : instruction list =
  let true_label = sprintf "true#%d" t in
  let false_label = sprintf "false#%d" t in
  let logic_done_label = sprintf "or_done#%d" t in
  [ ILineComment (sprintf "BEGIN and#%d -------------" t);
    (* Move the first arg into RAX so we can type-check it. *)
    IMov (Reg RAX, e1) ]
  @ check_bool not_a_bool_logic_label
    (* In order to handle short-circuiting, we don't look at the second arg until later.
     * This means that `true or 5` will NOT raise a type error.
     *)
  @ [ IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJnz (Label true_label);
      IMov (Reg RAX, e2) ]
  @ check_bool not_a_bool_logic_label
  @ [ (* Need to re-set scratch_reg since it gets changed in check_bool.*)
      IMov (Reg scratch_reg, bool_mask);
      ITest (Reg RAX, Reg scratch_reg);
      IJnz (Label true_label);
      ILabel false_label;
      IMov (Reg RAX, const_false);
      IJmp (Label logic_done_label);
      ILabel true_label;
      IMov (Reg RAX, const_true);
      ILabel logic_done_label;
      ILineComment (sprintf "END or#%d   -------------" t) ]
;;

(*  ==================================================================================== *)
(*  ==================================================================================== *)

let rec replicate x i =
  if i = 0 then
    []
  else
    x :: replicate x (i - 1)

and reserve size tag =
  let ok = sprintf "$memcheck_%d" tag in
  [ IInstrComment
      (IMov (Reg RAX, LabelContents "?HEAP_END"), sprintf "Reserving %d words" (size / word_size));
    ISub (Reg RAX, Const (Int64.of_int size));
    ICmp (Reg RAX, Reg heap_reg);
    IJge (Label ok) ]
  @ native_call (Label "?try_gc")
      [ Sized (QWORD_PTR, Reg heap_reg);
        (* alloc_ptr in C *)
        Sized (QWORD_PTR, Const (Int64.of_int size));
        (* bytes_needed in C *)
        Sized (QWORD_PTR, Reg RBP);
        (* first_frame in C *)
        Sized (QWORD_PTR, Reg RSP) (* stack_top in C *) ]
  @ [ IInstrComment
        ( IMov (Reg heap_reg, Reg RAX),
          "assume gc success if returning here, so RAX holds the new heap_reg value" );
      ILabel ok ]

and compile_fun
    name
    args
    (body : tag aexpr)
    (env_env : arg name_envt name_envt)
    tag
    si
    free_var_offsets : instruction list * instruction list * instruction list =
  (* Debug instruction that terminates the program *)
  let env = safe_find_opt name env_env ~callee_tag:(sprintf "COMPILE_FUN! id: %s" name) in
  let fun_label = name in
  let after_label = name ^ "_end" in
  let acexp = ACExpr (CLambda (args, body, get_tag_A body)) in
  let vars = deepest_stack env in
  let arity = List.length args in
  let free_vars = StringSet.elements (free_vars acexp) in
  (* The order we get these out of the set is not the same as their order on the stack. *)
  let num_free = List.length free_vars in
  let load_closure =
    List.concat
      (List.mapi
         (fun i (arg : arg) ->
           match arg with
           (* Handles self-reference by tagging the heap pointer with the closure tag.
            * This works because we know that this closure will be on the top of the heap at this given moment.
            *)
           | Reg heap_reg ->
               [ IMov (Reg RAX, arg);
                 IAdd (Reg RAX, Const closure_tag);
                 IMov (Sized (QWORD_PTR, RegOffset (i + 3, heap_reg)), Reg RAX) ]
           | _ ->
               [ IMov (Sized (QWORD_PTR, Reg RAX), arg);
                 IMov (Sized (QWORD_PTR, RegOffset (i + 3, heap_reg)), Reg RAX) ] )
         free_var_offsets )
  in
  let stack_padding =
    if vars mod 2 = 1 then
      vars + 1
    else
      vars
  in
  let _, _, unpack_closure_instrs, new_env =
    (* This fold needs two counters, so it can't just be a mapi.
     * i: The index in the closure
     * j: The offset from RBP, where we will move the variable.
     *)
    List.fold_left
      (fun (i, j, acc_instrs, old_env) id ->
        if name = id then
          (i, j, acc_instrs, old_env)
        else
          let offset = RegOffset (j, RBP) in
          ( (* Advance to the next word in the closure *)
            i + 1,
            (* Move up to the next slot above RBP *)
            j - 1,
            (* At this point in time, the closure pointer
             * should be stored in the scratch register. *)
            IInstrComment (IMov (Reg RAX, RegOffset (i, scratch_reg)), sprintf "moving: %s" id)
            (* Grab the closure ptr*)
            :: IMov (offset, Reg RAX) (* Put it where it belongs*)
            :: acc_instrs,
            update_envt_envt name id offset old_env ) )
      (* Start the index at 3 to skip the metadata words. *)
      (3, ~-1, [], env_env)
      free_vars
  in
  let heap_padding =
    ( if (4 + arity) mod 2 == 0 then
        8 + arity
      else
        8 + arity + 1 )
    * word_size
  in
  let gc =
    (* Need to push allocated registers onto the stack in order to garbage collect them. *)
    let gc_setup = List.rev_map (fun r -> IPush r) colors in
    let gc_body = reserve heap_padding tag in
    let gc_teardown = List.map (fun r -> IPop r) colors in
    gc_setup @ gc_body @ gc_teardown
  in
  (* reserve heap_padding tag in *)
  let stack_size = Int64.of_int (word_size * (2 + stack_padding)) in
  let prelude =
    [IJmp (Label after_label); ILabel fun_label; IPush (Reg RBP); IMov (Reg RBP, Reg RSP)]
  in
  let load_closure_setup =
    [ ILineComment "=== Load closure values ===";
      (* Convert the `arity` and the `num_free` to be SNALVALs *)
      IInstrComment
        ( IMov (Sized (QWORD_PTR, RegOffset (0, heap_reg)), Const (Int64.of_int (arity * 2))),
          "Arity in SNAKEVAL" );
      IInstrComment
        ( ILea (Reg scratch_reg, RelLabel fun_label),
          "Load the address of the function label into scratch reg" );
      IInstrComment
        ( IMov (Sized (QWORD_PTR, RegOffset (1, heap_reg)), Reg scratch_reg),
          "Load the func address into the 1st offset of the heap" );
      IInstrComment
        ( IMov (Sized (QWORD_PTR, RegOffset (2, heap_reg)), Const (Int64.of_int (num_free * 2))),
          "Load the number of free vars into the 2nd offset of the heap (as a SNAKEVAL)" ) ]
  in
  let compiled_body = compile_aexpr body si new_env (List.length args) false name in
  let stack_cleanup =
    [ILineComment "=== Stack clean-up ==="; IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet]
  in
  let bump_heap =
    [ ILineComment "===========================";
      ILineComment "===== Begin Bump Heap =====";
      IMov (Reg RAX, Reg heap_reg);
      IInstrComment (IAdd (Reg RAX, Const closure_tag), "Add on the closure tag");
      IInstrComment (IAdd (Reg heap_reg, Const (Int64.of_int heap_padding)), "Pad the heap");
      ILineComment "====== End Bump Heap ======" ]
  in
  let rsi_push_done_label = sprintf "rsi_push_done#%d" tag in
  let rdi_push_done_label = sprintf "rdi_push_done#%d" tag in
  let perform_rdi_push = sprintf "perform_rdi_push#%d" tag in
  let rsi_push =
    [ ICmp (Reg RSI, Const 0L);
      IJe (Label rsi_push_done_label);
      IMov (RegOffset (3, RBP), Reg RSI);
      ILabel rsi_push_done_label ]
  in
  ( prelude,
    [ ILineComment "=== Unpacking closure ===";
      (* Boost RSP to make room for closed vars *)
      ISub (Reg RSP, Const (Int64.of_int (num_free * word_size)))
      (* The scratch reg is going to hold the tuple pointer.
       * (i.e. the implicit first argument)
       * This means that we can't mangle it!
       *) ]
    @ [ ICmp (Reg RSI, Const 0L);
        IJne (Label perform_rdi_push);
        IMov (Reg scratch_reg, RegOffset (2, RBP));
        ISub (Reg scratch_reg, Const closure_tag);
        IJmp (Label rdi_push_done_label);
        ILabel perform_rdi_push;
        IMov (Reg scratch_reg, Reg RDI);
        ISub (Reg scratch_reg, Const closure_tag);
        ILabel rdi_push_done_label ]
    @ unpack_closure_instrs
    @ [ ILineComment "=====================";
        ISub (Reg RSP, Const stack_size);
        IMov (RegOffset (0, RSP), Reg RDI) ]
    @ rsi_push
    @ [ILineComment "=== Function call ==="]
    @ compiled_body
    @ stack_cleanup
    @ [ILabel after_label]
    @ check_memory (Int64.of_int heap_padding)
    @ gc
    @ load_closure_setup
    @ load_closure,
    bump_heap )

and args_help args regs =
  match (args, regs) with
  | arg :: args, reg :: regs -> IMov (Sized (QWORD_PTR, Reg reg), arg) :: args_help args regs
  | args, [] -> List.rev_map (fun arg -> IPush arg) args
  | [], _ -> []

and native_call label args =
  (* We know that on entry to every function, RSP is 16-byte aligned.
     We know that every frame is a multiple of 16 bytes.
     The call instruction pushes one return pointer onto the stack.
     The first thing we do is push RBP onto the stack
     So, we add 8 bytes of padding IFF the number of spilled args is *ODD*.
  *)
  let num_stack_args = max (List.length args - 6) 0 in
  let padding_needed = num_stack_args mod 2 <> 0 in
  let setup =
    ( if padding_needed then
        [IInstrComment (IPush (Sized (QWORD_PTR, Const 0L)), "Padding to 16-byte alignment")]
      else
        [] )
    @ args_help args first_six_args_registers
  in
  let teardown =
    ( if num_stack_args = 0 then
        []
      else
        [ IInstrComment
            ( IAdd (Reg RSP, Const (Int64.of_int (word_size * num_stack_args))),
              sprintf "Popping %d arguments" num_stack_args ) ] )
    @
    if padding_needed then
      [IInstrComment (IAdd (Reg RSP, Const (Int64.of_int word_size)), "Unpadding one word")]
    else
      []
  in
  setup @ [ICall label] @ teardown

and call (closure : arg) args =
  let closure_to_rax = [IMov (Reg RAX, closure)] in
  (* Step 1: Ensure that `closure` is actually a closure. *)
  let closure_check = check_tag (Reg RAX) closure_tag not_a_closure_label in
  (* Step 2: Check the arity. *)
  let call_arity = List.length args in
  let arity_check =
    (* Arity_check will result in an untagged heap ptr in R11. *)
    [ IMov (Reg scratch_reg, Reg RAX);
      untag_snakeval (Reg scratch_reg);
      (* Note that we multiply the caller arity by two, since closures store a snakeval. *)
      ICmp (Sized (QWORD_PTR, RegOffset (0, scratch_reg)), Const (Int64.of_int (2 * call_arity)));
      IJne (Label err_arity_mismatch_label) ]
  in
  let push_args =
    List.rev_map
      (fun arg ->
        match arg with
        | Sized _ -> IPush arg
        | _ -> IPush (Sized (QWORD_PTR, arg)) )
      args
  in
  let push_closure = [IPush (Sized (QWORD_PTR, closure))] in
  let make_the_call = [untag_snakeval (Reg RAX); ICall (RegOffset (1, RAX))] in
  let teardown =
    if call_arity = 0 then
      []
    else
      [ IInstrComment
          ( IAdd (Reg RSP, Const (Int64.of_int (word_size * (call_arity + 1)))),
            sprintf "Popping %d arguments" call_arity ) ]
  in
  [ILineComment "=== Begin func call ==="]
  @ [IMov (Reg RSI, Const 0L)]
  @ closure_to_rax (* Move closure into RAX*) @ closure_check (* Don't change RAX *)
  @ arity_check (* Untags RAX *) @ push_args (* *)
  @ push_closure (* Push thre original, TAGGED, closure val. *)
  @ make_the_call (* Calls the code ptr at [RAX+8] *)
  @ teardown (* Moves the stack top down by # args + 1, to account for the closure push *)

and compile_aexpr
    (e : tag aexpr)
    (si : int)
    (env_env : arg name_envt name_envt)
    (num_args : int)
    (is_tail : bool)
    (env_name : string) : instruction list =
  match e with
  | ALet (id, (CLambda (args, fun_body, ((tag, _) : tag)) as lambda), let_body, _) ->
      let cur_env =
        safe_find_opt env_name env_env
          ~callee_tag:(sprintf "COMPILE_AEXPR! ALet1. env_name: %s" env_name)
      in
      let prelude =
        (* Since we're stepping into the body of a lambda, we set the env_name to the current id. *)
        let free = StringSet.elements @@ free_vars (ACExpr lambda) in
        let free_locations = List.map (fun v -> safe_find_opt v cur_env) free in
        let a, b, c = compile_fun id args fun_body env_env tag si free_locations in
        a @ b @ c
      in
      let offset =
        safe_find_opt id cur_env
          ~callee_tag:
            (sprintf "COMPILE_AEXPR! Alet1. id: %s, env: %s" id (string_of_name_envt cur_env))
      in
      let updated_env_env = update_envt_envt env_name id offset env_env in
      let body = compile_aexpr let_body si updated_env_env num_args is_tail env_name in
      [ILineComment "=== Compile ALet Aexpr ==="]
      @ prelude
      @ [IMov (offset, Reg RAX)]
      @ body
      @ [ILineComment "== End Compile ALet Aexpr =="]
  | ALet (id, bound, body, _) ->
      let cur_env =
        safe_find_opt env_name env_env
          ~callee_tag:(sprintf "COMPILE_AEXPR! Alet2. env_name: %s" env_name)
      in
      let prelude = compile_cexpr bound si env_env num_args false env_name in
      let body = compile_aexpr body si env_env num_args is_tail env_name in
      let offset =
        safe_find_opt id cur_env
          ~callee_tag:
            (sprintf "COMPILE_AEXPR! Alet2. id: %s, env: %s" id (string_of_name_envt cur_env))
      in
      prelude @ [IMov (offset, Reg RAX)] @ body
  | ALetRec ([(id, (CLambda (args, fun_body, ((tag, _) : tag)) as lambda))], let_body, _) ->
      let current_env = safe_find_opt env_name env_env in
      let offset =
        safe_find_opt id current_env
          ~callee_tag:
            (sprintf "COMPILE_AEXPR! Aletrec1. id: %s, env: %s" id (string_of_name_envt current_env))
      in
      let prelude =
        (* Since we're stepping into the body of a lambda, we set the env_name to the current id. *)
        let free = StringSet.elements @@ free_vars (ACExpr lambda) in
        let free_locations = List.map (fun v -> safe_find_opt v current_env) free in
        let fun_prelude, fun_body, fun_heap_bump =
          compile_fun id args fun_body env_env tag si free_locations
        in
        fun_prelude @ fun_body @ fun_heap_bump
      in
      let body = compile_aexpr let_body si env_env num_args is_tail env_name in
      [ILineComment "=== Compile ALetRec Aexpr ==="]
      @ [ IMov (Sized (QWORD_PTR, offset), Reg heap_reg);
          IAdd (Sized (QWORD_PTR, offset), Const closure_tag) ]
      @ prelude
      @ [IMov (offset, Reg RAX)]
      @ body
      @ [ILineComment "== End Compile ALetRec Aexpr =="]
  | ALetRec (bindings, body, _) ->
      let current_env = safe_find_opt env_name env_env in
      let bindings_instr =
        List.concat
          (List.map
             (fun (id, assign_val) ->
               let new_env = update_envt_envt env_name id (Reg heap_reg) env_env in
               let compiled_assign_val =
                 compile_cexpr assign_val si new_env num_args is_tail env_name
               in
               let stack_idx =
                 match find_opt current_env id with
                 | None -> raise (InternalCompilerError (sprintf "Cannot find %s in environment" id))
                 | Some si -> si
               in
               [ILineComment (sprintf "making lambda for %s" id)]
               @ compiled_assign_val
               @ [IMov (stack_idx, Reg RAX)] )
             bindings )
      in
      let body = compile_aexpr body si env_env num_args is_tail env_name in
      bindings_instr @ body
  | ASeq (first, next, _) ->
      let compiled_first = compile_cexpr first si env_env num_args is_tail env_name in
      let compiled_next = compile_aexpr next si env_env num_args is_tail env_name in
      compiled_first @ compiled_next
  | ACExpr cexp -> compile_cexpr cexp si env_env num_args is_tail env_name

and compile_cexpr (e : tag cexpr) si (env_env : arg name_envt name_envt) num_args is_tail env_name =
  match e with
  | CImmExpr immexp ->
      let compiled_immexp = compile_imm immexp env_env env_name in
      [IMov (Reg scratch_reg, compiled_immexp); IMov (Reg RAX, Reg scratch_reg)]
  | CIf (cond, thn, els, ((t, _) : tag)) ->
      let else_label = sprintf "if_else#%d" t in
      let done_label = sprintf "if_done#%d" t in
      (let cond_reg = compile_imm cond env_env env_name in
       [ILineComment (sprintf "BEGIN conditional#%d   -------------" t); IMov (Reg RAX, cond_reg)]
       @ check_bool not_a_bool_if_label
       @ [ IMov (Reg scratch_reg, bool_mask);
           ITest (Reg RAX, Reg scratch_reg);
           IJz (Label else_label);
           ILineComment "  Then case:" ]
       @ compile_aexpr thn si env_env num_args is_tail env_name
       @ [IJmp (Label done_label); ILineComment "  Else case:"; ILabel else_label]
       @ compile_aexpr els si env_env num_args is_tail env_name )
      @ [ILabel done_label; ILineComment (sprintf "END conditional#%d     -------------" t)]
  | CPrim1 (op, e, ((t, s) : tag)) -> (
      let e_reg = compile_imm e env_env env_name in
      match op with
      | Add1 ->
          (IMov (Reg RAX, e_reg) :: check_num not_a_number_arith_label)
          @ [IAdd (Reg RAX, Const 2L); check_overflow]
      | Sub1 ->
          (IMov (Reg RAX, e_reg) :: check_num not_a_number_arith_label)
          @ [IAdd (Reg RAX, Const (-2L)); check_overflow]
      (* `xor` can't take a 64-bit literal, *)
      | Not ->
          (IMov (Reg RAX, e_reg) :: check_bool not_a_bool_logic_label)
          @ [IMov (Reg scratch_reg, bool_mask); IXor (Reg RAX, Reg scratch_reg)]
      | IsBool ->
          let false_label = sprintf "is_bool_false#%d" t in
          let done_label = sprintf "is_bool_done#%d" t in
          [ILineComment (sprintf "BEGIN is_bool%d -------------" t); IMov (Reg RAX, e_reg)]
          @ check_bool false_label
          @ [ IMov (Reg RAX, const_true);
              IJmp (Label done_label);
              ILabel false_label;
              IMov (Reg RAX, const_false);
              ILabel done_label;
              ILineComment (sprintf "END is_bool%d   -------------" t) ]
      | IsNum ->
          let false_label = sprintf "is_num_false#%d" t in
          let done_label = sprintf "is_num_done#%d" t in
          [ILineComment (sprintf "BEGIN is_num%d -------------" t); IMov (Reg RAX, e_reg)]
          @ check_num false_label
          @ [ IMov (Reg RAX, const_true);
              IJmp (Label done_label);
              ILabel false_label;
              IMov (Reg RAX, const_false);
              ILabel done_label;
              ILineComment (sprintf "END is_num%d   -------------" t) ]
      | Print ->
          [ (* Print both passes its value to the external function, and returns it. *)
            IMov (Reg RDI, e_reg);
            ICall (Label "?print") (* The answer goes in RAX :) *) ]
      | IsTuple ->
          let false_label = sprintf "is_tuple_false#%d" t in
          let done_label = sprintf "is_tuple_done#%d" t in
          [ILineComment (sprintf "BEGIN is_tuple%d -------------" t); IMov (Reg RAX, e_reg)]
          @ check_tuple false_label
          @ check_not_nil false_label
          @ [ IMov (Reg RAX, const_true);
              IJmp (Label done_label);
              ILabel false_label;
              IMov (Reg RAX, const_false);
              ILabel done_label;
              ILineComment (sprintf "END is_tuple%d   -------------" t) ]
      | PrintStack ->
          [ ILineComment "===== Printing Stack =====";
            IMov (Reg RDI, Const 1L);
            IMov (Reg RSI, Reg RSP);
            IMov (Reg RDX, Reg RBP);
            IAdd (Reg RDX, Const 16L);
            IMov (Reg RCX, Const 0L);
            IMov (Reg scratch_reg, RelLabel heap_end_label);
            ICall (Label "?print_stack");
            ILineComment "=== End Printing Stack ===" ]
      | Crash -> [IJmp (Label crash_label)]
      | Raise ->
          [ ILineComment "== Raising an exception ==";
            IMov (Reg RDI, e_reg);
            ICall (Label "?ex_raise");
            ILineComment "==========================" ]
      | ReportTestPass -> [ICall (Label "?report_pass")]
      | ReportTestFailException ->
          load_sourcespan s first_six_args_registers @ [ICall (Label "?report_fail_exception")] )
  | CPrim2 (op, e1, e2, ((_, s) as t)) -> (
      let e1_reg = compile_imm e1 env_env env_name in
      let e2_reg = compile_imm e2 env_env env_name in
      match op with
      | Plus | Minus | Times -> arithmetic_prim2 op e1_reg e2_reg
      | Greater | GreaterEq | Less | LessEq -> compare_prim2 op e1_reg e2_reg t
      | And -> and_prim2 e1_reg e2_reg t
      | Or -> or_prim2 e1_reg e2_reg t
      | Eq ->
          let true_label = sprintf "equal#%d" (fst t) in
          let done_label = sprintf "equal_done#%d" (fst t) in
          (* No typechecking for Eq. We can just see if the two values are equivalent. *)
          [ IMov (Reg RAX, e1_reg);
            IMov (Reg scratch_reg, e2_reg);
            ICmp (Reg RAX, Reg scratch_reg);
            IJe (Label true_label);
            IMov (Reg RAX, const_false);
            IJmp (Label done_label);
            ILabel true_label;
            IMov (Reg RAX, const_true);
            ILabel done_label ]
      | CheckSize ->
          (* Check that the tuple `e1` has size `e2`.
           * We don't have to type-check these since:
           * - By the time we evaluate a CheckSize, we have already guaranteed that e1 is a tuple
           * - We create CheckSize during desugaring, and we only ever make `e2` an ENumber.
           *)
          [ IMov (Reg RAX, e1_reg);
            IMov (Reg scratch_reg, RegOffset (0, RAX));
            IMov (Reg RAX, e2_reg);
            ISar (Reg RAX, Const 1L);
            ICmp (Reg scratch_reg, Reg RAX);
            IMul (Reg RAX, Const 2L);
            (* Note that RAX stores the expected arity. *)
            IJne (Label err_unpack_err_label) ]
      | ReportTestFailMismatch ->
          let first = List.nth first_six_args_registers 0 in
          let second = List.nth first_six_args_registers 1 in
          let rest = drop first_six_args_registers 2 in
          [IMov (Sized (QWORD_PTR, Reg first), e1_reg); IMov (Sized (QWORD_PTR, Reg second), e2_reg)]
          @ load_sourcespan s rest
          @ [ICall (Label "?report_fail")] )
  | CLambda _ -> raise (InternalCompilerError "Encountered an un-bound CLambda!")
  | CApp (callee, args, Snake, _) ->
      let compiled_closure = compile_cexpr (CImmExpr callee) si env_env num_args is_tail env_name in
      let compiled_args = List.map (fun arg -> compile_imm arg env_env env_name) args in
      (ILineComment "~~~~~~~~~~" :: compiled_closure) @ call (Reg RAX) compiled_args
  | CApp (callee, args, Native, _) -> (
    match callee with
    | ImmId (id, _) -> (
        let name = List.hd (String.split_on_char '_' id) in
        match name with
        | "input" -> [ICall (Label "?input")]
        | "equal" ->
            let comp_args = List.map (fun arg -> compile_imm arg env_env env_name) args in
            native_call (Label "?equal") comp_args
        | _ -> raise (InternalCompilerError (sprintf "Unsupported function: %s" name)) )
    | _ ->
        raise
          (InternalCompilerError
             (sprintf "Invariant violation: Native functions must be an ImmId but got: %s"
                (string_of_immexpr callee) ) ) )
  | CApp (_, _, call_type, _) ->
      raise
        (InternalCompilerError
           (sprintf "CApp with non-Snake and non-Native call-type. Got: %s"
              (string_of_call_type call_type) ) )
  | CTuple (items, ((tag, _) : tag)) ->
      let n = List.length items in
      (* expected: (1, 2, 3, 5)
       * but got: forwarding to 0x4
       * Pain.
       * To avoid this, we make tuples and closures hold snakevals for their metadata.
       *)
      let n_snake = Int64.of_int (2 * n) in
      let heap_size = Int64.of_int (word_size * (n + 1)) in
      (* This is a gross way to do this and I'm sorry. *)
      let heap_bump_amt, heap_bump_amt_int =
        if n mod 2 == 0 then
          (Int64.of_int word_size, word_size)
        else
          (0L, 0)
      in
      let gc =
        (* Need to push allocated registers onto the stack in order to garbage collect them. *)
        let gc_setup = List.rev_map (fun r -> IPush r) colors in
        let gc_body = reserve heap_bump_amt_int tag in
        let gc_teardown = List.map (fun r -> IPop r) colors in
        gc_setup @ gc_body @ gc_teardown
      in
      let loading_instrs =
        List.concat
        @@ List.mapi
             (fun i item ->
               move_with_scratch (RegOffset (i + 1, R15)) (compile_imm item env_env env_name) )
             items
      in
      ILineComment "=== Begin tuple initialization ==="
      :: move_with_scratch (RegOffset (0, R15)) (HexConst n_snake)
      @ loading_instrs
      @ gc
      @ check_memory heap_size
      @ [ IMov (Reg RAX, Reg R15);
          IAdd (Reg RAX, Const 1L);
          IAdd (Reg R15, Const heap_size);
          IInstrComment (IAdd (Reg R15, Const heap_bump_amt), "8 if even items, 0 if odd") ]
      @ [ILineComment "==== End tuple initialization ===="]
  | CGetItem (tup, idx, _) ->
      let tup_reg = compile_imm tup env_env env_name in
      let idx_reg = compile_imm idx env_env env_name in
      [ILineComment "==== Begin get-item ===="; IMov (Reg RAX, tup_reg)]
      @ check_tuple not_a_tuple_access_label
      @ [IMov (Reg RAX, tup_reg)]
      @ check_not_nil nil_deref_label
      @ [IMov (Reg RAX, idx_reg)]
      @ check_num not_a_number_index_label
      @ [ IMov (Reg RAX, tup_reg);
          ISub (Reg RAX, Const tuple_tag);
          IMov (Reg R11, idx_reg);
          ICmp (Reg R11, Reg RAX);
          IJge (Label index_high_label);
          IShr (Reg R11, Const 1L);
          ICmp (Reg R11, Const 0L);
          IJl (Label index_low_label);
          IMov (Reg RAX, Sized (QWORD_PTR, RegOffsetReg (RAX, R11, word_size, word_size)));
          ILineComment "Multiply the value in R11 by 8 with no further offset" ]
      @ move_with_scratch (Reg RAX) (RegOffsetReg (RAX, R11, word_size, word_size))
      @ [ILineComment "===== End get-item ====="]
  | CSetItem (tup, idx, value, _) ->
      let tup_reg = compile_imm tup env_env env_name in
      let idx_reg = compile_imm idx env_env env_name in
      let val_reg = compile_imm value env_env env_name in
      let tuple_slot_offset = RegOffsetReg (RAX, R11, word_size, word_size) in
      [ILineComment "==== Begin set-item ===="; IMov (Reg RAX, tup_reg)]
      @ check_tuple not_a_tuple_access_label
      @ [IMov (Reg RAX, tup_reg)]
      @ check_not_nil nil_deref_label
      @ [IMov (Reg RAX, idx_reg)]
      @ check_num not_a_number_index_label
      @ [ IMov (Reg RAX, tup_reg);
          ISub (Reg RAX, Const tuple_tag);
          IMov (Reg R11, idx_reg);
          ICmp (Reg R11, Reg RAX);
          IJge (Label index_high_label);
          IShr (Reg R11, Const 1L);
          ICmp (Reg R11, Const 0L);
          IJl (Label index_low_label);
          IMov (Reg scratch_reg2, val_reg);
          IInstrComment
            ( IMov (tuple_slot_offset, Reg scratch_reg2),
              "Store the location of the relevant value in RAX" );
          IMov (Reg RAX, Reg scratch_reg2);
          ILineComment "===== End set-item =====" ]
  | CTryCatch (try_block, except, catch_block, tag) ->
      (* 1. Add the exception handler *)
      (* 2. Call the try function *)
      (*    - CASE 1: Smooth Exit *)
      (*        3. Pop the exception handler *)
      (*        4. Jump to the end label *)
      (*    - CASE 2: Non-smooth Exit *)
      (*        3. We have a raise call and it will check if there is any handler left on the 
       *           stack, if so, it will RETURN the exception, if not, it will THROW the exception *)
      (*        4. We will jump to the catch label. NOTE: the above will have returned the exception,
       *           and as such, it will be in RAX for the equality check within the catch block *)
      let compiled_try = compile_imm try_block env_env env_name in
      let compiled_catch = compile_imm catch_block env_env env_name in
      let excptn = ImmExcept (except, tag) in
      let exception_arg = compile_imm excptn env_env env_name in
      native_call (Label "?try_catch") [compiled_try; compiled_catch; exception_arg]
  | CTestOp2 (given, expected, _, _, _) ->
      (* Naive implementation! No error checking *)
      let given_reg = compile_imm given env_env env_name in
      let expected_reg = compile_imm expected env_env env_name in
      [ IMov (Reg RSI, given_reg);
        IMov (Reg RDI, expected_reg);
        ICall (Label "?equal");
        ICmp (Sized (QWORD_PTR, Reg RAX), const_true) ]
  (* We made these ANF types before we realized we do not need them... Oops! *)
  | CCheck _ -> raise (InternalCompilerError "CCheck Desugared away")
  | CTestOp1 _ -> raise (InternalCompilerError "CTestOp1 Desugared away")
  | CTestOp2Pred _ -> raise (InternalCompilerError "CTestOp2Pred Desugared away")

and compile_imm e (env_env : arg name_envt name_envt) env_name =
  match e with
  | ImmNum (n, _) -> Const (Int64.shift_left n 1)
  | ImmBool (true, _) -> const_true
  | ImmBool (false, _) -> const_false
  | ImmId (x, _) -> get_nested env_name x env_env
  | ImmNil _ -> Const tuple_tag
  | ImmExcept (ex, _) -> (
    match ex with
    | Runtime -> runtime_exception
    | Value -> value_exception )
;;

(* This function can be used to take the native functions and produce DFuns whose bodies
   simply contain an EApp (with a Native call_type) to that native function.  Then,
   your existing compilation can turn these DFuns into ELambdas, which can then be called
   as in the rest of Fer-De-Lance, but the Native EApps will do the work of actually
   native_calling the runtime-provided functions. *)
let add_native_lambdas (p : sourcespan program) =
  let wrap_native name arity =
    let argnames = List.init arity (fun i -> sprintf "%s_arg_%d" name i) in
    [ DFun
        ( name,
          List.map (fun name -> BName (name, false, dummy_span)) argnames,
          EApp
            ( EId (name, dummy_span),
              List.map (fun name -> EId (name, dummy_span)) argnames,
              Native,
              dummy_span ),
          dummy_span ) ]
  in
  match p with
  | Program (declss, body, checks, tag) ->
      Program
        ( StringMap.fold
            (fun name (_, arity, _) declss ->
              match arity with
              | Some a -> wrap_native name a :: declss
              | _ -> raise (InternalCompilerError "All native functions require arity") )
            native_fun_bindings declss,
          body,
          checks,
          tag )
;;

let error_suffix =
  List.fold_left
    (fun asm (label, instrs) -> asm ^ sprintf "%s:%s\n" label instrs)
    "\n"
    [ ( not_a_number_comp_label,
        to_asm (native_call (Label "?error") [Const err_COMP_NOT_NUM; Reg scratch_reg]) );
      ( not_a_number_arith_label,
        to_asm (native_call (Label "?error") [Const err_ARITH_NOT_NUM; Reg scratch_reg]) );
      ( not_a_bool_logic_label,
        to_asm (native_call (Label "?error") [Const err_LOGIC_NOT_BOOL; Reg scratch_reg]) );
      ( not_a_bool_if_label,
        to_asm (native_call (Label "?error") [Const err_IF_NOT_BOOL; Reg scratch_reg]) );
      (overflow_label, to_asm (native_call (Label "?error") [Const err_OVERFLOW; Reg RAX]));
      ( not_a_tuple_access_label,
        to_asm (native_call (Label "?error") [Const err_GET_NOT_TUPLE; Reg scratch_reg]) );
      ( not_a_number_index_label,
        to_asm (native_call (Label "?error") [Const err_INDEX_NOT_NUM; Reg scratch_reg]) );
      ( index_low_label,
        to_asm (native_call (Label "?error") [Const err_GET_LOW_INDEX; Reg scratch_reg]) );
      (index_high_label, to_asm (native_call (Label "?error") [Const err_GET_HIGH_INDEX]));
      (nil_deref_label, to_asm (native_call (Label "?error") [Const err_NIL_DEREF; Reg scratch_reg]));
      ( err_out_of_memory_label,
        to_asm (native_call (Label "?error") [Const err_OUT_OF_MEMORY; Reg scratch_reg]) );
      ( not_a_closure_label,
        to_asm (native_call (Label "?error") [Const err_CALL_NOT_CLOSURE; Reg scratch_reg]) );
      ( err_arity_mismatch_label,
        to_asm (native_call (Label "?error") [Const err_CALL_ARITY_ERR; Reg scratch_reg]) );
      (crash_label, to_asm (native_call (Label "?error") [Const err_CRASH])) ]
;;

let compile_prog (anfed, (env : arg name_envt name_envt)) =
  let prelude =
    "section .text\n\
     extern ?error\n\
     extern ?input\n\
     extern ?print\n\
     extern ?print_stack\n\
     extern ?equal\n\
     extern ?try_gc\n\
     extern ?naive_print_heap\n\
     extern ?HEAP\n\
     extern ?HEAP_END\n\
     extern ?ex_raise\n\
     extern ?set_stack_bottom\n\
     extern ?report_pass\n\
     extern ?report_fail\n\
     extern ?report_fail_exception\n\
     extern ?try_catch\n\
     global " ^ ocsh_name
  in
  let suffix = error_suffix in
  match anfed with
  | AProgram (body, ((tag, _) : tag)) ->
      (* $heap and $size are mock parameter names, just so that compile_fun knows our_code_starts_here takes in 2 parameters *)
      let prologue, comp_main, epilogue =
        compile_fun ocsh_name ["$heap"; "$size"] body env tag 0 []
      in
      let heap_start =
        [ ILineComment "heap start";
          IInstrComment
            ( IMov (Sized (QWORD_PTR, Reg heap_reg), Reg (List.nth first_six_args_registers 0)),
              "Load heap_reg with our argument, the heap pointer" );
          IInstrComment
            ( IAdd (Sized (QWORD_PTR, Reg heap_reg), Const 15L),
              "Align it to the nearest multiple of 16" );
          IMov (Reg scratch_reg, HexConst 0xFFFFFFFFFFFFFFF0L);
          IInstrComment
            ( IAnd (Sized (QWORD_PTR, Reg heap_reg), Reg scratch_reg),
              "by adding no more than 15 to it" ) ]
      in
      let set_stack_bottom =
        [IMov (Reg R12, Reg RDI)]
        @ native_call (Label "?set_stack_bottom") [Reg RBP]
        @ [IMov (Reg RDI, Reg R12)]
      in
      let main = prologue @ set_stack_bottom @ heap_start @ comp_main @ epilogue in
      sprintf "%s%s%s\n" prelude (to_asm main) suffix
;;

let run_if should_run f =
  if should_run then
    f
  else
    no_op_phase
;;

let pick_alloc_strategy (strat : alloc_strategy) =
  match strat with
  | Naive -> naive_stack_allocation
  | Register -> register_allocation
;;

let compile_to_string
    ?(no_builtins = false)
    (alloc_strat : alloc_strategy)
    (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> add_err_phase well_formed is_well_formed
  |> run_if (not no_builtins) (add_phase add_natives add_native_lambdas)
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase locate_bindings (pick_alloc_strategy alloc_strat)
  |> add_phase result compile_prog
;;
