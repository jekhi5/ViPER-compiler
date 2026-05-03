open Assembly

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)
module TagMap = Map.Make (Int)

type 'a name_envt = 'a StringMap.t
type 'a tag_envt = 'a TagMap.t
type freevars = StringSet.t
type livevars = StringSet.t

let blank_stack_val = 0xDEFACED
let heap_end_label = "?HEAP_END"
let const_true = HexConst 0xFFFFFFFFFFFFFFFFL
let const_false = HexConst 0x7FFFFFFFFFFFFFFFL
let bool_mask = HexConst 0x8000000000000000L
let bool_tag = 0x0000000000000007L
let bool_tag_mask = 0x0000000000000007L
let num_tag = 0x0000000000000000L
let num_tag_mask = 0x0000000000000001L
let closure_tag = 0x0000000000000005L
let closure_tag_mask = 0x0000000000000007L
let tuple_tag = 0x0000000000000001L
let tuple_tag_mask = 0x0000000000000007L
let const_nil = HexConst tuple_tag
(* We are digging into the booleans here. 
 * 0011111... is representative of a runtime exception (like you tried to do addition with a boolean)
 * 0001111... is representative of a value based exception (raised by the user. Ex: illegal argument exception)
 *)
let runtime_exception = HexConst 0x3FFFFFFFFFFFFFFFL
let value_exception = HexConst 0x1FFFFFFFFFFFFFFFL

let err_COMP_NOT_NUM = 1L
let err_ARITH_NOT_NUM = 2L
let err_LOGIC_NOT_BOOL = 3L
let err_IF_NOT_BOOL = 4L
let err_OVERFLOW = 5L
let err_GET_NOT_TUPLE = 6L
let err_GET_LOW_INDEX = 7L
let err_GET_HIGH_INDEX = 8L
let err_NIL_DEREF = 9L
let err_OUT_OF_MEMORY = 10L
let err_SET_NOT_TUPLE = 11L
let err_SET_LOW_INDEX = 12L
let err_SET_HIGH_INDEX = 13L
let err_CALL_NOT_CLOSURE = 14L
let err_CALL_ARITY_ERR = 15L
let err_INDEX_NOT_NUM = 16L
(* We added a Prim1 that just crashes the program. *)
let err_CRASH = 99L
let crash_label = "?crash"

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos)

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]
let caller_saved_regs : arg list = [Reg RDI; Reg RSI; Reg RDX; Reg RCX; Reg R8; Reg R9; Reg R10]
let callee_saved_regs : arg list = [Reg R12; Reg R14; Reg RBX]
let heap_reg = R15
let scratch_reg = R11
let scratch_reg2 = R10

let not_a_number_comp_label = "?error_not_number_comp"
let not_a_number_arith_label = "?error_not_number_arith"
let not_a_bool_logic_label = "?error_not_bool_logic"
let not_a_bool_if_label = "?error_not_bool_if"
let overflow_label = "?error_overflow"
(* Errors for tuples *)
let not_a_tuple_access_label = "?error_not_tuple_access"
let not_a_number_index_label = "?error_not_number_index"
let index_high_label = "?error_get_high_index"
let index_low_label = "?error_get_low_index"
let nil_deref_label = "?error_nil_deref"
let err_call_not_closure_label = "?err_not_closure"
let err_arity_mismatch_label = "?err_arity_mismatch"
let err_unpack_err_label = "?err_unpack_err"
let err_out_of_memory_label = "?err_out_of_memory"
let unpack_err_label = "?err_unpack_err"
let not_a_closure_label = "?err_not_closure"
