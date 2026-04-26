open Printf

(* Abstract syntax of (a small subset of) x86 assembly instructions *)
let word_size = 8

type reg =
  | RAX
  | RSP
  | RBP
  | RSI
  | RDI
  | RDX
  | RCX
  | R8
  | R9
  | R10
  | R11
  | CL

type size =
  | QWORD_PTR
  | DWORD_PTR
  | WORD_PTR
  | BYTE_PTR

type arg =
  | Const of int64
  | HexConst of int64
  | Reg of reg
  | RegOffset of int * reg (* int is # words of offset *)
  | Sized of size * arg
  | LabelContents of string
  (* you may find this useful if developing locally on macOS
     for some of the extra credit, or in future assignments.
     Keep in mind we will run your assignments on the Khoury
     Linux VMs. *)
  | RelLabel of string

type instruction =
  | IMov of arg * arg
  | ILea of arg * arg (* like LabelContents above... *)
  | IAdd of arg * arg
  | ISub of arg * arg
  | IMul of arg * arg
  | ILabel of string
  | ICmp of arg * arg
  | IJo of string
  | IJe of string
  | IJne of string
  | IJl of string
  | IJle of string
  | IJg of string
  | IJge of string
  | IJmp of string
  | IJz of string
  | IJnz of string
  | IRet
  | IAnd of arg * arg
  | IOr of arg * arg
  | IXor of arg * arg
  | IShl of arg * arg
  | IShr of arg * arg
  | ISar of arg * arg
  | IPush of arg
  | IPop of arg
  | ICall of string
  | ITest of arg * arg
  | ILineComment of string
  | IInstrComment of instruction * string

let r_to_asm (r : reg) : string =
  match r with
  | RAX -> "RAX"
  | RSI -> "RSI"
  | RDI -> "RDI"
  | RCX -> "RCX"
  | RDX -> "RDX"
  | RSP -> "RSP"
  | RBP -> "RBP"
  | R8 -> "R8"
  | R9 -> "R9"
  | R10 -> "R10"
  | R11 -> "R11"
  | CL -> "CL"
;;

let rec arg_to_asm (a : arg) : string =
  match a with
  | Const n -> sprintf "%Ld" n
  | HexConst n -> sprintf "0x%Lx" n
  | Reg r -> r_to_asm r
  | RegOffset (n, r) ->
      if n >= 0 then
        sprintf "[%s+%d]" (r_to_asm r) (word_size * n)
      else
        sprintf "[%s-%d]" (r_to_asm r) (-1 * word_size * n)
  | Sized (size, a) ->
      sprintf "%s %s"
        ( match size with
        | QWORD_PTR -> "QWORD"
        | DWORD_PTR -> "DWORD"
        | WORD_PTR -> "WORD"
        | BYTE_PTR -> "BYTE" )
        (arg_to_asm a)
  | LabelContents s -> sprintf "[%s]" s
  | RelLabel s -> sprintf "[rel %s]" s
;;

let rec i_to_asm (i : instruction) : string =
  match i with
  | IMov (dest, value) -> sprintf "  mov %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | ILea (dest, value) -> sprintf "  lea %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IAdd (dest, to_add) -> sprintf "  add %s, %s" (arg_to_asm dest) (arg_to_asm to_add)
  | ISub (dest, to_sub) -> sprintf "  sub %s, %s" (arg_to_asm dest) (arg_to_asm to_sub)
  | IMul (dest, to_mul) -> sprintf "  imul %s, %s" (arg_to_asm dest) (arg_to_asm to_mul)
  | ICmp (left, right) -> sprintf "  cmp %s, %s" (arg_to_asm left) (arg_to_asm right)
  | ILabel name -> name ^ ":"
  | IJo label -> sprintf "  jo %s" label
  | IJe label -> sprintf "  je %s" label
  | IJne label -> sprintf "  jne %s" label
  | IJl label -> sprintf "  jl %s" label
  | IJle label -> sprintf "  jle %s" label
  | IJg label -> sprintf "  jg %s" label
  | IJge label -> sprintf "  jge %s" label
  | IJmp label -> sprintf "  jmp %s" label
  | IJz label -> sprintf "  jz %s" label
  | IJnz label -> sprintf "  jnz %s" label
  | IAnd (dest, value) -> sprintf "  and %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IOr (dest, value) -> sprintf "  or %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IXor (dest, value) -> sprintf "  xor %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IShl (dest, value) -> sprintf "  shl %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IShr (dest, value) -> sprintf "  shr %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | ISar (dest, value) -> sprintf "  sar %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IPush value -> sprintf "  push %s" (arg_to_asm value)
  | IPop dest -> sprintf "  pop %s" (arg_to_asm dest)
  | ICall label -> sprintf "  call %s" label
  | IRet -> "  ret"
  | ITest (arg, comp) -> sprintf "  test %s, %s" (arg_to_asm arg) (arg_to_asm comp)
  | ILineComment str -> sprintf "  ;; %s" str
  | IInstrComment (instr, str) -> sprintf "%s ; %s" (i_to_asm instr) str
;;

let to_asm (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (i_to_asm i)) "" is
;;
