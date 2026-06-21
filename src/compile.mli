open Exprs
open Phases
open Assembly

val compile_to_string :
  ?no_builtins:bool -> alloc_strategy -> sourcespan program pipeline -> string pipeline

val compile_prog : tag aprogram * arg name_envt name_envt -> string
