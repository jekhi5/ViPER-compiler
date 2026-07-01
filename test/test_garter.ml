open Test_funcs

(** Tests for Garter, Viper's garbage collection system. *)

let builtins_size =
  4 (* arity + 0 vars + codeptr + padding *)
  * 1 (* TODO FIXME (List.length Compile.native_fun_bindings) *)
;;

let oom =
  [ tgcerr "oomgc1" (7 + builtins_size) "(1, (3, 4))" "" "Out of memory";
    tgc "oomgc2" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
    tvgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
    tgc "oomgc4" (4 + builtins_size) "(3, 4)" "" "(3, 4)";
    tgcerr "oomgc5" (3 + builtins_size) "(1, 2, 3, 4, 5, 6, 7, 8, 9, 0)" "" "Allocation" ]
;;

let gc =
  [ tgc "gc_lam1" (10 + builtins_size)
      "let f = (lambda: (1, 2)) in\n\
      \       begin\n\
      \         f();\n\
      \         f();\n\
      \         f();\n\
      \         f()\n\
      \       end"
      "" "(1, 2)" ]
;;

let fvc =
  [ tfvsc "nested_lambda"
      "let \n\
      \    foo = (lambda(w, x, y, z):\n\
      \             (lambda(a): a + x + z))\n\
      \ in\n\
      \    foo(1, 2, 3, 4)(5)"
      (AProgram
         ( ALet
             ( "lam_5",
               CLambda
                 ( ["w"; "x"; "y"; "z"],
                   ALet
                     ( "lam_6",
                       CLambda
                         ( ["a"],
                           ALet
                             ( "binop_8",
                               CPrim2
                                 ( Plus,
                                   ImmId ("a", set ["a"]),
                                   ImmId ("x", set ["x"]),
                                   set ["x"; "a"] ),
                               ACExpr
                                 (CPrim2
                                    ( Plus,
                                      ImmId ("binop_8", set ["binop_8"]),
                                      ImmId ("z", set ["z"]),
                                      set ["z"; "binop_8"] ) ),
                               set ["a"; "x"; "z"] ),
                           set ["x"; "z"] ),
                       ACExpr (CImmExpr (ImmId ("lam_6", set ["lam_6"]))),
                       set ["x"; "z"] ),
                   empty_set ),
               ALet
                 ( "foo",
                   CImmExpr (ImmId ("lam_5", set ["lam_5"])),
                   ALet
                     ( "app_19",
                       CApp
                         ( ImmId ("?foo", set ["foo"]),
                           [ ImmNum (4L, empty_set);
                             ImmNum (3L, empty_set);
                             ImmNum (2L, empty_set);
                             ImmNum (1L, empty_set) ],
                           Snake,
                           set ["foo"] ),
                       ACExpr
                         (CApp
                            ( ImmId ("?app_19", set ["app_19"]),
                              [ImmNum (5L, empty_set)],
                              Snake,
                              set ["app_19"] ) ),
                       set ["foo"] ),
                   set ["lam_5"] ),
               empty_set ),
           empty_set ) );
    tfvsc "full_prog1" "let foo = true in foo"
      (AProgram
         ( ALet
             ( "foo",
               CImmExpr (ImmBool (true, empty_set)),
               ACExpr (CImmExpr (ImmId ("foo", set ["foo"]))),
               empty_set ),
           empty_set ) );
    tfvsc "full_prog2" "let foo = 1 in foo + bar"
      (AProgram
         ( ALet
             ( "foo",
               CImmExpr (ImmNum (1L, empty_set)),
               ACExpr
                 (CPrim2
                    ( Plus,
                      ImmId ("foo", set ["foo"]),
                      ImmId ("bar", set ["bar"]),
                      set ["foo"; "bar"] ) ),
               set ["bar"] ),
           set ["bar"] ) ) ]
;;

module Suite : TestSuite = struct
  let suite = oom @ gc @ fvc
end
