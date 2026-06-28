open Test_funcs

open Exprs

let parse_checks =
  [ tparse "single_check_spits" "1 check: 1 spits (lambda(x): 1) end"
      (Program
         ( [],
           ENumber (1L, ()),
           [ ECheck
               ( [ ETestOp2
                     ( ENumber (1L, ()),
                       ELambda ([BName ("x", false, ())], ENumber (1L, ()), ()),
                       DeepEq,
                       false,
                       () ) ],
                 () ) ],
           () ) );
    tparse "complex_check"
      "\n\
      \      true \n\
      \      \n\
      \      check: \n\
      \        let \n\
      \          a = 1, \n\
      \          b = 2 \n\
      \        in (a, b) \n\
      \        spits \n\
      \        (1, 2),\n\
      \        4 + true sheds RuntimeException,\n\
      \        let foo = (lambda(x, y): (x, y)) in foo(1, 2) !bites (1, 2),\n\
      \        \n\
      \        1 !spits 5\n\
      \      end\n\n\
      \      check: 1 broods (lambda(x): 1) end"
      (Program
         ( [],
           EBool (true, ()),
           [ ECheck
               ( [ ETestOp2
                     ( ELet
                         ( [ (BName ("a", false, ()), ENumber (1L, ()), ());
                             (BName ("b", false, ()), ENumber (2L, ()), ()) ],
                           ETuple ([EId ("a", ()); EId ("b", ())], ()),
                           () ),
                       ETuple ([ENumber (1L, ()); ENumber (2L, ())], ()),
                       DeepEq,
                       false,
                       () );
                   ETestOp2
                     ( EPrim2 (Plus, ENumber (4L, ()), EBool (true, ()), ()),
                       EException (Runtime, ()),
                       Raises,
                       false,
                       () );
                   ETestOp2
                     ( ELet
                         ( [ ( BName ("foo", false, ()),
                               ELambda
                                 ( [BName ("x", false, ()); BName ("y", false, ())],
                                   ETuple ([EId ("x", ()); EId ("y", ())], ()),
                                   () ),
                               () ) ],
                           EApp (EId ("?foo", ()), [ENumber (1L, ()); ENumber (2L, ())], Snake, ()),
                           () ),
                       ETuple ([ENumber (1L, ()); ENumber (2L, ())], ()),
                       ShallowEq,
                       true,
                       () );
                   ETestOp2 (ENumber (1L, ()), ENumber (5L, ()), DeepEq, true, ()) ],
                 () );
             ECheck
               ( [ ETestOp1
                     ( ENumber (1L, ()),
                       ELambda ([BName ("x", false, ())], ENumber (1L, ()), ()),
                       false,
                       () ) ],
                 () ) ],
           () ) );
    tparse "basic_try_catch" "try 1 catch RuntimeException as r in 1"
      (Program
         ( [],
           ETryCatch
             ( ENumber (1L, ()),
               BName ("r", false, ()),
               EException (Runtime, ()),
               ENumber (1L, ()),
               () ),
           [],
           () ) ) ]
;;

module Suite : TestSuite = struct
  let suite = parse_checks
end
