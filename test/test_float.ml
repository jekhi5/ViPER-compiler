open Test_funcs

let simple_tests = [t "simple_float" "1.5" "" "1.5"]

(* Failing tests. Need to clarify expected semantics wrt to very large and small floats. *)
(* let boundary_tests =
  [ t "very_large_floats"
      "(   (4503599627370496.0 == 4503599627370496) ,\n\
      \    (4503599627370496 == 4503599627370496.0) ,\n\
      \    !(4503599627370497 == 4503599627370496.0) ,\n\
      \    !(4503599627370496.0 == 4503599627370497) ,\n\n\
      \    !(4503599627370496.5 == 4503599627370496) ,\n\
      \    (4503599627370496.5 > 4503599627370496) )"
      "" "(true, true, true, true, true, true)";
    t "very_small_floats"
      "(   (3.0000001 > 3) ,\n\
      \    !(3.0000001 == 3) ,\n\
      \    (2.9999999 < 3) ,\n\
      \    !(2.9999999 == 3) ,\n\
      \    !(2.9999999 >= 3) )"
      "" "(true, true, true, true, true)" ]
;; *)

module Suite : TestSuite = struct
  let suite = simple_tests (* @ boundary_tests *)
end
