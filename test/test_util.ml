open Test_funcs
open Util
open OUnit2

(* Tests for the utility functions for ViPER *)

let test_suite =
  [ tar "findNotFound" (Errors.InternalCompilerError "Name five not found") (fun _ ->
        Util.find [] "five" );
    tar "findNotPresent" (Errors.InternalCompilerError "Name ten not found") (fun _ ->
        Util.find [("one", "two"); ("three", "four")] "ten" );
    tae "findSingleElemList" "target" (Util.find [("targetKey", "target")] "targetKey");
    tae "findMultiElemList" "this one" (Util.find [("no", "not here"); ("here", "this one")] "here");
    tae "takeEmpty" [] (Util.take [] 10000);
    tae "takeZero" [] (Util.take [1; 2; 3] 0);
    tae "takeLessThan" [1; 2; 3] (Util.take [1; 2; 3; 4; 5] 3);
    tae "takeGreaterThan" [1; 2; 3; 4; 5; 6] (Util.take [1; 2; 3; 4; 5; 6] 1000);
    tae "dropEmpty" [] (Util.drop [] 10000);
    tae "dropZero" [1; 2; 3] (Util.drop [1; 2; 3] 0);
    tae "dropLessThan" [4; 5] (Util.drop [1; 2; 3; 4; 5] 3);
    tae "dropGreaterThan" [] (Util.drop [1; 2; 3; 4; 5; 6] 1000) ]
;;

module Suite : TestSuite = struct
  let suite = test_suite
end