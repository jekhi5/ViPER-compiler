open Printf

let max (n : int) (m : int) : int =
  if n > m then n else m;;

(printf "Should be 5: %d\n" (max 5 4));
(printf "Should be 4: %d\n" (max 3 4));
(printf "Should be 4: %d\n" (max 4 4));
