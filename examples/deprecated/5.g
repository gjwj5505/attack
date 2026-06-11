x := 0;
(if x < 0 then
  y := 1
else
  y := 2);
(if y <> 2 then
  z := 1
else
  z := 2)
(* analyzer expected: [y |-> [2,2]; z |-> [2,2]] *)
