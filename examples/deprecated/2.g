x := 1;
y := 2;
y := 2;
y := 2;
if x < 10 then
  r := 5
else
  r := 3;
if 1 < y then
  r := 4
else
  r := 9;
r := r + 10
(* [r ↦ 14; x ↦ 1; y ↦ 2] *)
