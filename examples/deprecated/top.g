x := 0;
y := 0;
while x < 1 do
  x := x + 1
end;
while y < 1 do
  x := x - 1;
  y := y + 1
end
(* analyzer intended: x becomes top through upward widening, then y-controlled downward widening *)
