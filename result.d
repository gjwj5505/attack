(* attack = 1 *)
(* size = (16,15); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
while (- x) do
  x := (x + x)
end

(* attack = 2 *)
(* size = (16,16); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
while (- x) do
  x := 0
end;
while x do
  x := (- x)
end

(* attack = 3 *)
(* size = (17,17); concrete = 0; abstract = [-∞,∞] *)
x := (-1 * -1);
while (- x) do
  x := 0
end;
while (- x) do
  x := (- x)
end

(* attack = 4 *)
(* size = (17,17); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
while (- x) do
  x := 0
end;
while (- x) do
  x := (- x)
end

(* attack = 5 *)
(* size = (17,17); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
while x do
  x := (- x)
end

(* attack = 6 *)
(* size = (17,17); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
while x do
  x := (- x)
end

(* attack = 7 *)
(* size = (17,17); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
while x do
  x := (- x)
end

(* attack = 8 *)
(* size = (18,15); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
while (- x) do
  x := (1 + (-1 = -1))
end

(* attack = 9 *)
(* size = (18,16); concrete = 0; abstract = [-∞,∞] *)
x := (-1 * -1);
while (- x) do
  x := 0
end;
while x do
  x := (- (-1 + x))
end

(* attack = 10 *)
(* size = (18,16); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
while (- x) do
  x := 0
end;
while x do
  x := (- (-1 + x))
end

(* attack = 11 *)
(* size = (18,16); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
while (- x) do
  x := 0
end;
while x do
  x := (- (1 + x))
end

(* attack = 12 *)
(* size = (18,17); concrete = 0; abstract = [-∞,∞] *)
x := (-1 * -1);
while (- x) do
  x := 0
end;
while (- x) do
  x := (x + x)
end

(* attack = 13 *)
(* size = (18,17); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < 1);
while (- x) do
  x := 0
end;
while (- x) do
  x := (x * x)
end

(* attack = 14 *)
(* size = (18,18); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
while (x + (x * x)) do
  x := (- x)
end

(* attack = 15 *)
(* size = (18,18); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
while x do
  x := (- x)
end

(* attack = 16 *)
(* size = (18,18); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
while (- x) do
  x := (- x)
end

(* attack = 17 *)
(* size = (18,18); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
while (- x) do
  x := (- x)
end

(* attack = 18 *)
(* size = (18,18); concrete = 0; abstract = [-∞,∞] *)
x := x;
x := 1;
while (- x) do
  x := 0
end;
while (- x) do
  x := (- x)
end

(* attack = 19 *)
(* size = (19,17); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < 1);
while (- x) do
  x := 0
end;
while (- x) do
  x := (- (-1 + x))
end

(* attack = 20 *)
(* size = (19,17); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < (- x));
while (- x) do
  x := 0
end;
while x do
  x := (- (1 + x))
end

(* attack = 21 *)
(* size = (19,17); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
while x do
  x := (- (1 + x))
end

(* attack = 22 *)
(* size = (19,17); concrete = 0; abstract = [-∞,∞] *)
x := x;
x := 1;
while (- x) do
  x := 0
end;
while x do
  x := (- (1 + x))
end

(* attack = 23 *)
(* size = (19,18); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < (- x));
while (- x) do
  x := 0
end;
while (- x) do
  x := (x * x)
end

(* attack = 24 *)
(* size = (19,18); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
while (- x) do
  x := (x + x)
end

(* attack = 25 *)
(* size = (19,18); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
while (- x) do
  x := (-1 * x)
end

(* attack = 26 *)
(* size = (19,19); concrete = 0; abstract = [-∞,∞] *)
x := (-1 * -1);
while (- x) do
  x := 0
end;
while (- (x < -1)) do
  x := (- x)
end

(* attack = 27 *)
(* size = (19,19); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
while (x * x) do
  x := (- x)
end

(* attack = 28 *)
(* size = (17,20); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := (x * (x + (x * x)))

(* attack = 29 *)
(* size = (17,20); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := ((-1 + x) * (x * x))

(* attack = 30 *)
(* size = (20,18); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
while (- x) do
  x := 0
end;
if x then
  x := -1
else
  while x do
    x := (- x)
  end
end

(* attack = 31 *)
(* size = (20,18); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
while x do
  x := (- (1 + x))
end

(* attack = 32 *)
(* size = (20,18); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
while (- x) do
  x := (- (-1 + x))
end

(* attack = 33 *)
(* size = (20,19); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
while (x * x) do
  x := (-1 * x)
end

(* attack = 34 *)
(* size = (20,19); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := (- x);
while (- x) do
  x := (x + x)
end

(* attack = 35 *)
(* size = (20,20); concrete = 0; abstract = [-∞,∞] *)
x := (-1 * -1);
while (- x) do
  x := 0
end;
while (- (x <> (- x))) do
  x := (- x)
end

(* attack = 36 *)
(* size = (20,20); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < 1);
while (- x) do
  x := 0
end;
while (x + (x * x)) do
  x := (- x)
end

(* attack = 37 *)
(* size = (20,20); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
while (x * x) do
  x := (- x)
end

(* attack = 38 *)
(* size = (20,20); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
while (- (x < -1)) do
  x := (- x)
end

(* attack = 39 *)
(* size = (20,20); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
while (- (x < -1)) do
  x := (- x)
end

(* attack = 40 *)
(* size = (20,20); concrete = 0; abstract = [-∞,∞] *)
x := x;
x := 1;
while (- x) do
  x := 0
end;
while (- (x < -1)) do
  x := (- x)
end

(* attack = 41 *)
(* size = (21,15); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
while (- x) do
  x := ((x = x) + (x + (- x)))
end

(* attack = 42 *)
(* size = (21,18); concrete = 0; abstract = [-∞,∞] *)
x := (-1 * -1);
while (- x) do
  x := 0
end;
while (x * x) do
  while (- x) do
    x := (- x)
  end
end

(* attack = 43 *)
(* size = (21,19); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < 1);
while (- x) do
  x := 0
end;
if x then
  x := (- (-1 * x))
else
  x := (- x)
end

(* attack = 44 *)
(* size = (21,19); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
while (- x) do
  x := 0
end;
if x then
  x := (- (-1 * x))
else
  x := (- x)
end

(* attack = 45 *)
(* size = (21,19); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
while (- x) do
  x := (x * (- x))
end

(* attack = 46 *)
(* size = (21,19); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
while (- x) do
  x := (- (-1 + x))
end

(* attack = 47 *)
(* size = (21,19); concrete = 0; abstract = [-∞,∞] *)
x := (1 + (0 = 0));
while (- x) do
  x := 0
end;
while (- x) do
  x := (x * (- x))
end

(* attack = 48 *)
(* size = (21,19); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
if x then
  x := -1
else
  while x do
    x := (- x)
  end
end

(* attack = 49 *)
(* size = (21,21); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < (- x));
while (- x) do
  x := 0
end;
while (x + (x * x)) do
  x := (- x)
end

(* attack = 50 *)
(* size = (21,21); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
while (- (x < -1)) do
  x := (- x)
end

(* attack = 51 *)
(* size = (21,21); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
while (x + (x * x)) do
  x := (- x)
end

(* attack = 52 *)
(* size = (21,21); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
while (- (x <> (- x))) do
  x := (- x)
end

(* attack = 53 *)
(* size = (21,21); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
while x do
  x := (- x)
end

(* attack = 54 *)
(* size = (22,18); concrete = 0; abstract = [-∞,∞] *)
if x then
  x := -1
else
  x := (-1 < 1)
end;
while (- x) do
  x := 0
end;
while x do
  x := (- (1 + x))
end

(* attack = 55 *)
(* size = (22,19); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
while (- x) do
  x := (1 + (-1 = -1))
end

(* attack = 56 *)
(* size = (22,19); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
while (x * x) do
  while (- x) do
    x := (- x)
  end
end

(* attack = 57 *)
(* size = (19,22); concrete = 0; abstract = [-∞,∞] *)
x := (-1 * -1);
while (- x) do
  x := 0
end;
x := ((-1 + x) * (x * x))

(* attack = 58 *)
(* size = (19,22); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < 1);
while (- x) do
  x := 0
end;
x := (x * (x + (x * x)))

(* attack = 59 *)
(* size = (19,22); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < 1);
while (- x) do
  x := 0
end;
x := ((-1 + x) * (x * x))

(* attack = 60 *)
(* size = (19,22); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
while (- x) do
  x := 0
end;
x := (x * (x + (x * x)))

(* attack = 61 *)
(* size = (19,22); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
while (- x) do
  x := 0
end;
x := ((-1 + x) * (x * x))

(* attack = 62 *)
(* size = (22,20); concrete = 0; abstract = [-∞,∞] *)
x := 1;
if x then
  while (- x) do
    x := 0
  end
else
  x := 1
end;
while (- (x <> (- x))) do
  x := (- x)
end

(* attack = 63 *)
(* size = (22,20); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
if (-1 < 1) then
  while (- x) do
    x := 0
  end
else
  x := x
end;
while x do
  x := (- x)
end

(* attack = 64 *)
(* size = (22,20); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := (- x);
if x then
  x := -1
else
  while x do
    x := (- x)
  end
end

(* attack = 65 *)
(* size = (22,21); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
while (- (x <> (- x))) do
  x := (-1 * x)
end

(* attack = 66 *)
(* size = (22,22); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
while (x + (x * x)) do
  x := (- x)
end

(* attack = 67 *)
(* size = (22,22); concrete = 0; abstract = [-∞,∞] *)
x := (1 + (0 = 0));
while (- x) do
  x := 0
end;
while (- (x <> (- x))) do
  x := (- x)
end

(* attack = 68 *)
(* size = (22,22); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
while (- x) do
  x := (- x)
end

(* attack = 69 *)
(* size = (23,15); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
while (- x) do
  while (-1 = (- x)) do
    x := (1 + (-1 = -1))
  end
end

(* attack = 70 *)
(* size = (23,19); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
if x then
  x := (1 < -1)
else
  while x do
    x := (- x)
  end
end

(* attack = 71 *)
(* size = (23,20); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := (- x);
while (x * x) do
  while (- x) do
    x := (- x)
  end
end

(* attack = 72 *)
(* size = (20,23); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < (- x));
while (- x) do
  x := 0
end;
x := (x * (x + (x * x)))

(* attack = 73 *)
(* size = (20,23); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < (- x));
while (- x) do
  x := 0
end;
x := ((-1 + x) * (x * x))

(* attack = 74 *)
(* size = (20,23); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
x := (x * (x + (x * x)))

(* attack = 75 *)
(* size = (20,23); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
x := ((-1 + x) * (x * x))

(* attack = 76 *)
(* size = (20,23); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
x := (x * (x + (x * x)))

(* attack = 77 *)
(* size = (20,23); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
x := ((-1 + x) * (x * x))

(* attack = 78 *)
(* size = (20,23); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (x * (x + (x * x)))

(* attack = 79 *)
(* size = (20,23); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := ((-1 + x) * (x * x))

(* attack = 80 *)
(* size = (20,23); concrete = 0; abstract = [-∞,∞] *)
x := x;
x := 1;
while (- x) do
  x := 0
end;
x := (x * (x + (x * x)))

(* attack = 81 *)
(* size = (23,21); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
if (-1 < 1) then
  while (- x) do
    x := 0
  end
else
  x := x
end;
while (- x) do
  x := (- x)
end

(* attack = 82 *)
(* size = (23,21); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := (- x);
if x then
  x := (- (-1 * x))
else
  x := (- x)
end

(* attack = 83 *)
(* size = (23,22); concrete = 0; abstract = [-∞,∞] *)
x := 1;
if 1 then
  while (- x) do
    x := 0
  end
else
  x := (-1 = x)
end;
x := ((-1 + x) * (x * x))

(* attack = 84 *)
(* size = (23,22); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
while (- (x <> (- x))) do
  x := (-1 * x)
end

(* attack = 85 *)
(* size = (23,22); concrete = 0; abstract = [-∞,∞] *)
x := (1 + (0 = 0));
while (- x) do
  x := 0
end;
while (- (x <> (- x))) do
  x := (-1 * x)
end

(* attack = 86 *)
(* size = (23,22); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
while (- x) do
  x := (x + x)
end

(* attack = 87 *)
(* size = (23,22); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
while (- x) do
  x := (-1 * x)
end

(* attack = 88 *)
(* size = (23,23); concrete = 0; abstract = [-∞,∞] *)
x := (-1 * -1);
while (- x) do
  x := 0
end;
x := (1 < (x * x));
while x do
  x := (- x)
end

(* attack = 89 *)
(* size = (24,20); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
if x then
  while (- x) do
    x := 0
  end
else
  x := -1
end;
if x then
  x := -1
else
  while x do
    x := (- x)
  end
end

(* attack = 90 *)
(* size = (24,20); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
if 0 then
  x := (0 <> x)
else
  while (- x) do
    x := (- x)
  end
end

(* attack = 91 *)
(* size = (24,20); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
while 0 do
  x := x
end;
while x do
  x := (- (1 + x))
end

(* attack = 92 *)
(* size = (24,20); concrete = 0; abstract = [-∞,∞] *)
if x then
  x := x
else
  x := (- (-1 + -1));
  while (- x) do
    x := 0
  end
end;
while (- x) do
  x := (- (-1 + x))
end

(* attack = 93 *)
(* size = (24,21); concrete = 0; abstract = [-∞,∞] *)
x := 1;
if (- ((- x) < x)) then
  while (- x) do
    x := 0
  end
else
  x := 1
end;
while (- x) do
  x := (-1 * x)
end

(* attack = 94 *)
(* size = (24,21); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
if (-1 < 1) then
  while (- x) do
    x := 0
  end
else
  x := x
end;
while (- x) do
  x := (x + x)
end

(* attack = 95 *)
(* size = (24,21); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
if x then
  x := -1
else
  while (x * x) do
    x := (-1 * x)
  end
end

(* attack = 96 *)
(* size = (24,21); concrete = 0; abstract = [-∞,∞] *)
if x then
  x := x
else
  x := 0;
  x := 1;
  while (- x) do
    x := 0
  end
end;
while (x * x) do
  x := (-1 * x)
end

(* attack = 97 *)
(* size = (21,24); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
x := (x * (x + (x * x)))

(* attack = 98 *)
(* size = (21,24); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
x := ((-1 + x) * (x * x))

(* attack = 99 *)
(* size = (21,24); concrete = 0; abstract = [-∞,∞] *)
x := (1 + (0 = 0));
while (- x) do
  x := 0
end;
x := ((-1 + x) * (x * x))

(* attack = 100 *)
(* size = (21,24); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := (- x);
x := (x * (x + (x * x)))

(* attack = 101 *)
(* size = (21,24); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := (- x);
x := ((-1 + x) * (x * x))

(* attack = 102 *)
(* size = (24,22); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < (- x));
while (- x) do
  x := 0
end;
if (- (0 <> x)) then
  x := 0
else
  while x do
    x := (- x)
  end
end

(* attack = 103 *)
(* size = (24,22); concrete = 0; abstract = [-∞,∞] *)
if x then
  x := -1
else
  x := (-1 < 1)
end;
while (- x) do
  x := 0
end;
while (- (x <> (- x))) do
  x := (- x)
end

(* attack = 104 *)
(* size = (24,24); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (1 = x);
while (x * x) do
  x := (- x)
end

(* attack = 105 *)
(* size = (25,18); concrete = 0; abstract = [-∞,∞] *)
x := 1;
if 1 then
  while (- x) do
    x := 0
  end
else
  x := (-1 = x)
end;
while (x * x) do
  while (- x) do
    x := (- x)
  end
end

(* attack = 106 *)
(* size = (25,18); concrete = 0; abstract = [-∞,∞] *)
x := x;
x := 1;
while (- x) do
  x := 0
end;
while (- x) do
  if (- x) then
    x := (- x)
  else
    x := (0 = 1)
  end
end

(* attack = 107 *)
(* size = (25,21); concrete = 0; abstract = [-∞,∞] *)
x := 1;
if (- ((- x) < x)) then
  while (- x) do
    x := 0
  end
else
  x := 1
end;
while (- x) do
  x := (- (-1 + -1))
end

(* attack = 108 *)
(* size = (25,21); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
while (- x) do
  x := -1
end;
while x do
  x := (- (-1 + x))
end

(* attack = 109 *)
(* size = (25,21); concrete = 0; abstract = [-∞,∞] *)
if (0 <> x) then
  x := -1
else
  x := (-1 < x);
  while (- x) do
    x := 0
  end
end;
while (- x) do
  x := (- (1 + x))
end

(* attack = 110 *)
(* size = (22,25); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < 1);
while (- x) do
  x := 0
end;
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 111 *)
(* size = (22,25); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
while (- x) do
  x := 0
end;
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 112 *)
(* size = (25,23); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
if (-1 < 1) then
  while (- x) do
    x := 0
  end
else
  x := x
end;
while (- (x < -1)) do
  x := (- x)
end

(* attack = 113 *)
(* size = (25,23); concrete = 0; abstract = [-∞,∞] *)
if x then
  x := x
else
  x := (- (-1 + -1));
  while (- x) do
    x := 0
  end
end;
while (- (x <> (- x))) do
  x := (- x)
end

(* attack = 114 *)
(* size = (25,23); concrete = 0; abstract = [-∞,∞] *)
if x then
  x := x
else
  x := 0;
  x := 1;
  while (- x) do
    x := 0
  end
end;
while (x + (x * x)) do
  x := (- x)
end

(* attack = 115 *)
(* size = (24,25); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
if -1 then
  while (- x) do
    x := 0
  end
else
  x := 1
end;
x := (x * (x + (x * x)))

(* attack = 116 *)
(* size = (25,25); concrete = 0; abstract = [-∞,∞] *)
x := (-1 * -1);
while (- x) do
  x := 0
end;
x := (- ((0 <> 1) = (- x)));
while x do
  x := (- x)
end

(* attack = 117 *)
(* size = (25,25); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
while (x + (x * x)) do
  x := (- x)
end

(* attack = 118 *)
(* size = (25,25); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
while (- (x <> (- x))) do
  x := (- x)
end

(* attack = 119 *)
(* size = (26,20); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
if -1 then
  while (- x) do
    x := 0
  end
else
  x := 1
end;
while (- x) do
  x := (x * (- (0 = 0)))
end

(* attack = 120 *)
(* size = (26,20); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
while 0 do
  x := x
end;
while x do
  x := (x * (- (0 = 0)))
end

(* attack = 121 *)
(* size = (26,21); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < 1);
if (-1 < 1) then
  while (- x) do
    x := 0
  end
else
  x := x
end;
while (- x) do
  while (- x) do
    x := (- x)
  end
end

(* attack = 122 *)
(* size = (26,22); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
x := x;
if x then
  while (- x) do
    x := 0
  end
else
  x := x
end;
while (- x) do
  x := (- (-1 + -1))
end

(* attack = 123 *)
(* size = (26,22); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
x := x;
if x then
  while (- x) do
    x := 0
  end
else
  x := x
end;
while (- x) do
  x := (- (-1 + x))
end

(* attack = 124 *)
(* size = (26,22); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
while (- x) do
  x := -1
end;
while (- x) do
  x := (- (-1 + x))
end

(* attack = 125 *)
(* size = (26,22); concrete = 0; abstract = [-∞,∞] *)
if x then
  x := x
else
  x := (- (-1 + -1));
  while (- x) do
    x := 0
  end
end;
if x then
  x := (- (-1 * x))
else
  x := (- x)
end

(* attack = 126 *)
(* size = (26,23); concrete = 0; abstract = [-∞,∞] *)
if ((- x) < 0) then
  x := x
else
  x := (- (-1 + -1));
  while (- x) do
    x := 0
  end
end;
while (- x) do
  x := (-1 * x)
end

(* attack = 127 *)
(* size = (26,23); concrete = 0; abstract = [-∞,∞] *)
if ((- x) < 0) then
  x := 0
else
  x := 1;
  while (- x) do
    x := 0
  end;
  x := x
end;
while (- x) do
  x := (1 + x)
end

(* attack = 128 *)
(* size = (23,26); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < (- x));
while (- x) do
  x := 0
end;
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 129 *)
(* size = (23,26); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 130 *)
(* size = (23,26); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 131 *)
(* size = (23,26); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 132 *)
(* size = (23,26); concrete = 0; abstract = [-∞,∞] *)
x := x;
x := 1;
while (- x) do
  x := 0
end;
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 133 *)
(* size = (26,24); concrete = 0; abstract = [-∞,∞] *)
x := 1;
if (- ((- x) < x)) then
  while (- x) do
    x := 0
  end
else
  x := 1
end;
while (- (x <> (- x))) do
  x := (- x)
end

(* attack = 134 *)
(* size = (26,24); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := (- x);
x := (- (1 = x));
while x do
  x := (- (-1 + x))
end

(* attack = 135 *)
(* size = (26,24); concrete = 0; abstract = [-∞,∞] *)
x := x;
x := 1;
while (- x) do
  x := 0
end;
if (- x) then
  x := -1
else
  x := 0
end;
while (- x) do
  x := (- x)
end

(* attack = 136 *)
(* size = (25,26); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
if (-1 < 1) then
  while (- x) do
    x := 0
  end
else
  x := x
end;
x := (x * (x + (x * x)))

(* attack = 137 *)
(* size = (25,26); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
if (x < -1) then
  x := 0
else
  while (- x) do
    x := 0
  end
end;
x := ((-1 + x) * (x * x))

(* attack = 138 *)
(* size = (25,26); concrete = 0; abstract = [-∞,∞] *)
if (0 <> x) then
  x := -1
else
  x := (-1 < x);
  while (- x) do
    x := 0
  end
end;
x := (x * (x + (x * x)))

(* attack = 139 *)
(* size = (26,26); concrete = 0; abstract = [-∞,∞] *)
x := (-1 * -1);
while (- x) do
  x := 0
end;
x := (- ((0 <> 1) = (- x)));
while (- x) do
  x := (- x)
end

(* attack = 140 *)
(* size = (26,26); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := (- x);
x := (- (1 = x));
while (x * x) do
  x := (- x)
end

(* attack = 141 *)
(* size = (27,21); concrete = 0; abstract = [-∞,∞] *)
if x then
  x := -1
else
  x := (-1 < 1)
end;
while (- x) do
  x := 0
end;
if 0 then
  x := (0 <> x)
else
  while (- x) do
    x := (- x)
  end
end

(* attack = 142 *)
(* size = (27,22); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
if x then
  while -1 do
    x := 1
  end
else
  while (x * x) do
    x := (-1 * x)
  end
end

(* attack = 143 *)
(* size = (27,22); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
while ((0 <> x) < 0) do
  x := (1 = x)
end;
while (- x) do
  x := (-1 * x)
end

(* attack = 144 *)
(* size = (27,22); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
while (- x) do
  x := -1;
  x := -1
end;
while (- x) do
  x := (- x)
end

(* attack = 145 *)
(* size = (27,23); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
if (- ((0 = 0) <> (0 < 0))) then
  while x do
    x := (- (1 + x))
  end
else
  x := x
end

(* attack = 146 *)
(* size = (27,24); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
if (- x) then
  x := -1
else
  x := 0
end;
while (- (x <> (- x))) do
  x := (-1 * x)
end

(* attack = 147 *)
(* size = (27,24); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (1 = x);
while (x * x) do
  while (- x) do
    x := (- x)
  end
end

(* attack = 148 *)
(* size = (24,27); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 149 *)
(* size = (24,27); concrete = 0; abstract = [-∞,∞] *)
x := (1 + (0 = 0));
while (- x) do
  x := 0
end;
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 150 *)
(* size = (24,27); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := (- x);
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 151 *)
(* size = (24,27); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
x := (x * (x + (x * x)))

(* attack = 152 *)
(* size = (24,27); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
x := ((-1 + x) * (x * x))

(* attack = 153 *)
(* size = (27,25); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
if (- ((- x) < x)) then
  while (- x) do
    x := 0
  end
else
  x := -1
end;
while (- (x < -1)) do
  x := (- x)
end

(* attack = 154 *)
(* size = (27,26); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := (- x);
x := (- (1 = x));
while (x * x) do
  x := (-1 * x)
end

(* attack = 155 *)
(* size = (26,27); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
x := x;
if x then
  while (- x) do
    x := 0
  end
else
  x := x
end;
x := ((-1 + x) * (x * x))

(* attack = 156 *)
(* size = (27,27); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
x := (- ((0 <> 1) = (- x)));
while x do
  x := (- x)
end

(* attack = 157 *)
(* size = (27,27); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
x := (x < (- (-1 <> (-1 + x))));
while x do
  x := (- x)
end

(* attack = 158 *)
(* size = (28,19); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
while (- x) do
  x := (1 < (0 < (- x)))
end;
while (- x) do
  x := (x * (- x))
end

(* attack = 159 *)
(* size = (28,21); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < 1);
while (- x) do
  x := 0
end;
while (- x) do
  x := (- (-1 * x))
end;
while (- x) do
  x := (- (1 + x))
end

(* attack = 160 *)
(* size = (28,23); concrete = 1; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
if x then
  x := (- x)
else
  x := 1
end;
if x then
  while (x < -1) do
    x := -1
  end
else
  x := (- x)
end

(* attack = 161 *)
(* size = (28,24); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
if (- ((- x) < x)) then
  while (- x) do
    x := 0
  end
else
  x := -1
end;
if x then
  x := 1
else
  while x do
    x := (- x)
  end
end

(* attack = 162 *)
(* size = (28,24); concrete = 0; abstract = [-∞,∞] *)
if ((- x) < 0) then
  x := x
else
  x := (- (-1 + -1));
  while (- x) do
    x := 0
  end
end;
if x then
  x := -1
else
  while x do
    x := (- x)
  end
end

(* attack = 163 *)
(* size = (28,26); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
if 0 then
  x := -1
else
  x := (- x)
end;
while (x * x) do
  x := (- x)
end

(* attack = 164 *)
(* size = (28,27); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
while ((0 <> x) < 0) do
  x := (1 = x)
end;
x := (x * (x + (x * x)))

(* attack = 165 *)
(* size = (27,28); concrete = 0; abstract = [-∞,∞] *)
if x then
  x := x
else
  x := 0;
  x := 1;
  while (- x) do
    x := 0
  end
end;
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 166 *)
(* size = (27,28); concrete = 0; abstract = [-∞,∞] *)
if ((- x) < 0) then
  x := x
else
  x := (- (-1 + -1));
  while (- x) do
    x := 0
  end
end;
x := (x * (x + (x * x)))

(* attack = 167 *)
(* size = (27,28); concrete = 0; abstract = [-∞,∞] *)
if ((- x) < 0) then
  x := 0
else
  x := 1;
  while (- x) do
    x := 0
  end;
  x := x
end;
x := (x * (x + (x * x)))

(* attack = 168 *)
(* size = (29,19); concrete = 0; abstract = [-∞,∞] *)
x := (-1 * -1);
while (- x) do
  x := 0
end;
if 0 then
  while -1 do
    x := 1
  end
else
  while (- x) do
    if 0 then
      while -1 do
        x := 1
      end
    else
      x := (- x)
    end
  end
end

(* attack = 169 *)
(* size = (29,19); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
while (- x) do
  x := (- (0 = (0 = x)));
  x := (- (-1 + x))
end

(* attack = 170 *)
(* size = (29,22); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
if (x < -1) then
  x := 0
else
  while (- x) do
    x := 0
  end
end;
if 0 then
  x := (x <> (- x))
else
  while x do
    x := (- x)
  end
end

(* attack = 171 *)
(* size = (29,22); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
if 1 then
  if 1 then
    while (- x) do
      x := 0
    end
  else
    x := -1
  end
else
  x := 0
end;
while (- x) do
  while (- x) do
    x := (- x)
  end
end

(* attack = 172 *)
(* size = (29,22); concrete = 0; abstract = [-∞,∞] *)
if ((- x) < 0) then
  while 1 do
    x := (-1 = 1)
  end
else
  x := (-1 < x);
  while (- x) do
    x := 0
  end
end;
while (- x) do
  x := (x * x)
end

(* attack = 173 *)
(* size = (29,25); concrete = 0; abstract = [-∞,∞] *)
x := (1 + (0 = 0));
while (- x) do
  x := 0
end;
while (0 < 0) do
  x := (- x)
end;
while (x * x) do
  x := (-1 * x)
end

(* attack = 174 *)
(* size = (29,25); concrete = 0; abstract = [-∞,∞] *)
if (- ((0 = 0) <> (0 < 0))) then
  x := (-1 < x);
  while (- x) do
    x := 0
  end
else
  x := x
end;
while x do
  x := (- (-1 + x))
end

(* attack = 175 *)
(* size = (29,26); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < 1);
if (- ((- x) < x)) then
  while (- x) do
    x := 0
  end
else
  x := -1
end;
while (- (x <> (- x))) do
  x := (-1 * x)
end

(* attack = 176 *)
(* size = (29,27); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
x := (x < (- (-1 <> (-1 + x))));
while x do
  x := (- (1 + x))
end

(* attack = 177 *)
(* size = (29,27); concrete = 0; abstract = [-∞,∞] *)
if (- (-1 <> (-1 + x))) then
  x := 1
else
  x := (-1 < x);
  while (- x) do
    x := 0
  end
end;
while (- (x <> (- x))) do
  x := (- x)
end

(* attack = 178 *)
(* size = (29,28); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < (- x));
while (- x) do
  x := 0
end;
while ((0 <> 1) = (x + (- (x = (-1 + x))))) do
  x := (-1 * x)
end

(* attack = 179 *)
(* size = (30,20); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < 1);
while (- x) do
  x := 0
end;
if (- x) then
  while (-1 < x) do
    while 1 do
      x := 1
    end
  end
else
  while (- x) do
    x := (- (1 + x))
  end
end

(* attack = 180 *)
(* size = (30,21); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
if 0 then
  x := (- x)
else
  while (- x) do
    if 0 then
      while -1 do
        x := 1
      end
    else
      x := (- x)
    end
  end
end

(* attack = 181 *)
(* size = (30,21); concrete = 0; abstract = [-∞,∞] *)
x := (1 + (0 = 0));
while (- x) do
  x := 0
end;
if 0 then
  if x then
    x := 0
  else
    x := (1 < -1)
  end
else
  while (- x) do
    x := (x + x)
  end
end

(* attack = 182 *)
(* size = (30,21); concrete = 0; abstract = [-∞,∞] *)
if x then
  x := -1
else
  x := (-1 < 1)
end;
while (- x) do
  x := 0
end;
if x then
  x := (- (-1 * x))
else
  while (- x) do
    x := (- (1 + x))
  end
end

(* attack = 183 *)
(* size = (30,22); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
while (- x) do
  x := (1 < (0 < (- x)))
end;
while (- (x <> (- x))) do
  x := (-1 * x)
end

(* attack = 184 *)
(* size = (30,23); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (1 = x);
while (- x) do
  if (- x) then
    x := (- x)
  else
    x := (0 = 1)
  end
end

(* attack = 185 *)
(* size = (30,24); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
while (- x) do
  x := 0
end;
while (- x) do
  x := -1
end;
if 0 then
  x := (0 <> x)
else
  while (- x) do
    x := (- x)
  end
end

(* attack = 186 *)
(* size = (30,25); concrete = 0; abstract = [-∞,∞] *)
x := x;
x := 1;
while (- x) do
  x := 0
end;
if (- (0 <> x)) then
  x := (x <> (- x))
else
  while x do
    x := (- x)
  end;
  x := x
end

(* attack = 187 *)
(* size = (30,25); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
while (- x) do
  x := -1;
  x := x
end;
while (- (x <> (- x))) do
  x := (- x)
end

(* attack = 188 *)
(* size = (30,25); concrete = 0; abstract = [-∞,∞] *)
x := x;
x := 1;
while (- x) do
  x := 0
end;
if (- x) then
  x := -1
else
  x := 0
end;
while (x * x) do
  while (- x) do
    x := (- x)
  end
end

(* attack = 189 *)
(* size = (30,26); concrete = 0; abstract = [-∞,∞] *)
x := x;
x := 1;
while (- x) do
  x := 0
end;
if (- ((0 = 0) <> (0 < 0))) then
  while x do
    x := (- (1 + x))
  end
else
  x := x
end

(* attack = 190 *)
(* size = (30,26); concrete = 0; abstract = [-∞,∞] *)
if (- ((0 = 0) <> (0 < 0))) then
  x := (-1 < x);
  while (- x) do
    x := 0
  end
else
  x := x
end;
while (- x) do
  x := (x * (- x))
end

(* attack = 191 *)
(* size = (30,27); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
if x then
  while (- x) do
    x := 0
  end
else
  x := -1
end;
x := (- (x < (0 <> x)));
while (- x) do
  x := (-1 * x)
end

(* attack = 192 *)
(* size = (30,27); concrete = 0; abstract = [-∞,∞] *)
x := (1 + (0 = 0));
while (- x) do
  x := 0
end;
while (0 < 0) do
  x := (- x)
end;
while (- (x <> (- x))) do
  x := (- x)
end

(* attack = 193 *)
(* size = (30,27); concrete = 0; abstract = [-∞,∞] *)
if (- ((- (x <> (- x))) < 0)) then
  x := x
else
  x := (- (-1 + -1));
  while (- x) do
    x := 0
  end
end;
while (- x) do
  x := (1 + x)
end

(* attack = 194 *)
(* size = (27,30); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 195 *)
(* size = (31,23); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
if (- ((- x) < x)) then
  while (- x) do
    x := 0
  end
else
  x := -1
end;
while (- x) do
  x := ((x = x) + (x + (- x)))
end

(* attack = 196 *)
(* size = (31,25); concrete = 0; abstract = [-∞,∞] *)
x := 1;
if x then
  while (- x) do
    x := 0
  end
else
  x := 1
end;
if ((-1 + x) <> (-1 + x)) then
  x := (- x)
else
  while (- x) do
    x := (1 + x)
  end
end

(* attack = 197 *)
(* size = (31,27); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
x := (- ((0 <> 1) = (- x)));
while x do
  x := (x * (- (0 = 0)))
end

(* attack = 198 *)
(* size = (31,28); concrete = 0; abstract = [-∞,∞] *)
x := (- ((0 <> 1) = (- (0 <> x))));
x := 1;
while (- x) do
  x := 0
end;
if (- x) then
  x := (- x)
else
  while 0 do
    x := (- x)
  end
end

(* attack = 199 *)
(* size = (31,28); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := (- x);
x := (- (1 = x));
if x then
  x := -1
else
  while (x * x) do
    x := (-1 * x)
  end
end

(* attack = 200 *)
(* size = (28,31); concrete = 0; abstract = [-∞,∞] *)
x := (- ((0 <> 1) = (- (0 <> x))));
x := 1;
while (- x) do
  x := 0
end;
x := ((-1 + x) * (x * x))

(* attack = 201 *)
(* size = (28,31); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
x := (x * (x + (x * x)));
x := (- x)

(* attack = 202 *)
(* size = (31,29); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < (- (x <> (- x))));
if (- (-1 = (x < -1))) then
  x := x
else
  while (- x) do
    x := 0
  end
end;
while (x * x) do
  x := (- x)
end

(* attack = 203 *)
(* size = (31,30); concrete = 0; abstract = [-∞,∞] *)
x := 1;
if x then
  while (- x) do
    x := 0
  end;
  x := 1;
  while (- x) do
    x := 0
  end
else
  x := (-1 <> 0)
end;
while (x * x) do
  x := (- x)
end

(* attack = 204 *)
(* size = (31,30); concrete = 0; abstract = [-∞,∞] *)
x := (-1 * -1);
if x then
  while (- x) do
    x := 0
  end;
  x := 1;
  while (- x) do
    x := 0
  end
else
  x := 0
end;
while x do
  x := (- (-1 + x))
end

(* attack = 205 *)
(* size = (31,30); concrete = 0; abstract = [-∞,∞] *)
if ((- (x = (- x))) < x) then
  x := (-1 < x);
  while (- x) do
    x := 0
  end
else
  x := (0 = 1)
end;
x := (x * (x + (x * x)))

(* attack = 206 *)
(* size = (30,31); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < 1);
if (- ((- x) < x)) then
  while (- x) do
    x := 0
  end
else
  x := -1
end;
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 207 *)
(* size = (30,31); concrete = 0; abstract = [-∞,∞] *)
x := (- x);
x := (-1 < x);
if x then
  while (- x) do
    x := 0
  end
else
  x := 0
end;
x := ((-1 = (- x)) + (x + (x * x)))

(* attack = 208 *)
(* size = (30,31); concrete = 0; abstract = [-∞,∞] *)
if (- ((0 = 0) <> (0 < 0))) then
  x := (-1 < x);
  while (- x) do
    x := 0
  end
else
  x := x
end;
x := (x * (x + (x * x)))

(* attack = 209 *)
(* size = (30,31); concrete = 0; abstract = [-∞,∞] *)
if (- ((0 = 0) <> (0 < 0))) then
  x := (-1 < x);
  while (- x) do
    x := 0
  end
else
  x := x
end;
x := ((-1 + x) * (x * x))

(* attack = 210 *)
(* size = (31,31); concrete = 0; abstract = [-∞,∞] *)
x := 0;
x := 1;
while (- x) do
  x := 0
end;
x := (x < (- (-1 <> (-1 + x))));
while (x + (x * x)) do
  x := (- x)
end

(* attack = 211 *)
(* size = (32,17); concrete = 0; abstract = [-∞,∞] *)
x := (-1 * -1);
while (- x) do
  x := 0
end;
while (- x) do
  if (- (x < x)) then
    x := (-1 = x)
  else
    if x then
      x := (- (1 + x))
    else
      x := 1
    end
  end
end

(* attack = 212 *)
(* size = (32,24); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
if (0 <> x) then
  x := (1 = 1)
else
  while 0 do
    x := 1
  end
end;
while x do
  x := (- (1 + x))
end

(* attack = 213 *)
(* size = (32,26); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
if -1 then
  while (- x) do
    x := 0
  end
else
  x := 1
end;
while (x * x) do
  x := (x <> x)
end;
while (x * x) do
  x := (- x)
end

(* attack = 214 *)
(* size = (32,28); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
x := (- ((0 <> 1) = (- x)));
while (- x) do
  if 0 then
    x := x
  else
    x := (- x)
  end
end

(* attack = 215 *)
(* size = (32,28); concrete = 0; abstract = [-∞,∞] *)
if (- x) then
  x := (x <> (- x))
else
  x := 1
end;
if (- (x < x)) then
  x := x
else
  while (- x) do
    x := 0
  end
end;
x := ((-1 + x) * (x * x))

(* attack = 216 *)
(* size = (32,30); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
x := (x * (x + (x * x)));
while x do
  while 1 do
    x := (- x)
  end
end

(* attack = 217 *)
(* size = (32,31); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
x := (x * (x + (x * x)));
while (- x) do
  x := (-1 = x)
end

(* attack = 218 *)
(* size = (32,31); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
x := (x * (x + (x * x)));
while (- x) do
  x := (x * x)
end

(* attack = 219 *)
(* size = (32,32); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := 0;
x := 1;
if 1 then
  while (- x) do
    x := 0
  end
else
  x := x
end;
while (- x) do
  x := (1 + x)
end

(* attack = 220 *)
(* size = (33,17); concrete = 0; abstract = [-∞,∞] *)
x := (-1 < x);
while (- x) do
  x := 0
end;
while (- x) do
  if (- (0 <> (x < x))) then
    while (- (0 < x)) do
      x := (x <> x)
    end
  else
    x := (- x)
  end
end

(* attack = 221 *)
(* size = (33,19); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
while (- x) do
  if (0 < 0) then
    x := (-1 = x)
  else
    x := (-1 = 0)
  end
end;
while (- x) do
  x := (- (-1 + -1))
end

(* attack = 222 *)
(* size = (33,20); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
while (- x) do
  if (0 < 0) then
    x := (-1 = x)
  else
    x := (-1 = 0)
  end
end;
while (x * x) do
  x := (-1 * x)
end

(* attack = 223 *)
(* size = (33,21); concrete = 0; abstract = [-∞,∞] *)
x := 1;
if x then
  while (- x) do
    x := 0
  end
else
  x := 1
end;
if 0 then
  if x then
    x := 0
  else
    x := (1 < -1)
  end
else
  if x then
    x := (- (-1 * x))
  else
    x := (- x)
  end
end

(* attack = 224 *)
(* size = (33,22); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := x;
x := (- x);
while (- x) do
  x := (0 < (-1 * -1));
  x := (-1 + (- (1 = x)))
end

(* attack = 225 *)
(* size = (33,23); concrete = 0; abstract = [-∞,∞] *)
if ((- x) < 0) then
  x := 0
else
  x := 1;
  while (- x) do
    x := 0
  end;
  x := x
end;
while (- x) do
  x := ((-1 = (-1 + 1)) + (-1 + (- x)))
end

(* attack = 226 *)
(* size = (33,24); concrete = 0; abstract = [-∞,∞] *)
while 0 do
  x := (-1 <> 0)
end;
x := 1;
if (- (x < x)) then
  x := x
else
  while (- x) do
    x := 0
  end
end;
while (x * x) do
  while (- x) do
    x := (- x)
  end
end

(* attack = 227 *)
(* size = (33,25); concrete = 0; abstract = [-∞,∞] *)
x := (0 <> (0 = 0));
while (- x) do
  x := 0
end;
if 0 then
  x := -1
else
  x := (- x)
end;
while (- x) do
  x := ((x = x) + (x + (- x)))
end

(* attack = 228 *)
(* size = (33,27); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end;
x := (- x);
x := (- (1 = x));
while x do
  x := (- (-1 + x))
end;
while 0 do
  while -1 do
    x := -1
  end
end

(* attack = 229 *)
(* size = (33,28); concrete = 0; abstract = [-∞,∞] *)
x := (- (-1 + -1));
if 0 then
  x := (1 = 1)
else
  while 0 do
    x := (1 < -1)
  end;
  while (- x) do
    x := 0
  end;
  x := ((-1 + x) * (x * x))
end

