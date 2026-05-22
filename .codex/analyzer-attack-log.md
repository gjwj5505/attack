# Analyzer Attack Log

## 2026-04-21 - while 0 truthiness attack

공격 프로그램
```
while 0
  x := 1;
  while 0
    x := 0
```

분석기 약점
- 기존 `filter_t` / `filter_f`는 condition이 `Bop`인 경우만 refine했다.
- `Int 0` 같은 non-relational condition은 true/false branch 모두 그대로 통과했다.
- 그 결과 `while 0`의 body가 reachable하다고 분석됐다.
- unreachable loop body가 widening을 타면서 `x`가 `[-∞,∞]`까지 커졌다.

강화 방법
- `filter_t` / `filter_f` 시작에서 `Eval.antp_exp`로 condition 값을 먼저 평가한다.
- true branch에서 `Itv.maybe_true`가 false면 즉시 `Abs_mem.Bot`으로 보낸다.
- false branch에서 `Itv.maybe_false`가 false면 즉시 `Abs_mem.Bot`으로 보낸다.
- 이후 가능한 branch에 대해서만 기존 relational refinement를 수행한다.

## 2026-05-11 - one-iteration while widening precision attack

공격 프로그램
```
x := 1;
while x
  x := 0
```

공격 결과
- Big-Step concrete result: `x = 0`
- Analyzer result: `x |-> [-∞,1]`
- Objective: `nonsingleton`
- Found by: `./attack -attack -objective nonsingleton -bound 7 9`

분석기 약점
- Concrete execution enters the loop once, assigns `x := 0`, then exits.
- The analyzer uses widening on the loop back-edge.
- Joining/widening the loop body result back into the loop header loses the
  lower bound and produces an imprecise interval for `x`.
- The final false branch still contains the concrete value `0`, so this is a
  sound-but-imprecise false alarm rather than an unsoundness bug.

강화 방법
- 미정.
- 후보: loop handling/widening policy 개선, delayed widening 또는 narrowing
  검토.

## 2026-05-22 - top attack via weak loop filtering and lost correlation

공격 명령
```
./attack -attack -objective top
```

공격 프로그램
```
x := 1;
while (- x)
  x := 0;
x := (x * x)
```

공격 결과
- Found size: `(13,16)`
- Big-Step concrete result: `x = 0`
- Analyzer result: `x |-> [-∞,∞]`
- Objective: `top`

분석기 약점
- Concrete execution is simple: `x` starts at `0`, becomes `1`, enters the loop
  because `-x = -1`, the body sets `x := 0`, the next guard evaluates to `0`,
  and the final assignment computes `0 * 0 = 0`.
- The loop guard is `-x`, not `x`, so the exit filter does not refine `x`
  strongly enough after the loop. The analysis keeps a broad interval such as
  `[-∞,1]`.
- The final expression `x * x` loses the correlation between the two operands.
  Mathematically, `x * x` is always non-negative, but interval multiplication
  treats the two occurrences independently.
- The initial `x := 1` matters. If the interval before the multiplication were
  only `[-∞,0]`, then `x * x` could still be approximated as `[0,∞]`. Keeping
  the upper bound at `1` lets interval multiplication combine a negative lower
  side with a positive upper side, producing `[-∞,∞]`.

강화 방법
- 미정.
- 후보: unary guard에 대한 relational filtering 강화.
- 후보: 같은 변수끼리의 multiplication 같은 단순 relational pattern을 별도 처리.
