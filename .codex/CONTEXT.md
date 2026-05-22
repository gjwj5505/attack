# Context

정적 분석기가 false alarm 또는 unsound result를 내는 프로그램을 합성하는
프로젝트. 프로그램 자체가 아니라 Big-Step proof tree를 bottom-up으로 합성하고,
tree 결론의 command를 analyzer에 넣어 공격 성공 여부를 확인한다.

# Current Shape

- Entry: `bin/main.ml`, root executable: `./attack`.
- Attack config: `Synthesis.Config.attack`, 기본 변수는 `x`.
- 프로그램 시작 concrete memory는 all-zero로 본다.
- Analyzer는 concrete initial memory를 받을 수 있고, 없으면 all-zero로 돈다.
- Attack check는 proof tree initial concrete memory가 config 변수들에 대해
  all-zero일 때만 수행한다.
- Input language는 `*` multiplication을 파싱한다.

# Size / Search

- Size는 `(prog_size, proof_size)`.
- Size schedule은 `lib/synthesis/size_schedule.ml`.
  - `diagonal_up_to`: bounded bottom-up build용.
  - `rectangular_up_to`: partition용.
  - `square_forever`: attack search용 무한 순회.
- `square_forever`는 square bound를 1,2,3,... 키우되 frontier 안에서는 작은
  total size부터 처리한다.
- Raw syntax size `(k,0)`은 처음 필요한 proof target `(k+2,2)` 직전에만 삽입한다.
- `Partition.partition_special_while`은 `CWhileTrue`용. rest ctree는 같은 while
  command를 증명하므로 `rest.prog_size = target.prog_size`이고 proof size만 작다.

# Attack CLI

- `./attack -attack`: 첫 공격 하나.
- `./attack -attack -bound p q`: bound 안의 공격 전부.
- `./attack -attack -forever`: 무한 탐색하며 `result.d`에 append.
- `-bound`와 `-forever`는 같이 쓰지 않는다.
- `-seed n`: random component score seed.
- `-objective top|nonsingleton|unbounded|unsound`.
- precision objective를 골라도 `unsound`를 항상 먼저 검사한다.
- Progress:
  - raw syntax line은 파란색.
  - skipped size는 출력하지 않음.
  - 해당 size에서 공격을 찾으면 `found = N`.
  - forever mode는 별도 빨간 줄로 `found = N`만 출력.

`result.d` forever format:

```d
(* attack = 1 *)
(* size = (18,16); concrete = 0; abstract = [-∞,∞] *)
x := 1;
while (- x) do
  x := 0
end

```

`-forever` 시작 시 `result.d`는 비워지고, 이후 공격마다 빈 줄 하나를 두고 append.

# Temporary Heuristic

- Component는 `lib/synthesis/component_pool/component.ml`에서 payload + metadata.
- 현재 score는 임시 random score.
- `Synthesis.Attack`은 grown bucket을 score 상위 1000개로 cap.
- Rule input product도 임시 제한:
  - `Grow_util.binary_fanout_cap = 32`
  - `Grow_util.ternary_fanout_cap = 10`
- `Grow_prog` / `Grow_proof`의 제한 fold는 `TEMP: random-score fanout cap` 표시.
- 장기 방향:
  - random score를 analyzer-aware priority로 교체.
  - diversity metric 추가.
  - top-k 밖도 언젠가 탐색하는 eventual-success 근거 마련.

# Analyzer Output

- Engine: `lib/analyzer/analyzer_engine.ml`.
- `analysis`: exit abstract env.
- `analysis_sem`: label-to-abstract-env map.
- `./attack -analyze -v file.d`는 `Analyzer.Visualizer`로 프로그램 왼쪽에 label별
  abstract env를 붙여 출력한다.

# Important Files

- `bin/main.ml`: CLI.
- `lib/synthesis/attack.ml`: attack search.
- `lib/synthesis/size_schedule.ml`: size traversal.
- `lib/synthesis/grow_prog.ml`, `grow_proof.ml`, `grow_util.ml`: component growth.
- `lib/synthesis/component_pool/component.ml`, `component_set.ml`: component metadata,
  bucket table, caps.
- `lib/synthesis/objective.ml`: attack objectives and witnesses.
- `lib/analyzer/analyzer_engine.ml`, `lib/analyzer/visualizer.ml`: analyzer.
- `test/synthesis_test.ml`: regression tests.
- 성공 공격 설명: `.codex/analyzer-attack-log.md`.
- 성공 공격 프로그램: `examples/yymmdd-*.d`.

# Useful Commands

- `dune build`
- `./attack -attack -objective top -seed 10`
- `./attack -attack -bound 5 5`
- `./attack -attack -forever -objective top -seed 10`
- `./attack -analyze -v examples/260522-unary-guard-square-top.d`
- `dune exec ./test/synthesis_test.exe -- -forever`
