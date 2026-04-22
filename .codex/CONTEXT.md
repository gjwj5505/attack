# Overview

정적 분석기가 false alarm을 발생시키는 프로그램을 합성하는 프로젝트.
프로그램 syntax만 합성하지 않고 Big-Step proof tree를 bottom-up으로 합성한
뒤, tree 결론의 command를 analyzer에 넣어 공격 성공 여부를 확인한다.

# Current Status

- GitHub remote: `https://github.com/gjwj5505/attack.git`, branch `main`.
- Synthesis는 `(prog_size, proof_size)` size table 기반.
- `Partition.rectangular_up_to` / `diagonal_up_to`는 `prog_size = 0`을
  제외한다.
- `Partition.partition_special_while`은 `CWhileTrue` 전용:
  - rest ctree는 같은 while command를 증명하므로
    `rest.prog_size = target.prog_size`.
  - rest proof size는 더 작아서 diagonal order에서 먼저 생성된다.
- `Bottom_up.grow_at_size` 순서:
  - `Grow_prog.grow_at_size`
  - `Grow_proof.grow_at_size`
- Syntax component:
  - exp: Int, Var, Uop, Bop
  - cmd: Assign, Seq, If, While
- Proof tree component:
  - etree: EInt, EVar, EUop, EBop
  - ctree: CAssign, CSeq, CIfTrue, CIfFalse, CWhileTrue, CWhileFalse
- Tests check:
  - generated tree validity with `BigStepChecker`
  - bucket size consistency for exp/cmd/etree/ctree
- `Attack` synthesis exists:
  - `-attack`: find first program whose analyzer result for `x` is top
  - `-attack -bound p q`: find all attacks up to bound
  - config lives in `Synthesis.Config.attack`
  - unbounded `Attack.diagonal_forever` uses delayed syntax scheduling:
    proof sizes are generated first; raw syntax size `(k,0)` is emitted
    immediately before proof target `(k+2,2)`, the first point where a
    raw command of prog size `k` can be needed by `CWhileFalse`.
  - bounded attack still uses `Partition.diagonal_up_to`.
- Pruning exists in `lib/synthesis/prune.ml`:
  - `Grow_prog` adds exp/cmd candidates through `add_pruned_exp` /
    `add_pruned_cmd`.
  - `Grow_proof` adds etree/ctree candidates through `add_pruned_etree` /
    `add_pruned_ctree`.
  - active rules: reject right-nested seq commands, reject `Uminus(Int _)`,
    and reject double unary minus `Uminus(Uminus _)`.
  - pruning decisions are recorded in `.codex/prune.txt`.
- `Visualizer` has a proof-tree-only command printer and short labels:
  - `Int`, `Var`, `Bop`, `Uop`, `Asgn`, `Seq`, `IfT`, `IfF`, `WhlT`, `WhlF`
  - size prints as `(prog,proof)`.

# Important Files

- `lib/synthesis/config.ml`: synthesis config and attack config
- `lib/synthesis/partition.ml`: size enumeration and partitions
- `lib/synthesis/bottom_up.ml`: size-by-size table growth
- `lib/synthesis/grow_prog.ml`: syntax component growth
- `lib/synthesis/grow_proof.ml`: proof tree growth
- `lib/synthesis/attack.ml`: analyzer attack search and unbounded size schedule
- `lib/synthesis/prune.ml`: syntactic pruning predicates
- `lib/synthesis/component/component_set.ml`: size bucket table
- `lib/language/semantics/size.ml`: size definitions
- `lib/language/semantics/bigStep.ml`: proof tree constructors
- `lib/language/semantics/bigStepChecker.ml`: proof validity checker
- `lib/language/semantics/visualizer.ml`: proof tree output
- `lib/analyzer/analyzer.ml`: next major target
- `test/synthesis_test.ml`: synthesis regression tests

# Build / Run

- Build main executable:
  - `dune build @all`
  - or `dune build bin/main.exe`
- Run main executable:
  - `dune exec attack -- <options>`
  - attack search: `dune exec attack -- -attack`
  - bounded attack search: `dune exec attack -- -attack -bound <prog_size> <proof_size>`
  - examples:
    - `dune exec attack -- -attack -bound 3 3`
    - `dune exec attack -- -pp path/to/file`
    - `dune exec attack -- -analyze path/to/file`
    - `dune exec attack -- -big path/to/file`
- Run tests:
  - pass/fail only, stdout hidden on success: `dune runtest`
  - synthesis tests with printed output: `dune exec ./test/synthesis_test.exe`
  - specific synthesis test, e.g. seq: `dune exec ./test/synthesis_test.exe -- -seq`
  - unbounded attack schedule test: `dune exec ./test/synthesis_test.exe -- -forever`
  - all synthesis tests explicitly: `dune exec ./test/synthesis_test.exe -- -all`
