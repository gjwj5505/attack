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
- `Visualizer` has a proof-tree-only command printer and short labels:
  - `Int`, `Var`, `Bop`, `Uop`, `Asgn`, `Seq`, `IfT`, `IfF`, `WhlT`, `WhlF`
  - size prints as `(prog,proof)`.

# Important Files

- `lib/synthesis/config.ml`: synthesis config and attack config
- `lib/synthesis/partition.ml`: size enumeration and partitions
- `lib/synthesis/bottom_up.ml`: size-by-size table growth
- `lib/synthesis/grow_prog.ml`: syntax component growth
- `lib/synthesis/grow_proof.ml`: proof tree growth
- `lib/synthesis/attack.ml`: analyzer attack search
- `lib/synthesis/component/component_set.ml`: size bucket table
- `lib/language/semantics/size.ml`: size definitions
- `lib/language/semantics/bigStep.ml`: proof tree constructors
- `lib/language/semantics/bigStepChecker.ml`: proof validity checker
- `lib/language/semantics/visualizer.ml`: proof tree output
- `lib/analyzer/analyzer.ml`: next major target
- `test/synthesis_test.ml`: synthesis regression tests

# Next Priority

Fix analyzer crashes and soundness bugs before trusting synthesized attacks.
