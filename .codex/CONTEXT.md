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
- Program execution assumption:
  - All variables are initialized to `0` at program start.
  - Analyzer attacks must be checked against proof trees whose initial concrete
    memory matches that all-zero initial state.
- Tests check:
  - generated tree validity with `BigStepChecker`
  - bucket size consistency for exp/cmd/etree/ctree
- `Attack` synthesis exists:
  - `-attack`: find first program whose analyzer result satisfies the selected
    objective for `x`
  - `-attack -bound p q`: find all attacks up to bound
  - `-attack -objective <name>` supports `top`, `nonsingleton`, `unbounded`,
    and `unsound`; `unsound` is checked first even when a precision objective is
    selected.
  - config lives in `Synthesis.Config.attack`
  - attack candidates are checked only when the ctree initial concrete env
    matches the all-zero program initial state for `cfg.vars`.
  - unbounded `Attack.diagonal_forever` uses delayed syntax scheduling:
    proof sizes are generated first; raw syntax size `(k,0)` is emitted
    immediately before proof target `(k+2,2)`, the first point where a
    raw command of prog size `k` can be needed by `CWhileFalse`.
  - bounded attack follows the same delayed schedule and filters out sizes not
    needed within the rectangular bound.
  - for raw syntax `(k,0)`, bounded attack keeps it only if the proof target
    `(k+2,2)` is inside the requested bound.
  - progress output distinguishes raw syntax buckets from proof-tree buckets;
    raw lines are printed in blue and skipped sizes are not printed.
- Pruning exists in `lib/synthesis/prune.ml`:
  - `Grow_prog` adds exp/cmd candidates through `add_pruned_exp` /
    `add_pruned_cmd`.
  - `Grow_proof` adds etree/ctree candidates through `add_pruned_etree` /
    `add_pruned_ctree`.
  - active rules include right-nested seq rejection, unary-minus
    canonicalization, commutative bop operand ordering, arithmetic
    identity/absorbing pruning, and independent assignment order
    canonicalization.
  - pruning decisions are recorded in `.codex/prune.txt`.
- Current component-cap experiment:
  - Components are being wrapped as payload + metadata records in
    `lib/synthesis/component_pool/component.ml`.
  - As a temporary stress test, each component gets a random score when it is
    made, and `Synthesis.Attack` caps each grown size bucket to the top 1000
    components by score.
  - This is intentionally heuristic and not the final design. The goal is to
    quickly increase reachable sizes and study where the combinatorial
    bottlenecks move.
  - A bucket-level top-1000 cap reduces stored components but does not prevent
    expensive rule input products. With capped buckets of size 1000, binary
    rules can still try `1000 * 1000` combinations per partition, and ternary
    rules such as `CIfTrue`, `CIfFalse`, and `CWhileTrue` can still try up to
    `1000 * 1000 * 1000` combinations per partition.
  - Current near-term heuristic: cap rule inputs as well as outputs.
    `Grow_util.binary_fanout_cap = 32` and
    `Grow_util.ternary_fanout_cap = 10`. Multiple partitions may still produce
    more than 1000 outputs, so `Synthesis.Attack` keeps the final top-1000
    bucket cap.
  - The full folds are left as comments near the temporary limited folds in
    `Grow_prog` and `Grow_proof`; the new code is explicitly marked as a
    temporary random-score fanout cap.
  - With the current seed and temporary caps, `./attack -attack -objective top`
    finds a top attack at size `(13,16)`:
    `x := 1; while (- x) do x := 0 end; x := x * x`.
  - Longer-term direction: replace random scoring with analyzer-aware priority
    and diversity metrics, and add a schedule that eventually explores beyond
    the current top slice so the search can retain an "eventual success"
    argument rather than becoming a permanent random/top-k prune.
- Attack objective discussion:
  - In the general sense, an analyzer attack succeeds whenever the abstract
    result is strictly less precise than the concrete result; using `top` was
    only an initial, very strong proxy objective.
  - Because this project synthesizes terminating Big-Step proof trees, each
    synthesized execution has one concrete final environment, so each concrete
    variable result is a singleton value for that execution.
  - The current `x == top` success criterion is probably too strong for
    general bottom-up synthesis because it asks for a very large precision
    gap, not just a meaningful false alarm.
  - A better staged objective is to distinguish soundness bugs from precision
    attacks: concrete result not in abstract interval, concrete singleton vs
    non-singleton interval, concrete singleton vs unbounded interval, and only
    finally concrete singleton vs top.
  - The small widening example `while x < 1 do x := x + 1 end` can expose
    one-sided unbounded imprecision, but it does not satisfy the current top
    criterion.
  - Deliberately producing top appears to need both upward and downward
    widening on the target variable, usually with a second loop guard/counter
    variable so the loop exit filter does not refine the target variable back.
  - The hand-written `examples/top.d` attack has size `(28,36)`, so it is
    not realistic for the current unguided bottom-up search.
  - For top attacks, consider a skeleton-guided synthesis mode with holes for
    guards and updates, using the existing components to fill the holes.
  - Analyzer-based ranking can be used as a heuristic inside guided search:
    prefer candidates whose analyzer result has large width, infinity bounds,
    or a large concrete/abstract precision gap, while penalizing size.
  - Next design direction: factor the hard-coded attack success predicate out
    of `Synthesis.Attack` into a swappable objective/module. Candidate
    objectives include exact top, non-singleton precision loss, unbounded
    interval precision loss, and concrete-value-not-contained soundness bugs.
  - When running precision objectives such as `top`, `nonsingleton`, or
    `unbounded`, also check the `unsound` objective. Unsoundness is a distinct,
    more severe analyzer bug and should not be hidden just because the selected
    precision objective requires the abstract value to contain the concrete
    singleton.
- Analyzer module structure:
  - The analyzer library no longer uses `analyzer.ml` as a same-named facade.
  - The analysis engine lives in `lib/analyzer/analyzer_engine.ml` and is
    referenced as `Analyzer.Analyzer_engine`.
  - Other analyzer modules are referenced directly through the wrapped library
    namespace, e.g. `Analyzer.Itv` and `Analyzer.Abs_domain.Abs_env`.
  - This keeps the library namespace distinct from the analysis engine module.
  - `Analyzer_engine.analysis` returns the exit abstract environment.
    `Analyzer_engine.analysis_sem` returns the whole label-to-abstract-env map.
  - `Analyzer.Visualizer` prints `analysis_sem` next to the same program text
    used by `-pp`. `./attack -analyze -v file.d` uses this view.
- `Visualizer` has a proof-tree-only command printer and short labels:
  - `Int`, `Var`, `Bop`, `Uop`, `Asgn`, `Seq`, `IfT`, `IfF`, `WhlT`, `WhlF`
  - size prints as `(prog,proof)`.
- Analyzer attack examples:
  - Successful attacks are logged in `.codex/analyzer-attack-log.md`.
  - Date-stamped runnable programs live in `examples/` using `yymmdd-*.d`
    filenames, e.g. `260421-while-0-truthiness.d`,
    `260511-one-iteration-widening.d`, and
    `260522-unary-guard-square-top.d`.
  - The input language now parses `*` as multiplication (`Times`).

# Important Files

- `lib/synthesis/config.ml`: synthesis config and attack config
- `lib/synthesis/partition.ml`: size enumeration and partitions
- `lib/synthesis/bottom_up.ml`: size-by-size table growth
- `lib/synthesis/grow_prog.ml`: syntax component growth
- `lib/synthesis/grow_proof.ml`: proof tree growth
- `lib/synthesis/attack.ml`: analyzer attack search and unbounded size schedule
- `lib/synthesis/prune.ml`: syntactic pruning predicates
- `lib/synthesis/component_pool/component.ml`: component payload + metadata
- `lib/synthesis/component_pool/component_set.ml`: size bucket table and
  score-based temporary caps
- `lib/language/semantics/size.ml`: size definitions
- `lib/language/semantics/bigStep.ml`: proof tree constructors
- `lib/language/semantics/bigStepChecker.ml`: proof validity checker
- `lib/language/semantics/visualizer.ml`: proof tree output
- `lib/analyzer/analyzer_engine.ml`: analyzer worklist engine
- `lib/analyzer/visualizer.ml`: analyzer result + program output
- `lib/analyzer/itv.ml`: interval domain implementation
- `lib/synthesis/objective.ml`: swappable attack success objectives
- `test/synthesis_test.ml`: synthesis regression tests

# Build / Run

- Build main executable:
  - `dune build @all`
  - `dune build`
  - or `dune build bin/attack`
  - building `bin/attack` promotes a root-level `./attack` executable
- Run main executable:
  - `dune exec attack -- <options>`
  - after `dune build bin/attack`, run promoted executable directly:
    `./attack <options>`
  - attack search: `dune exec attack -- -attack`
  - direct attack search after build: `./attack -attack`
  - objective attack search:
    `dune exec attack -- -attack -objective <top|nonsingleton|unbounded|unsound>`
  - bounded attack search: `dune exec attack -- -attack -bound <prog_size> <proof_size>`
  - examples:
    - `dune exec attack -- -attack -bound 3 3`
    - `dune exec attack -- -pp path/to/file`
    - `dune exec attack -- -analyze path/to/file`
    - `dune exec attack -- -analyze -v path/to/file`
    - `dune exec attack -- -big path/to/file`
- Run tests:
  - pass/fail only, stdout hidden on success: `dune runtest`
  - synthesis tests with printed output: `dune exec ./test/synthesis_test.exe`
  - specific synthesis test, e.g. seq: `dune exec ./test/synthesis_test.exe -- -seq`
  - unbounded attack schedule test: `dune exec ./test/synthesis_test.exe -- -forever`
  - all synthesis tests explicitly: `dune exec ./test/synthesis_test.exe -- -all`
