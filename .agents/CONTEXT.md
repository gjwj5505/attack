# Context

정적 분석기가 false alarm 또는 unsound result를 내는 프로그램을 합성하는
프로젝트. 현재 코드는 G 언어 baseline이며, 다음 큰 방향은 C subset 언어로
차근차근 전환하는 것이다.

# Current State

- Entry: `bin/main.ml`, executable: `./attack`.
- 기존 G source extension은 `.g`였고, C rewrite 이후 예제는 `.c`를 사용한다.
- C subset rewrite 준비를 위해 현재 프로젝트는 language-only shell 상태다.
  - `bin/main.ml`은 `-pp`, `-tab`, `-tintp`, `-dintp`, `-big`만 유지한다.
  - `-attack`, `-analyze`, `-forever`, `-objective`, `-bound`는 임시 비활성화됐다.
  - `analyzer`, `attack_config`, `synthesis`, `test` dune stanzas는
    `(enabled_if false)`로 꺼져 있다.
- Attack config는 `Config_util.attack ()`이 만든다.
  - 주요 값: `vars`, `ints`, `value_range`, `uops`, `bops`,
    `heuristic_name`, `analyzer_name`, `seed`.
  - seed는 config에서만 설정하고 CLI 입력으로 받지 않는다.
- 기존 Attack search는 Big-Step proof tree를 bottom-up으로 합성하고, tree 결론의
  command를 analyzer에 넣어 objective를 확인했다. 현재는 C rewrite 동안 꺼져 있다.
- Size는 `(prog_size, proof_size)`.
- 프로그램 시작 concrete memory는 config 변수들에 대해 all-zero로 본다.

# CLI / Commands

- `dune build`
- C parser가 준비되면 `./attack -pp examples/simple.c`
- C Big-Step이 준비되면 `./attack -big examples/simple.c`

# Heuristic / Selection

- Heuristic 구현은 `lib/synthesis/heuristic/` 아래에 둔다.
- `Heuristic` API는 score와 selection 정책을 모두 담당한다.
  - `choose_n`: n개 고르는 기본 선택 함수.
  - `trim`: size bucket을 실제로 pruning하는 함수.
  - `choose_for_grow`: grow 중 rule별 후보를 고르는 함수.
- `choose_for_grow`는 `BigStep.grow_rule`을 받아 rule별/binary/ternary별 정책을
  정한다.
- arity 구분은 `BigStep.arity_of_grow_rule`,
  `BigStep.is_binary_grow_rule`, `BigStep.is_ternary_grow_rule`가 담당한다.
- `Bottom_up.grow_at_size`는 grow를 끝낸 뒤
  `Component_set.trim_size_with_heuristic`으로 현재 size bucket을
  `Heuristic.trim` 결과만 남기게 한다.
- `random1`/`random2`는 component 생성 시 score를 한 번 붙이고, 선택 시 저장된
  score를 사용한다. 기본 trim cap은 1000.

# Analyzer

- Analyzer 선택 껍데기는 `lib/analyzer/analyzer.ml`.
- 실제 analyzer 구현은 버전별 폴더에 있다.
  - `lib/analyzer/engine/v260528/`
  - `lib/analyzer/engine/v260417/`
- 외부 코드는 `Analyzer.analysis`, `Analyzer.analysis_sem`,
  `Analyzer.string_of_aenv`, `Analyzer.print_analysis_sem` 등 wrapper API만 사용한다.

# C Subset Rewrite Plan

목표는 G baseline을 C 분석기 공격용 C subset으로 옮기는 것이다. 초기에는 현재
G와 거의 1:1 대응되는 subset에서 시작하고, C다운 기능을 단계적으로 추가한다.

초기 C subset:

- `int main() { ... }`에서 시작.
- `int x;`, `int x = expr;`
- `x = expr;`
- block `{ stmt* }`
- `if (expr) stmt else stmt`
- `while (expr) stmt`
- `return expr;`
- pure integer expressions: literal, variable, unary `-`, binary
  `+ - * == != < <= > >=`.

초기에는 제외:

- pointer, array, struct
- function call
- side-effect expression (`++`, assignment expression, `+=`, etc.)
- short-circuit `&&`, `||`
- machine integer overflow / UB modeling
- preprocessor

# C Big-Step Design

C subset은 나중에 side-effect expression을 자연스럽게 추가할 수 있게 처음부터
expression semantics를 effect-aware 형태로 둔다.

- Expression judgment: `<state, expr> ⇓ <state', value>`
- Statement judgment: `<state, stmt> ⇓ control`
- `control`은 최소한 `Normal state`, `Return (state, value)`를 포함한다.
  나중에 `Break`, `Continue`를 추가할 수 있게 둔다.
- 초기 pure expression은 `state = state'`인 특수 경우다.
- evaluation order는 일단 deterministic left-to-right subset으로 명시한다.
  ISO C 전체 semantics가 아니라 analyzer attack용 C-like subset이다.

# Important Files

- `bin/main.ml`: CLI.
- `lib/language/`: syntax/parser/printer/semantics.
- `lib/language/semantics/bigStep.ml`: Big-Step tree and grow rule metadata.
- `lib/synthesis/attack.ml`: attack search.
- `lib/synthesis/grow_prog.ml`, `grow_proof.ml`, `grow_util.ml`: component growth.
- `lib/synthesis/component_pool/`: component storage.
- `lib/synthesis/heuristic/`: scoring/selection policy.
- `lib/analyzer/`: analyzer wrapper and engines.
- `examples/simple.c`: initial C subset example.
