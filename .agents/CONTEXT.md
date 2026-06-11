# Context

정적 분석기가 false alarm 또는 unsound result를 내는 프로그램을 합성하는
프로젝트. 현재 코드는 G 언어 baseline이며, 다음 큰 방향은 C subset 언어로
차근차근 전환하는 것이다.

# Current State

- Entry: `bin/main.ml`, executable: `./attack`.
- 기존 G source extension은 `.g`였고, C rewrite 이후 예제는 `.c`를 사용한다.
- 프로젝트는 G baseline에서 C/Sparrow analyzer attack 쪽으로 전환 중이다.
- 현재는 C subset 언어 정의에 집중하기 위해 language-only 빌드 상태로
  줄여두었다.
- `config`, `synthesis`, `analyzer`, `lib/test` dune stanza는 삭제하지 않고
  주석 처리로 임시 비활성화했다.
- C 언어 정의가 준비되면 analyzer를 가장 먼저 다시 활성화한다.
- Attack/synthesis 연결 코드는 보존되어 있지만, 현재 빌드 대상에서는 빠져 있다.
- analyzer wrapper는 Sparrow를 Docker로 호출하는 구조를 유지한다.
- 현재 합성기는 아직 G AST/program을 만들지만, analyzer는 이를 text로 출력해
  `.i` 파일처럼 Sparrow에 강제로 넣는다.
  - 따라서 G 문법이 C와 맞지 않는 동안에는 Sparrow parse/analyzer 실패가
    정상적으로 발생할 수 있다.
- Attack config는 `Config_util.attack ()`이 만든다.
  - 주요 값: `vars`, `ints`, `value_range`, `uops`, `bops`,
    `heuristic_name`, `analyzer_name`, `seed`.
  - seed는 config에서만 설정하고 CLI 입력으로 받지 않는다.
- 기존 Attack search는 Big-Step proof tree를 bottom-up으로 합성하고, tree 결론의
  command를 analyzer에 넣어 objective를 확인한다.
- Size는 `(prog_size, proof_size)`.
- 프로그램 시작 concrete memory는 config 변수들에 대해 all-zero로 본다.

# CLI / Commands

- `dune build`
- 현재 executable은 language commands만 노출한다.
- 현재 사용 가능: `./attack -pp`, `./attack -tab`, `./attack -tintp`,
  `./attack -dintp`, `./attack -big`
- C parser가 준비되면 `./attack -pp examples/simple.c`
- C Big-Step이 준비되면 `./attack -big examples/simple.c`

# Heuristic / Selection

- Heuristic 구현은 `lib/synthesis/heuristic/` 아래에 둔다.
- Heuristic은 새 `analysis_result` 전체를 직접 받지 않는다.
- 기존처럼 `Analyzer.find target_var aenv`를 통해 target 변수 하나의 abstract
  value만 본다.
- 현재 `Analyzer.aval = Sparrow_result.value option`.
- `None`은 아직 top처럼 취급된다. 이건 나중에 실패/변수없음/진짜 top을 분리할
  때 고친다.
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

- Analyzer wrapper는 `lib/analyzer/analyzer.ml`.
- 현재 backend는 vendored Sparrow Docker image `attack-sparrow`.
- Sparrow source는 `lib/analyzer/sparrow/src/`, Docker build 환경은
  `lib/analyzer/sparrow/docker/`.
- Sparrow에 `-json_dump` 옵션을 추가했고, interval analysis 결과를 JSON으로
  dump한다.
- Local analyzer는 그 JSON을 `Sparrow_result` / `Sparrow_result_json` 모듈로
  파싱해 `analysis_result`에 저장한다.
- Sparrow JSON은 `main_exit_node`를 포함한다. 현재 이 값은 synthetic
  `main-EXIT`이 아니라, `main-EXIT`으로 들어가는 predecessor node다.
- `Analyzer.find var aenv`는 `main_exit_node`의 input memory를 먼저 보고 target
  변수 바인딩을 찾는다.
- `main_exit_node` input에서 찾지 못하면 기존 호환성을 위해 JSON `output`
  배열을 뒤에서부터 훑는 fallback을 사용한다.
- 디버그 확인은 `./attack -sparrow-find <var> examples/simple.i`로 한다.

# Sparrow JSON / Analysis Result

현재 dump 구조:

- `file`
- `analysis`
- `main_exit_node`
- `alarms`
- `input`
- `output`

현재 연결 규칙:

- `main_exit_node`는 `InterCfg.exitof global.icfg "main"` 자체가 아니라 그
  synthetic EXIT node의 main-local predecessor다.
- `Analyzer.find`는 해당 node의 `input` memory를 main 종료 상태로 본다.
- 현재 C subset은 pure return expression을 전제로 하므로 return node input을
  보는 것이 충분하다. side-effect expression을 추가하면 이 가정을 다시 본다.

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
- `lib/analyzer/sparrow/src/src/instance/itvAnalysis.ml`: Sparrow JSON dump 구현.
- `lib/analyzer/sparrow_result.ml`: 분석 결과 OCaml type.
- `lib/analyzer/sparrow_result_json.ml`: JSON -> 분석 결과 변환.
- `lib/analyzer/sparrow/docker/Dockerfile`: Sparrow build image.
- `examples/simple.c`: initial C subset example.
