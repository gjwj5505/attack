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
- 2026-06-15 기준 C subset parser/printer 1차 구현이 들어갔다.
  - `lib/language/typ.ml` 추가.
  - `lib/language/syntax.ml`은 C subset AST로 교체.
  - `lib/language/lexer.mll`은 C subset lexer로 교체.
  - `lib/language/parser.mly`은 C subset parser로 교체.
  - `bin/main.ml`은 현재 `-pp`만 help에 노출하고 parse/pretty-print를 수행한다.
  - `lib/language/dune`은 임시로 `typ syntax parser lexer`만 빌드한다.
  - `dune build` 통과.
  - `./attack -pp examples/simple.c`가 성공하고 C 형태로 pretty-print한다.
- `config`, `synthesis`, `analyzer`, `lib/test` dune stanza는 삭제하지 않고
  주석 처리로 임시 비활성화했다.
- `lib/language/semantics/*`, `interpreter.ml` 등 G semantics 모듈은 C 포팅 전이라
  현재 language library 빌드 대상에서 빠져 있다.
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
- 현재 executable은 C subset parse/pretty-print만 노출한다.
- 현재 help에 노출되는 사용 가능 명령: `./attack -pp examples/simple.c`
- `-tab`, `-tintp`, `-dintp`, `-big`은 C 포팅 전까지 help에서 숨겼고,
  관련 함수/flag 일부는 복구용으로 주석 또는 disabled placeholder 상태다.
- `./attack -h`는 `-pp`만 보여준다.
- C Big-Step이 준비되면 `./attack -big examples/simple.c`

# C Subset Implementation Notes

- 상세 언어 설계 문서: `.agents/LANGUAGE.md`.
- 현재 C feature matrix: `.agents/c-feature.csv`.
- Parser와 synthesis는 같은 core AST를 사용하기로 했다.
- Source location과 label은 core AST에 넣지 않는다.
- `Typ`은 별도 모듈 `lib/language/typ.ml`로 둔다.
- `Syntax.id = string`.
- `binding = { typ : Typ.t; name : id }`를 local declaration, future global,
  future parameter가 공유한다.
- `lval`은 현재 `LVar`만 있지만 pointer/array/field lvalue 확장을 위해
  expression variable과 assignment lhs에서 공유한다.
- Expression variable read는 `Exp.Lval (LVar x)`로 표현한다.
- Statement 모듈 이름은 `Stmt`, 기존 `Cmd`는 C AST에서 쓰지 않는다.
- `Stmt.codeblock = Stmt.t list`.
- Empty codeblock은 parser에서 허용한다. `Stmt.codeblock = Stmt.t list`이며
  empty block은 `[]`로 표현한다. 다만 synthesis는 별도 search policy가 생기기
  전까지 empty block을 생성하지 않는다.
- 현재 parser grammar:
  - `int main() { stmt* }`
  - `int x = expr;`
  - `x = expr;`
  - `if (expr) { ... } else { ... }`
  - `while (expr) { ... }`
  - `return expr;`
  - integer expressions: literals, lvalue reads, unary `-`,
    `+ - * / %`, `== != < <= > >=`
- 현재 제외/미결정 feature는 `.agents/c-feature.csv`에서 관리한다.
  semantics 정책 항목은 아직 이 CSV에서 제외했다.

# Next Actions

- `syntax.ml` pretty-printer 출력 형태를 필요하면 더 정돈한다.
  - 현재는 안전하게 괄호를 많이 출력한다.
- C parser smoke example을 subset 전용으로 추가할지 결정한다.
- 다음 큰 구현 단계는 C Big-Step semantics 설계/포팅이다.
  - expression judgment: `<state, expr> ⇓ <state', value>`
  - statement judgment: `<state, stmt> ⇓ control`
  - `control = Normal state | Return (state, value)`부터 시작.
- C semantics를 넣을 때 `lib/language/dune`의 빌드 대상에 semantics 모듈을
  하나씩 되돌린다.
- `-big`, `-tintp`, `-dintp`, `-tab`은 C semantics/labeling 정책이 정리된 뒤
  순서대로 복구한다.
- Analyzer 재활성화는 C syntax + C Big-Step이 안정된 뒤 진행한다.

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
Semantics, AST, memory model, derivator 구조를 설계할 때는 항상 future language
extension을 고려하고, 예상되는 확장을 어렵게 만드는 선택은 피한다.
현재 언어는 faithful C surface subset이 아니라 CIL/Sparrow-facing structural
core로 본다. C-like parser/printer는 facade이며, semantics와 synthesis target은
structural core AST다. 새 feature는 Sparrow CFG command로의 lowering과
Big-Step concrete meaning이 명확할 때만 추가한다.

- Expression judgment: `<state, expr> ⇓ <state', value>`
- Statement judgment: `<state, stmt> ⇓ control`
- `control`은 최소한 `Normal state`, `Return (state, value)`를 포함한다.
  나중에 `Break`, `Continue`를 추가할 수 있게 둔다.
- 초기 pure expression은 `state = state'`인 특수 경우다.
- evaluation order는 일단 deterministic left-to-right subset으로 명시한다.
  ISO C 전체 semantics가 아니라 analyzer attack용 C-like subset이다.
- 현재 expression subset은 pure라 left-to-right proof tree 선택이 관찰 가능한
  차이를 만들지 않는다. Side-effect expression, function call, short-circuit
  operator 등을 추가하기 전에는 Sparrow/CIL lowering이 실제로 어떤 evaluation
  order와 temporary command를 만드는지 작은 예제로 확인한 뒤 Big-Step rule을
  정한다.
- Structural core와 Sparrow 분석 대상의 기준 대응:
  - declaration/assignment는 CIL instruction flattening 이후 `IntraCfg.Cmd.Cset`.
  - `if`는 CFG branch edge에 삽입되는 `Cassume(e)` / `Cassume(!e)`.
  - `while`은 CFG cycle과 body/exit edge의 condition assume.
  - `return e`는 `Creturn(Some e)`.
  - `If`/`Loop` node 자체는 CFG 생성 후 `Cskip`으로 제거된다.
- Analyzer attack의 soundness 비교는 structural Big-Step execution이
  CIL/IntraCfg concrete path 하나와 대응되고, Sparrow abstract semantics가 그
  path의 concrete state를 over-approximate한다는 가정 위에서 한다. 이 가정은
  Sparrow 논문/문서의 soundness 정의 또는 구현의 command transfer semantics를
  근거로 확인해야 한다.
- Sparrow 공식 README/웹페이지는 Sparrow가 abstract interpretation 기반이며
  “sound in design”이라고 설명한다. PLDI 2012 sparse global analysis 슬라이드는
  프로그램을 control points와 control-flow relation으로 보고, 각 control point에
  `assign/alloc/assume/call/return`류 command가 붙는 모델을 사용한다. 이때
  collecting semantics는 program point별 reachable concrete states 집합이고,
  baseline abstract semantics는 각 point에서 reachable states를 subsume하는
  abstract state로 설명된다.
- 구현상 `SparseAnalysis`는 predecessor outputs를 join해 node input을 만들고
  `Sem.run`으로 `IntraCfg.Cmd` abstract transfer를 적용한 뒤 widening/narrowing
  fixpoint를 계산한다. Interval backend의 `ItvSem.run`은 `Cset`, `Cassume`,
  `Creturn` 등을 각각 `eval/update`, `prune`, return-location update로 처리한다.
  따라서 현재 공격 비교의 실질 기준은 CIL 이후 생성된 `IntraCfg.Cmd` path의
  concrete collecting semantics와 `ItvSem` abstract transfer/fixpoint 결과의
  포함 관계다.
- Big-Step state 이름은 `environment`가 아니라 `memory`를 사용한다.
- Runtime value domain은 별도 `Value` 모듈로 두고, 초기에는 `Value.Int`
  서브모듈이 32-bit signed C `int` 연산과 UB 판정을 담당한다.
- Integer literals는 syntax에서 `Int64.t`로 저장한다. 이는 `long long`을
  지원한다는 뜻이 아니라, decimal literal을 parsing 단계에서 안전하게 담고
  Big-Step에서 signed 32-bit `int` 범위/overflow를 엄격히 검사하기 위한
  내부 표현이다.
- Signed `int` overflow, division/modulo by zero, `INT_MIN / -1`,
  `INT_MIN % -1`은 UB이며, UB가 발생한 실행에는 Big-Step tree가 없다.
  Derivator는 디버깅을 위해 UB 이유를 `Error`로 반환한다.
- Memory는 C 변수 모델에 맞춰 `id -> loc` binding과 `loc -> Value.t`
  store를 분리한다.
- Scope는 function frame stack으로 둔다. 현재 subset에서는 `main` frame
  하나만 사용하고, frame 내부 local scope는 flat하게 관리한다. 함수 호출이
  추가되면 call마다 새 frame을 push/pop한다.
- Block scope/shadowing은 initial subset 밖으로 두고, synthesis는 unique
  local names를 생성한다.
- C Big-Step 구현은 작은 단계로 진행한다.
  1. `lib/language/semantics/value.ml` 추가: runtime value domain,
     32-bit signed `Value.Int`, overflow/UB 판정.
  2. `lib/language/semantics/memory.ml` 추가: function frame stack,
     `id -> loc` binding, `loc -> Value.t` store.
  3. `lib/language/semantics/bigStep.ml` 교체: expression/statement/block
     proof tree와 `control`.
  4. `lib/language/semantics/derivator.ml` 교체: deterministic proof builder와
     error propagation.
  5. `lib/language/dune`에 새 semantics modules 추가.

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
