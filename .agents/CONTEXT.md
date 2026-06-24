# Context

정적 분석기, 특히 Sparrow 계열 interval analyzer가 false alarm 또는 unsound
result를 내는 프로그램을 합성하고 검증하는 프로젝트다. G 언어 baseline에서
C-like Big-Step layer로 옮겼고, 다음 목표는 이를 Sparrow/CIL에 더 직접 대응되는
structural core로 정리하는 것이다.

## Current State

- Entry: `bin/main.ml`, executable: `./attack`.
- 현재 입력 예제는 `.c`를 사용한다. G 예제는 `examples/deprecated/`에 보존.
- Analyzer/config/synthesis/test 쪽은 임시 비활성화되어 있고, 현재는
  language-only 중심으로 빌드한다.
- Analyzer wrapper와 vendored Sparrow source는 보존되어 있다.
- 주요 명령:
  - `dune build`
  - `./attack -pp examples/branch_loop.c`
  - `./attack -big examples/branch_loop.c`
  - `./attack -big -v examples/branch_loop.c`
- `-big`은 Big-Step proof tree를 derive해서 같은 basename의 `.svg`로 저장한다.
- `-v`는 proof conclusion에 memory를 `{x |-> 1}` 형태로 표시한다.

## Implemented Language Layer

현재 구현은 C-like parser, Big-Step derivator, SVG visualizer까지 연결된 상태다.
언어 문법과 semantics 세부사항은 `.agents/LANGUAGE.md`가 source of truth다.

핵심 파일:

- `lib/language/syntax.ml`, `lexer.mll`, `parser.mly`: C-like syntax layer.
- `lib/language/semantics/value.ml`: signed 32-bit `int` value와 UB 판정.
- `lib/language/semantics/memory.ml`: frame, location, store 기반 memory.
- `lib/language/semantics/bigStep.ml`: proof tree type.
- `lib/language/semantics/derivator.ml`: deterministic proof builder.
- `lib/language/semantics/visualizer.ml`, `textSvg.ml`: SVG proof output.

Big-Step derivation now handles both successful examples and no-tree error
cases. Error policy details are in `.agents/LANGUAGE.md`.

## Validation

Success examples:

- `examples/small_while.c`
- `examples/branch_loop.c`: expected and observed final result is `15`.

Error examples:

- `examples/error_div_zero.c`
- `examples/error_overflow.c`
- `examples/error_literal_overflow.c`
- `examples/error_missing_return.c`
- `examples/error_unbound.c`
- `examples/error_duplicate.c`
- `examples/error_out_of_fuel.c`

All error examples should fail with `Big-Step derivation failed: ...` and not
create an SVG.

## CIL / Sparrow Direction

Next target: stop expanding faithful C surface syntax and define a
CIL/Sparrow-facing structural core.

Detailed CIL/Sparrow correspondence belongs in `.agents/LANGUAGE.md`. The
context-level point is that future synthesis/semantics work should target that
core, not a broader faithful-C surface language.

## Next Actions

1. Define the CIL-facing core AST.
2. Decide statement/block core vs explicit CFG-edge core.
3. Specify mapping from current C-like surface syntax to the core.
4. Move `bigStep.ml` and `derivator.ml` to use that core as source of truth.
5. Reconnect synthesis after core semantics stabilizes.
6. Reconnect Sparrow analyzer wrapper and compare against Sparrow results.
