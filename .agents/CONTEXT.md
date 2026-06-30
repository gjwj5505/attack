# Context

This project synthesizes and validates programs that can expose false alarms or
unsound results in Sparrow-style interval analysis.

The current implementation is in a language-only CIL' transition phase. Old
C-like parser and Big-Step code is preserved where useful, but the active
language pipeline is now CIL-based.

## Current State

- Entry: `bin/main.ml`
- Executable: `./attack`
- Active CLI option: `-pp`
- Disabled for now: old `-big` proof-tree mode
- Active language library: `lib/language`
- Analyzer/config/synthesis/test libraries are mostly disabled in their dune
  files until the CIL' semantics is ready.

Current `-pp` pipeline:

```text
C source
  -> GoblintCil parser
  -> GoblintCil.Cil.file
  -> CIL'
  -> Check.check_file
  -> CIL
  -> GoblintCil pretty printer
```

## Key Files

- `lib/language/syntax.ml`: CIL' AST.
- `lib/language/typ.ml`: CIL' type subset.
- `lib/language/cilBridge.ml`: GoblintCil CIL <-> CIL' conversion.
- `lib/language/check.ml`: thin CIL' checker.
- `lib/language/syntaxEqual.ml`: CIL' structural equality.
- `lib/language/syntaxPretty.ml`: debug string rendering.
- `lib/test/check_test.ml`: direct CIL' checker tests.
- `lib/language/semantics/`: old Big-Step implementation, preserved as
  reference for the CIL' port.

Removed old files:

- `lib/language/lexer.mll`
- `lib/language/parser.mly`

## Current Commands

```bash
dune build
dune runtest
./attack -pp examples/cil_small_while.c
./attack -pp examples/cil_branch_loop.c
./attack -pp examples/cil_pointer_array_call.c
./attack -pp examples/unsupported_cast_implicit.c
```

Expected behavior:

- the first three `-pp` examples succeed,
- `unsupported_cast_implicit.c` fails with `unsupported CIL feature: cast expression`,
- `dune runtest` runs direct CIL' checker fixtures.

## Important Design Decisions

Detailed language design lives in `.agents/LANGUAGE.md`.

Current highlights:

- CIL' is the internal source of truth.
- GoblintCil 2.0.9 is used for parsing, pretty-printing, and CIL checks.
- Sparrow uses CIL 1.7.3, so exported C must later be checked for frontend
  compatibility before attack claims rely on it.
- CIL' is cast-free.
- CIL' currently supports `int`, `unsigned int`, pointers, arrays, function
  definitions/calls, globals, conditionals, loops, break/continue, and returns.
- Unsupported features include structs/unions, field offsets, floats, strings,
  enums, typedefs, varargs, switch, goto, and casts.
- The checker is intentionally thin. Runtime definedness belongs in Big-Step.

Big-Step proof-tree direction:

- The CIL' Big-Step semantics must eventually be complete for the supported
  CIL' language: every well-defined CIL' program that terminates in finite time
  should have a representable proof tree.
- Runtime errors and nontermination are not represented as successful proof
  trees. They should be reported as derivation errors or fuel exhaustion.
- Fuel is an implementation cutoff for derivation/search, not part of the
  mathematical semantics.
- Start with a minimal executable subset, but keep the proof-tree layers aligned
  with CIL' structure: expression, lvalue, instruction, statement, block,
  function, and file.
- The current implementation target is to restore `-big` for CIL'. The `-pp`
  pipeline remains useful as parser/bridge validation, but Big-Step proof-tree
  generation is now the primary milestone.
- Function execution should be represented separately from call-instruction
  execution. A call instruction tree describes the caller-side effect of a
  `Call`, while a function tree describes callee frame setup, body execution,
  and return.
- Callee resolution should eventually become its own small proof component
  (`callee_tree` or equivalent), because CIL' represents the callee of `Call` as
  an expression. The first implementation may support only direct calls and
  postpone this tree until calls are implemented.
- Do not put unsupported calls in successful proof trees. Until call semantics
  is implemented, `Call` should be a derivation error. After the first minimal
  CIL' `-big` path works, add function call semantics next.

## Next Actions

1. Port Big-Step semantics to CIL'.
2. Define values, addresses, memory, and environments.
3. Implement expression/lvalue evaluation.
4. Implement instruction/statement/block/function evaluation.
5. Reintroduce proof trees for CIL'.
6. Reconnect synthesis once the evaluator stabilizes.
7. Reconnect Sparrow comparison after exported C compatibility is tested.
