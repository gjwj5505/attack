# Context

This project synthesizes and validates small C programs that can expose false
alarms or unsound results in Sparrow-style interval analysis.

The active implementation is in a language-only CIL' transition phase. CIL' is
the internal source of truth; GoblintCil is used for parsing, pretty-printing,
roundtrip checks, and CIL consistency checks. Detailed language design lives in
`.agents/LANGUAGE.md`.

## Current State

- Entry: `bin/main.ml`
- Executable: `./attack`
- Active CLI options: `-pp`, `-big`, `-ast`
- Active library: `lib/language`
- Analyzer/config/synthesis libraries remain mostly disabled until the CIL'
  Big-Step evaluator and checker are stable enough to reconnect.

Pipelines:

```text
-pp:  C source -> GoblintCil -> CIL' -> Check.check_file -> CIL -> pretty C
-ast: C source -> GoblintCil -> CIL' -> Check.check_file -> SVG AST
-big: C source -> GoblintCil -> CIL' -> Check.check_file
        -> Derivator.derive_file -> BigStepChecker.check_ptree
        -> SVG proof tree
```

Current success examples:

- `examples/simple.c`
- `examples/function_call.c`
- `examples/fibonacci.c`

Useful commands:

```bash
dune build
dune test
dune exec lib/test/bigstepcheck_test.exe
dune exec bin/main.exe -- -pp examples/simple.c
dune exec bin/main.exe -- -ast examples/fibonacci.c
dune exec bin/main.exe -- -big examples/fibonacci.c
```

## Key Files

- `lib/language/syntax.ml`: CIL' AST.
- `lib/language/typ.ml`: CIL' type subset.
- `lib/language/cilBridge.ml`: GoblintCil CIL <-> CIL' conversion.
- `lib/language/check.ml`: thin CIL' checker.
- `lib/language/semantics/runtime/`: locations, values, value operations, and
  memory.
- `lib/language/semantics/proof/bigStep.ml`: proof tree types.
- `lib/language/semantics/proof/derivator.ml`: concrete Big-Step derivation.
- `lib/language/semantics/proof/bigStepChecker.ml`: proof tree checker.
- `lib/language/semantics/typeUtil.ml`: scalar type side conditions for the
  proof checker.
- `lib/test/check_test.ml`: direct CIL' checker tests.
- `lib/test/bigstepcheck_test.ml`: Big-Step checker regression tests.
- `lib/language/semantics/proof/size.ml`: `(program size, proof size)`.

Removed old handwritten parser files:

- `lib/language/lexer.mll`
- `lib/language/parser.mly`

## Current Semantics Snapshot

- The executable Big-Step subset is scalar-integer focused: direct calls,
  conditionals, loops, `break`/`continue`, and returns are supported.
- Pointers and arrays are syntactically present in CIL', but execution remains
  partial. `Mem`, `Index`, field offsets, pointer arithmetic, shift, and
  bitwise operators are unsupported in the current derivator/checker path.
- `Check.check_file` is intentionally structural. Runtime definedness belongs
  in Big-Step derivation and proof checking.
- `-big` runs `Check.check_file` before derivation, then validates the proof
  with `BigStepChecker.check_ptree ~use_check_file:false`. That option only
  controls whether `Check.check_file` is called again; proof-level program
  checks still run.

## Recent Checker Status

`BigStepChecker` now rejects the important invalid proof shapes found in the
2026-07-07 audit:

- block proof trees must match the executed prefix of `block.bstmts`,
  non-empty blocks cannot have empty executions, and execution cannot continue
  after non-normal control;
- instruction and statement sequences must connect memory correctly;
- `return;`, `break`, and `continue` preserve memory;
- loop proof constructors must match body control;
- function proof input/output memory must match frame setup and
  `Memory.leave_function`;
- `FTreeReturn`/`FTreeNoReturn` must match the function return policy;
- whole-program proofs reject ghost callees and non-empty `main` input memory;
- logical `LAnd`/`LOr` must use short-circuit proof constructors;
- direct callees must match function identity and function signature;
- duplicate formal/local names are rejected by `Check.check_file`.

Regression coverage lives in `lib/test/bigstepcheck_test.ml`. It includes
representative invalid proofs for expression, lvalue, instruction, call/type,
statement, block, function, and program-level errors, including both
`ITreeCallAssign` and `ITreeCallVoid` callee-signature mismatches.

## Synthesis Size Policy

Synthesis size is two-dimensional: `(program size, proof size)`.

- `program size` bounds the syntax in proof conclusions.
- `proof size` bounds execution/proof expansion.
- Both dimensions are required for coverage: unexecuted syntax can be large
  while a proof is small, and a small program can have a large finite proof.
- Raw syntax components have proof size `0`; proof components have positive
  program and proof size.
- Program size follows active CIL' AST constructors. Type annotations, source
  locations, statement ids, labels, and other administrative metadata count as
  `0` unless they later become synthesis targets.
- Keep synthesis rules and `lib/language/semantics/proof/size.ml` aligned.

## Next Actions

1. Add global variable allocation and initializer semantics.
2. Add array index lvalue evaluation.
3. Add pointer dereference and pointer arithmetic.
4. Add runtime-error tests for uninitialized reads, division by zero, invalid
   locations, and fuel exhaustion.
5. Re-audit `BigStepChecker` when pointer/array/global execution semantics are
   added.
6. Reconnect synthesis once the evaluator/checker stabilizes.
7. Reconnect Sparrow comparison after exported C compatibility is tested.
