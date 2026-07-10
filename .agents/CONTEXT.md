# Context

This project synthesizes and validates small C programs that can expose false
alarms or unsound results in Sparrow-style interval analysis.

The active implementation is in a language-only CIL-- transition phase. CIL-- is
the internal source of truth; GoblintCil is used for parsing, pretty-printing,
roundtrip checks, and CIL consistency checks. Detailed language design lives in
`.agents/LANGUAGE.md`.

## Current State

- Entry: `bin/main.ml`
- Executable: `./attack`
- Active CLI options: `-pp`, `-big`, `-ast`, `-v`
- `-v` augments `-big` proof rendering with global and active top-stack
  memory. Empty global state is omitted; heap state is not rendered.
- Active library: `lib/language`
- Analyzer/config/synthesis libraries remain mostly disabled until the CIL--
  Big-Step evaluator and checker are stable enough to reconnect.

Pipelines:

```text
-pp:  C source -> GoblintCil -> CIL-- -> AstChecker.check_file -> CIL -> pretty C
-ast: C source -> GoblintCil -> CIL-- -> AstChecker.check_file -> SVG AST
-big: C source -> GoblintCil -> CIL-- -> AstChecker.check_file
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

- `lib/language/syntax.ml`: CIL-- AST.
- `lib/language/typ.ml`: CIL-- type subset.
- `lib/language/cilBridge.ml`: GoblintCil CIL <-> CIL-- conversion.
- `lib/language/astChecker.ml`: thin CIL-- AST checker.
- `lib/language/semantics/runtime/`: locations, values, value operations, and
  memory.
- `lib/language/semantics/proof/bigStep.ml`: proof tree types.
- `lib/language/semantics/proof/derivator.ml`: concrete Big-Step derivation.
- `lib/language/semantics/proof/bigStepChecker.ml`: proof tree checker.
- `lib/language/semantics/typeUtil.ml`: scalar type side conditions for the
  proof checker.
- `lib/test/astcheck_test.ml`: direct CIL-- AST checker tests.
- `lib/test/bigstepcheck_test.ml`: Big-Step checker regression tests.
- `lib/language/semantics/proof/size.ml`: `(program size, proof size)`.

Removed old handwritten parser files:

- `lib/language/lexer.mll`
- `lib/language/parser.mly`

## Current Semantics Snapshot

- The active checked/executable value type is `int`. `void` is used only for
  functions that return no value, and `Typ.TFun` carries function signatures.
- The executable Big-Step subset supports direct calls, conditionals, loops,
  `break`/`continue`, blocks, assignments, and returns.
- Pointers and arrays are syntactically present in CIL--, but execution remains
  partial. `Mem`, `Index`, field offsets, pointer arithmetic, shift, and
  bitwise operators are unsupported in the current derivator/checker path.
- `AstChecker.check_file` is intentionally structural. Runtime definedness belongs
  in Big-Step derivation and proof checking.
- `-big` runs `AstChecker.check_file` before derivation, then validates the proof
  with `BigStepChecker.check_ptree ~use_check_file:false`. That option only
  controls whether `AstChecker.check_file` is called again; proof-level program
  checks still run.

## Recent Checker Status

2026-07-10 checkpoint:

- `AstChecker.check_file` has 57 passing direct regression cases.
- `BigStepChecker` has 105 passing direct/end-to-end regression cases.
- `dune build`, `lib/test/astcheck_test.exe`, and
  `lib/test/bigstepcheck_test.exe` pass.
- Detailed checker policies and test mappings are recorded in
  `.agents/astcheck.md` and `.agents/bigstepcheck.md`.

`BigStepChecker` rejects the important invalid proof shapes found during the
checker audits:

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
- every subtree boundary memory must satisfy `Memory.check_well_formed`;
- standalone function proofs validate int arguments, function/formal/local
  scope and metadata, duplicate names, and local occurrences in the body;
- duplicate formal/local names are rejected by both the relevant standalone
  function checks and `AstChecker.check_file`.

Regression coverage lives in `lib/test/bigstepcheck_test.ml`. It includes
representative invalid proofs for expression, lvalue, instruction, call/type,
statement, block, function, and program-level errors, including both
`ITreeCallAssign` and `ITreeCallVoid` callee-signature mismatches. Top-frame
coverage includes nested caller restoration, callee-local disposal, global
update propagation, and forged-memory rejection.

## Synthesis Size Policy

Synthesis size is two-dimensional: `(program size, proof size)`.

- `program size` bounds the syntax in proof conclusions.
- `proof size` bounds execution/proof expansion.
- Both dimensions are required for coverage: unexecuted syntax can be large
  while a proof is small, and a small program can have a large finite proof.
- Raw syntax components have proof size `0`; proof components have positive
  program and proof size.
- Program size follows active CIL-- AST constructors. Type annotations, source
  locations, statement ids, labels, and other administrative metadata count as
  `0` unless they later become synthesis targets.
- Keep synthesis rules and `lib/language/semantics/proof/size.ml` aligned.

## Big-Step Synthesis Memory Policy

Both `-big` derivation and bottom-up synthesis use one top-only memory
representation. There is no separate full-stack mode.

Memory is divided by storage area into stack, global, and heap state. Each area
uses a `storage` value for its allocated objects and stored values. The stack
state contains only the currently active top frame.

The derivator's OCaml recursion retains the caller stack during a function call.
`enter_function` replaces the active stack state with an empty callee stack
while preserving global and heap state. `leave_function ~caller_stack mem`
replaces only the current stack and keeps the current global and heap state
unchanged.

`BigStep.f_concl` keeps its existing shape. Its input and output memories are
the caller-visible states before and after the call, while its child `btree`
carries the callee's top-frame state.

The checker continues to compare `Memory.t` strictly. Since `Memory.t` contains
only the top stack state plus global and heap state, no hidden stack tail is
ignored. Function-boundary checks reconstruct the expected callee input and
caller output using `enter_function` and `leave_function`.

Strict equality is preceded by `Memory.check_well_formed` at every proof
subtree boundary. The active int-only policy checks storage namespaces, object
IDs and sizes, `next_object_id`, binding scope/location uniqueness, store
locations, and `Value.Int IInt` contents. Equal but malformed memories are
therefore rejected.

Pointer reachability is not a separate storage area. When pointer execution is
implemented, the memory view must additionally retain stack objects reachable
across function boundaries.

## Synthesis Reconnect Plan

Reconnect synthesis incrementally while preserving the old file roles.

Initial temporary target:

- synthesize a `simple.c`-level scalar CIL-- program;
- no `if`, loop, function call, global, pointer, or array generation yet;
- validate generated candidates through `AstChecker.check_file`,
  `Derivator.derive_file`, `BigStepChecker.check_ptree ~use_check_file:false`,
  and `Objective.concrete_of_ptree`.

Implementation plan:

1. Rewrite `lib/synthesis/component_pool/` for CIL-- candidate components.
   Current component layers are syntax `exp`, `lval`, `offset`, `instr`,
   `stmt`, `block`, `fundec`, `init`, `global`, `file` and proof `etree`,
   `ltree`, `itree`, `stree`, `btree`, `ftree`, `ptree`.
2. Temporarily implement `bottom_up.ml` as the owner of the small hardcoded
   candidate generator, while preserving `grow_at_size` and `build_up_to`.
3. Rewrite `attack.ml` around candidate search from the bottom-up table.
   Keep `attack_result` as the future analyzer/objective result type, with
   `Objective.witness` carrying concrete and analyzer observations.
4. Re-enable the minimal `synthesis` library in dune and connect a small CLI
   option after the library builds.
5. Replace the temporary hardcoded candidate with real bottom-up grow rules for
   expressions, assignments, returns, blocks, and `main` files.

Current progress:

- `Syntax.ast` was added as a wrapper for the syntax component layers.
- `lib/synthesis/objective.ml` now contains CIL-- observation/witness placeholder
  types, with concrete `int main` return values explicitly narrowed to
  `Value.int_value`.
- `lib/synthesis/component_pool/component.ml`, `component_set.ml`, and `util.ml`
  were rewritten for the CIL-- syntax/proof component layers listed above.
- The language, top-only memory model, derivator, AstChecker, and
  BigStepChecker are ready for the minimal int-only synthesis target.
- `bottom_up.ml`, `attack.ml`, synthesis dune re-enabling, and CLI connection
  are still pending.

Presentation note:

- Show-and-tell title/abstract for this work are recorded in
  `.agents/Show&Tell.notice`.

## Next Actions

1. In the next session, inspect the existing `lib/synthesis` state and reconnect
   minimal int-only CIL-- synthesis as described above.
2. Add global variable allocation and initializer semantics.
3. Add array index lvalue evaluation.
4. Add pointer dereference and pointer arithmetic.
5. Add runtime-error tests for uninitialized reads, division by zero, invalid
   locations, and fuel exhaustion.
6. Re-audit `BigStepChecker` when pointer/array/global execution semantics are
   added.
7. Reconnect Sparrow comparison after exported C compatibility is tested.
