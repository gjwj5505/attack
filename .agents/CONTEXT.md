# Context

This project synthesizes and validates programs that can expose false alarms or
unsound results in Sparrow-style interval analysis.

The current implementation is in a language-only CIL' transition phase. Old
C-like parser and Big-Step code is preserved where useful, but the active
language pipeline is now CIL-based.

## Current State

- Entry: `bin/main.ml`
- Executable: `./attack`
- Active CLI options: `-pp`, `-big`, `-ast`
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

Current `-big` pipeline:

```text
C source
  -> GoblintCil parser
  -> GoblintCil.Cil.file
  -> CIL'
  -> Check.check_file
  -> Derivator.derive_file
  -> BigStep.ptree
  -> BigStepChecker.check_ptree
  -> SVG proof tree in dist/proofs/<basename>.svg
```

Current `-ast` pipeline:

```text
C source
  -> GoblintCil parser
  -> GoblintCil.Cil.file
  -> CIL'
  -> Check.check_file
  -> boxed AST rendering
  -> SVG AST tree in dist/asts/<basename>.svg
```

## Key Files

- `lib/language/syntax.ml`: CIL' AST.
- `lib/language/typ.ml`: CIL' type subset.
- `lib/language/cilBridge.ml`: GoblintCil CIL <-> CIL' conversion.
- `lib/language/check.ml`: thin CIL' checker.
- `lib/language/syntaxEqual.ml`: CIL' structural equality.
- `lib/language/syntaxPretty.ml`: debug string rendering.
- `lib/test/check_test.ml`: direct CIL' checker tests.
- `lib/language/semantics/runtime/`: locations, values, value operations, and
  memory.
- `lib/language/semantics/proof/`: CIL' Big-Step proof trees, proof-tree
  accessors, and derivator.
- `lib/language/semantics/proof/bigStepChecker.ml`: validates Big-Step proof
  trees against their conclusions and the whole-program `main` structure.
- `lib/language/semantics/typeUtil.ml`: scalar CIL' type side-condition checks
  used by Big-Step proof checking.
- `lib/language/semantics/proof/render/`: proof rendering helpers.
- `lib/language/render/textSvg.ml`: shared boxed SVG text renderer for proof
  and AST renderers.
- `lib/language/syntaxTree.ml`: boxed CIL' AST renderer.
- `lib/language/semantics/legacy/`: old Big-Step/reference files not in the
  active build.

Removed old files:

- `lib/language/lexer.mll`
- `lib/language/parser.mly`

## Current Commands

```bash
dune build
dune test
dune exec lib/test/bigstepcheck_test.exe
dune exec bin/main.exe -- -pp examples/simple.c
dune exec bin/main.exe -- -ast examples/fibonacci.c
dune exec bin/main.exe -- -big examples/fibonacci.c
```

Expected behavior:

- current success examples are `examples/simple.c`,
  `examples/function_call.c`, and `examples/fibonacci.c`,
- `-ast` writes `dist/asts/<basename>.svg` and prints AST size,
- `-big` constructs and checks a `BigStep.ptree`, writes
  `dist/proofs/<basename>.svg`, and prints the main return value plus size,
- `dune test` runs direct CIL' checker fixtures and Big-Step checker fixtures.

## Important Design Decisions

Detailed language design lives in `.agents/LANGUAGE.md`.

Current highlights:

- CIL' is the internal source of truth.
- GoblintCil 2.0.9 is used for parsing, pretty-printing, and CIL checks.
- Sparrow uses CIL 1.7.3, so exported C must later be checked for frontend
  compatibility before attack claims rely on it.
- CIL' is cast-free.
- CIL' syntax contains `int`, `unsigned int`, pointers, arrays, function
  definitions/calls, globals, conditionals, loops, break/continue, and returns.
  The currently executable/type-checked Big-Step subset is scalar integer
  focused; pointers, arrays, structs, and dereference/index execution remain
  unsupported unless explicitly added later.
- Unsupported features include structs/unions, field offsets, floats, strings,
  enums, typedefs, varargs, switch, goto, and casts.
- `Check.check_file` is intentionally thin. Runtime definedness belongs in
  Big-Step. `BigStepChecker` separately validates proof trees, including scalar
  type side conditions via `TypeUtil`.

Big-Step proof-tree direction:

- The CIL' Big-Step semantics must eventually be complete for the supported
  CIL' language: every well-defined CIL' program that terminates in finite time
  should have a representable proof tree.
- Runtime errors and nontermination are not represented as successful proof
  trees. They should be reported as derivation errors or fuel exhaustion.
- Fuel is an implementation cutoff for derivation/search, not part of the
  mathematical semantics.
- The proof-tree layers remain aligned with CIL' structure: expression, lvalue,
  instruction, statement, block, function, and file.
- `-big` is restored for the current executable subset. The `-pp` pipeline
  remains useful as parser/bridge validation, while Big-Step proof-tree
  generation is the primary semantics milestone.
- Function execution should be represented separately from call-instruction
  execution. A call instruction tree describes the caller-side effect of a
  `Call`, while a function tree describes callee frame setup, body execution,
  and return.
- Callee resolution is represented by a small proof component (`callee_tree`),
  because CIL' represents the callee of `Call` as an expression. The supported
  callee form is initially `Lval (Var f, NoOffset)` resolving to a known
  `GFun`; indirect/function-pointer calls remain unsupported until later.
  Call-instruction proof trees should include callee resolution, argument
  expression proofs, and an `ftree` premise.
- The user-facing `-big` path should always run `Check.check_file` before
  derivation. The derivator itself should not call the checker, so later
  synthesis/direct callers can choose whether to skip full checking when their
  generator maintains the required invariants.
- Logical `LAnd` and `LOr` must use dedicated short-circuit expression proof
  rules. Do not encode them as ordinary `EBinOp`, because that would force a
  right-hand proof even when C would not evaluate the right operand.
- The CIL' derivator includes `Loop`. Loop execution is bounded by fuel, with
  default fuel 100. `Break` is consumed as normal loop exit, `Continue` starts
  the next iteration, `Return` propagates, and fuel exhaustion is a derivation
  error rather than a proof tree.
- Fuel policy: `Instr` statements do not consume statement fuel; each
  instruction consumes fuel in `derive_instr`. Non-instruction statements
  consume fuel in `derive_stmt`.
- Pointer and array execution is still partial. Variable lvalues with
  `NoOffset`, `AddrOf`, and `StartOf` are implemented. `Mem`, `Index`, field
  offsets, pointer arithmetic, shift, and bitwise operators are still
  unsupported in the current derivator.
- Big-Step control distinguishes `ReturnVoid` from `Return value`. `return;`
  produces `ReturnVoid`; `return exp;` produces `Return value`. Non-void
  functions, including `main`, should reject `ReturnVoid` during derivation.
- Statement and block derivation should not need to know the enclosing function
  return type. `derive_function` is responsible for checking final control
  against the function return type. `Check.check_file` should also statically
  reject return statements whose expression presence does not match the
  enclosing function return type.
- The current `-big` path constructs a `BigStep.ptree`, validates it with
  `BigStepChecker.check_ptree ~check_file:false`, prints size, and writes a
  boxed SVG proof tree.
- Proof-tree constructors use layer-prefixed names such as `ETreeConst`,
  `LTreeVar`, `ITreeSet`, `STreeInstr`, `BTreeSeq`, `FTreeReturn`, and
  `PTreeMainReturn`.
- Block proof trees are flat sequences: `BTreeSeq` stores the list of statement
  proof trees that actually executed. Control and final memory are stored only
  in the block conclusion.
- `ValueOp` is the interface that lowers CIL' operators to primitive
  value-domain operations. `Value` owns runtime value representation and
  primitive integer construction/operations.
- CIL' expressions are pure. Expression proof conclusions do not carry output
  memory; all side effects belong to instructions.

Big-Step checker status:

- `BigStepChecker` has two practical levels:
  subtree checks for expression/lvalue/instruction/statement/block/function
  proof fragments, and `check_ptree` for whole-program proof trees.
- Whole-program checking verifies the optional `Check.check_file` result, that
  the file has exactly one `main`, that the proof's function is that `main`,
  that `main` is called with no arguments, and that `main` returns a value.
- `check_ptree` defaults to `check_file:true`. CLI `-big` calls
  `check_ptree ~check_file:false` because `Check.check_file` already ran before
  derivation.
- Return type checking is context-sensitive. Standalone `check_stree` can be
  called without a return type, but function checking passes the enclosing
  function return type into statement/block checks.
- Scalar type side conditions are checked through `TypeUtil`: assignments,
  calls, expression operators, lvalue reads, and returns must be type-consistent
  without casts or implicit conversions.
- `TypeUtil` currently supports scalar integer types. `Mem`, `Index`, fields,
  `AddrOf`, `StartOf`, pointers, arrays, structs, bitwise/shift operators, and
  pointer arithmetic are rejected as unsupported at the type-checking layer.
- Function proof output memory must equal `Memory.leave_function body_out`.
  Comparing body memory directly with function output memory is wrong because
  the function frame must be popped.
- `ETreeConst` must check both the expression shape and the concrete value.
  A proof such as `1 ⇓ 2` must be rejected.
- Big-Step checker regression coverage lives in
  `lib/test/bigstepcheck_test.ml`. It accepts the current examples and checks
  representative invalid proof trees for expression, lvalue, instruction,
  call/type, statement, block, function, and program-level errors.

Synthesis size policy:

- Synthesis size is two-dimensional: `(program size, proof size)`.
- The core requirement is coverage: if synthesis grows components in increasing
  two-dimensional size, every supported program and every finite terminating
  execution proof should eventually become reachable.
- Both dimensions are necessary.
- `program size` bounds the syntax in proof conclusions. Looking only at
  `proof size` can miss programs whose executed proof is small but whose
  unexecuted syntax is large, such as an `if` whose false branch contains a
  large block.
- `proof size` bounds execution/proof expansion. Looking only at `program size`
  can miss small programs with large finite executions, such as loops with many
  iterations or recursive calls with many unfolded calls.
- Raw syntax components have proof size `0`.
- Proof components have positive program size and positive proof size.
- For a proof tree, `program size` is the size of the program fragment in the
  conclusion, while `proof size` is the size of the proof tree itself.
- Program size follows CIL' AST structure mechanically. Active AST constructors
  and syntax records count as `1`; list and option wrappers count as `0`; type
  annotations, source locations, statement ids, labels, and other administrative
  metadata count as `0` unless they later become synthesis targets.
- Types are not currently synthesized as independent components. Instead,
  synthesis rules should generate only type-correct combinations by checking
  type side conditions when constructing expressions, lvalues, instructions,
  statements, functions, and files.
- If synthesis later starts generating variable declarations, function
  signatures, pointer depth, array shapes, or other type-driven structure more
  directly, revisit whether type structure should contribute to `program size`.
- Synthesis implementation and `lib/language/semantics/proof/size.ml` must stay
  aligned. Whenever a synthesis rule adds, removes, or reinterprets an AST or
  proof constructor, update or re-audit the corresponding size definition at
  the same time.

## Next Actions

1. Re-audit `BigStepChecker` for remaining structural gaps, especially whether
   `BTreeSeq` should verify that executed statement trees correspond to the
   prefix of `block.bstmts`.
2. Add tests for `ITreeCallVoid` and loop-specific proof checker failures if
   those branches are not yet covered enough.
3. Add global variable allocation and initializer semantics.
4. Add array index lvalue evaluation.
5. Add pointer dereference and pointer arithmetic.
6. Add runtime-error tests for uninitialized reads, division by zero, invalid
   locations, and fuel exhaustion.
7. Reconnect synthesis once the evaluator/checker stabilizes.
8. Reconnect Sparrow comparison after exported C compatibility is tested.
