# Context

This project synthesizes and validates programs that can expose false alarms or
unsound results in Sparrow-style interval analysis.

The current implementation is in a language-only CIL' transition phase. Old
C-like parser and Big-Step code is preserved where useful, but the active
language pipeline is now CIL-based.

## Current State

- Entry: `bin/main.ml`
- Executable: `./attack`
- Active CLI options: `-pp`, `-big`
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
- `lib/language/semantics/proof/render/`: proof rendering helpers.
- `lib/language/semantics/legacy/`: old Big-Step/reference files not in the
  active build.

Removed old files:

- `lib/language/lexer.mll`
- `lib/language/parser.mly`

## Current Commands

```bash
dune build
dune runtest
./attack -pp examples/small_while.c
./attack -pp examples/branch_loop.c
./attack -pp examples/pointer_array_call.c
./attack -pp examples/unsupported_cast_implicit.c
./attack -big examples/small_while.c
./attack -big examples/branch_loop.c
./attack -big examples/call.c
```

Expected behavior:

- the first three `-pp` examples succeed,
- `unsupported_cast_implicit.c` fails with `unsupported CIL feature: cast expression`,
- the listed `-big` examples construct a `BigStep.ptree` and print the main
  return value,
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
- The current `-big` milestone constructs a `BigStep.ptree`; proof-tree
  visualization/pretty-printing remains separate follow-up work.
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

## Next Actions

1. Implement pretty-printing / visualization for the generated CIL' Big-Step
   proof tree.
2. Add global variable allocation and initializer semantics.
3. Add array index lvalue evaluation.
4. Add pointer dereference and pointer arithmetic.
5. Add runtime-error tests for uninitialized reads, division by zero, invalid
   locations, and fuel exhaustion.
6. Reconnect synthesis once the evaluator stabilizes.
7. Reconnect Sparrow comparison after exported C compatibility is tested.
