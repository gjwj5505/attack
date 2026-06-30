# Language Design

This project no longer treats a hand-written C-like parser as the language
source of truth. The current language target is a Sparrow-facing, CIL-shaped
subset called CIL'.

## Goal

The purpose of CIL' is to synthesize and execute small deterministic programs
whose concrete final memory can be compared against Sparrow's abstract result.

The intended pipeline is:

```text
C source
  -> GoblintCil parser
  -> GoblintCil.Cil.file
  -> CIL'
  -> Check.check_file
  -> Big-Step / synthesis / objective
```

For generated attacks:

```text
Synthesized CIL'
  -> optional Check.check_file
  -> Big-Step concrete execution
  -> CIL
  -> pretty-printed C
  -> Sparrow input
```

## CIL and CIL'

- CIL means the external OCaml CIL representation from `goblint-cil`.
- CIL' means the internal supported subset in `lib/language/syntax.ml`.

CIL is used for parsing, pretty-printing, library utilities, and sanity checks.
CIL' is the source of truth for synthesis, Big-Step semantics, proof trees, and
attack objectives.

CIL' follows CIL constructor shapes where useful:

- `file -> global list`
- `GFun -> fundec`
- `fundec -> svar, sformals, slocals, sbody`
- `block -> stmt list`
- `stmt -> stmtkind`
- `instr` for control-flow-free actions
- `lval = lhost * offset`
- `lhost = Var | Mem`
- `offset = NoOffset | Field | Index`
- `exp` is side-effect-free

CIL' records are immutable for now. If later passes need labels, statement ids,
CFG metadata, analysis annotations, or proof annotations attached after
construction, make the relevant fields mutable in the CIL style at that point.

## Current Active Subset

Types:

- `void`
- `int`
- `unsigned int`
- pointers
- arrays with constant integer length or unknown length
- non-vararg function types

Globals:

- function definitions
- global variable declarations
- global variable definitions with initializers

Statements and instructions:

- instruction statements
- assignment
- function call
- return
- if
- loop
- break
- continue
- block

Expressions and lvalues:

- integer constants
- lvalue reads
- unary operators
- binary operators, including pointer arithmetic operators
- address-of
- array start
- variable lvalues
- memory lvalues
- array index offsets

## Excluded Features

These features are outside CIL' until explicitly designed:

- casts
- all integer kinds except `int` and `unsigned int`
- floating-point types and constants
- string and character constants
- structs and unions
- field offsets
- enums
- typedefs
- varargs
- inline assembly
- goto and computed goto
- switch/case/default
- source locations as active semantic data

Some excluded CIL constructors remain as comments beside the corresponding
active definitions in `syntax.ml`. That is intentional: the file records the
relationship to GoblintCil while keeping the active AST small.

## Cast-Free Policy

CIL' is a cast-free lowered CIL subset. There is no active `CastE` constructor.

This avoids having to distinguish source-level explicit casts from C front-end
implicit conversions. If GoblintCil lowers a C source program into CIL containing
`CastE`, the CIL -> CIL' bridge rejects it.

Consequences:

- CIL' contains no implicit casts.
- CIL' contains no explicit casts.
- Binary operations must already have matching operand/result types.
- Assignments and calls must be type-consistent without relying on conversion.
- Mixed signedness examples such as `int + unsigned int` are rejected because
  GoblintCil inserts casts.

If casts are needed later, add them one narrow case at a time with a precise
Big-Step rule and Sparrow CIL 1.7.3 compatibility check.

## Bridge Policy

`lib/language/cilBridge.ml` implements conversion between GoblintCil CIL and
CIL'.

- CIL' -> CIL should be total for checked CIL' programs.
- CIL -> CIL' accepts only the supported subset.
- Unsupported CIL features return explicit errors.
- Builtin declarations inserted by GoblintCil, such as `__builtin_*`,
  `__sync_*`, `__atomic_*`, and `__builtin_va_list`, are filtered from external
  input before conversion.

The bridge also provides roundtrip checking:

```text
CIL' -> CIL -> CIL'
```

Roundtrip equality is structural CIL' equality. Statement ids are ignored.

## Checker Policy

`lib/language/check.ml` is a thin structural checker, not a full C typechecker.

It currently checks:

- exactly one `main`
- `main` has return type `int`
- `main` has no parameters
- duplicate global names
- `break` outside loops
- `continue` outside loops
- CIL' roundtrip stability
- GoblintCil `Check.checkFile` on the converted CIL

GoblintCil's checker is used for CIL internal consistency, type consistency,
varinfo sharing, initializer consistency, call consistency, and related CIL
invariants.

The CIL' checker exists because some invariants are enforced by the C parser,
not by GoblintCil's CIL checker. For example, C source cannot contain a
top-level loop-free `break`, but a synthesizer can directly construct such a
CIL' AST.

The checker is useful for CLI input validation and synthesis debugging. The
final synthesis hot path may skip it if the generator itself maintains these
invariants.

## Runtime Errors

The checker does not try to prove runtime definedness. These are Big-Step
runtime errors or no-tree cases:

- uninitialized read
- division or modulo by zero
- invalid pointer dereference
- null pointer dereference, if null is later introduced
- out-of-bounds array access
- missing function body at call time
- nonzero `main` return for normal-completion comparisons
- fuel exhaustion / nontermination cutoff

This separation matches C practice: parser/type checking handles syntax and
type correctness, while runtime undefinedness is not fully rejected by the
front-end.

## Sparrow Compatibility

Sparrow reportedly uses CIL 1.7.3. GoblintCil 2.0.9 is only a utility layer for
this project.

For soundness/completeness attacks, CIL' Big-Step behavior must match the
concrete behavior of the exported C program as parsed and lowered by Sparrow's
CIL 1.7.3 frontend.

Before relying on a feature for attacks, check that:

```text
CIL' Big-Step concrete execution
  = concrete behavior of exported C under Sparrow CIL 1.7.3 lowering
```

Only then can the result be compared against Sparrow's abstract analysis.

## Examples Policy

Example files use `.c` because CIL is an OCaml AST, not a source-file syntax.
Examples should be C source programs whose GoblintCil-lowered CIL belongs to
the supported CIL' subset.

Success examples should avoid features outside CIL'. Unsupported examples
should be named clearly, such as `unsupported_cast_implicit.c`, and should have
an expected rejection reason.

Current examples include:

- `examples/cil_small_while.c`
- `examples/cil_branch_loop.c`
- `examples/cil_pointer_array_call.c`
- `examples/unsupported_cast_implicit.c`

Control-flow cases that cannot be represented as valid C source, such as
loop-free `break`, should be tested by constructing CIL' ASTs directly in OCaml
unit tests.

## Attack Observables

Source locals and CIL temporary variables are not distinguished. Both are local
memory bindings.

A concrete run is considered normally completed only when `main` returns `0`.
The return value itself is not an attack observable.

Soundness/completeness comparison uses all live local memory bindings at normal
`main` exit:

- soundness failure: the concrete value is not included in the analyzer result
- completeness/precision failure: the analyzer result is wider than the
  singleton abstraction of the concrete value

## Next Semantics Work

The next implementation step is to port Big-Step semantics to CIL'.

Suggested order:

1. define CIL' values,
2. define memory and addresses,
3. define environments and function tables,
4. implement expression and lvalue evaluation,
5. implement instruction, statement, block, and function evaluation,
6. produce proof trees alongside evaluation results,
7. add runtime-error tests.

Start with a minimal executable subset:

```c
int main(void) {
  int x;
  x = 3;
  return 0;
}
```

Then extend in this order: conditionals, loops, arrays/pointers, calls.
