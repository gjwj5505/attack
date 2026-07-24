# Language Design

This project no longer treats a hand-written C-like parser as the language
source of truth. The current language target is a Sparrow-facing, CIL-shaped
subset called CIL--.

## Goal

The purpose of CIL-- is to synthesize and execute small deterministic programs
whose concrete final memory can be compared against Sparrow's abstract result.

The intended pipeline is:

```text
C source
  -> GoblintCil parser
  -> GoblintCil.Cil.file
  -> CIL--
  -> SyntaxChecker.check_file
  -> Big-Step / synthesis / objective
```

For generated attacks:

```text
Synthesized CIL--
  -> optional SyntaxChecker.check_file
  -> Big-Step concrete execution
  -> CIL
  -> pretty-printed C
  -> Sparrow input
```

## CIL and CIL--

- CIL means the external OCaml CIL representation from `goblint-cil`.
- CIL-- means the internal supported subset in
  `lib/language/syntax/syntax.ml`.

CIL is used for parsing, pretty-printing, library utilities, and sanity checks.
CIL-- is the source of truth for synthesis, Big-Step semantics, proof trees, and
attack objectives.

CIL-- follows CIL constructor shapes where useful:

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

CIL-- records are immutable for now. If later passes need labels, statement ids,
CFG metadata, analysis annotations, or proof annotations attached after
construction, make the relevant fields mutable in the CIL style at that point.

## Variable Identity

CIL-- identifies variables by `(scope, name)` rather than by arbitrary integer
IDs. A scope is either `Global` or `Function function_name`.

Global object names are unique within a file. A function identifier may occur
in compatible forward declarations and once in a function definition, as
specified below. Formal and local names are unique within their function.
Recursive activations reuse the same static variable ID because runtime memory
contains only the active top stack state.

`varinfo` does not store a separate `vname`. `VarId.name` is the sole source of
truth for a variable's name, preventing inconsistent name/ID pairs. Renderers
display only the name; scope remains available internally for checking and
synthesis.

GoblintCil integer `vid` values are bridge-only administrative IDs. CIL-- -> CIL
conversion allocates integer IDs and maintains a scoped-ID-to-CIL-varinfo table.
CIL -> CIL-- conversion reconstructs scoped IDs from the global or enclosing
function context.

The current bottom-up synthesis reconnect uses the finite canonical function
name set `main`, `f`, and `g`, plus finite canonical formal/local name sets. The
first auxiliary function is `f`; `g` is introduced only after `f`. This avoids
both integer-ID bookkeeping and unbounded alpha-renaming variants while still
distinguishing self calls from calls to another function. Scope-aware IDs
prevent components belonging to one function from being combined accidentally
with another function.

The current `Global | Function name` scope model relies on the existing policy
that rejects duplicate formal/local names within a function. If nested shadowing
is supported later, function scope must be refined with a declaration or block
path.

## Current Active Subset

Types:

- `void`
- `int`
- `unsigned int`
- pointers
- arrays with constant integer length or unknown length
- non-vararg function types

Globals:

- function declarations represented by `GVarDecl` whose type is `TFun`
- function definitions
- global variable declarations
- global variable definitions with initializers

### Function Forward Declarations

CIL-- permits a function declaration and definition to share one global
function identifier. This is required for recursive and mutually recursive
files whose definitions must be presented to C tooling in declaration order.

- Every declaration and definition of one function uses the same global
  `VarId`.
- Their complete non-vararg `TFun` signatures must be structurally equal,
  including return type and formal parameter types.
- A file contains at most one `GFun` definition for a function identifier.
- Compatible repeated declarations may be accepted by the checker. The
  synthesizer emits at most one forward declaration per function.
- A non-function global object and a function may not share an identifier.
- Function declarations needed by later definitions appear before those
  definitions in the emitted global list.
- The CIL bridge must reuse the same CIL function `varinfo` for compatible
  declarations, definitions, and direct call sites.

Forward declarations add static `Total` syntax but do not independently enter
an execution `Footprint`. A footprint records the unique completed `fundec`
actually used by a proof.

Implementation status: `SyntaxChecker` still rejects every duplicate global name,
including a compatible function declaration/definition pair. The synthesis
reconnect must implement the policy above before emitting mutual recursion.

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

These features are outside CIL-- until explicitly designed:

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
active definitions in `lib/language/syntax/syntax.ml`. That is intentional: the
file records the relationship to GoblintCil while keeping the active AST small.

## Cast-Free Policy

CIL-- is a cast-free lowered CIL subset. There is no active `CastE` constructor.

This avoids having to distinguish source-level explicit casts from C front-end
implicit conversions. If GoblintCil lowers a C source program into CIL containing
`CastE`, the CIL -> CIL-- bridge rejects it.

Consequences:

- CIL-- contains no implicit casts.
- CIL-- contains no explicit casts.
- Binary operations must already have matching operand/result types.
- Assignments and calls must be type-consistent without relying on conversion.
- Mixed signedness examples such as `int + unsigned int` are rejected because
  GoblintCil inserts casts.

If casts are needed later, add them one narrow case at a time with a precise
Big-Step rule and Sparrow CIL 1.7.3 compatibility check.

## Bridge Policy

`lib/language/cilBridge.ml` implements conversion between GoblintCil CIL and
CIL--.

- Input acceptance is based on the GoblintCil-lowered CIL form, not the surface
  C source shape. For example, a source expression such as `return f(-1);` may
  be accepted if GoblintCil lowers it into CIL instructions and expressions that
  belong to CIL--. The project does not currently enforce a stricter
  source-syntax-only CIL-- policy.
- CIL-- -> CIL should be total for checked CIL-- programs.
- CIL -> CIL-- accepts only the supported subset.
- Unsupported CIL features return explicit errors.
- Builtin declarations inserted by GoblintCil, such as `__builtin_*`,
  `__sync_*`, `__atomic_*`, and `__builtin_va_list`, are filtered from external
  input before conversion.

The bridge also provides roundtrip checking:

```text
CIL-- -> CIL -> CIL--
```

Roundtrip equality is structural CIL-- equality. Statement ids are ignored.

## Checker Policy

`lib/language/syntax/syntaxChecker.ml` is a thin structural checker, not a full C
typechecker.

It currently checks:

- exactly one `main`
- `main` has return type `int`
- `main` has no parameters
- duplicate global names; this is the current rule to be replaced by the
  compatible function declaration/definition policy above
- `break` outside loops
- `continue` outside loops
- return statement expression presence matches the enclosing function return
  type
- CIL-- roundtrip stability
- GoblintCil `Check.checkFile` on the converted CIL

Big-Step program entry intentionally supports only `int main(void)`. `argc` /
`argv` forms are not supported until an initial-memory layout for argument
strings and pointer arrays is designed.

GoblintCil's checker is used for CIL internal consistency, type consistency,
varinfo sharing, initializer consistency, call consistency, and related CIL
invariants.

The current checked and executable value type is `int`. `void` is used only for
functions that return no value, and `Typ.TFun` carries function signatures.
`unsigned int`, pointers, arrays, and compound types may still be syntactically
present in the bridge-facing AST, but their type correctness is intentionally
outside the current `SyntaxChecker.check_file` guarantee. When any of those types
enters the active CIL-- subset, add explicit type checks and direct AST-checker
tests before treating programs that use it as validated CIL--.

The CIL-- checker exists because some invariants are enforced by the C parser,
not by GoblintCil's CIL checker. For example, C source cannot contain a
top-level loop-free `break`, but a synthesizer can directly construct such a
CIL-- AST.

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

## Big-Step Semantics

The active Big-Step implementation constructs proof trees for CIL-- programs.

Layering:

- expression proof trees evaluate pure expressions to values
- lvalue proof trees evaluate lvalues to locations
- instruction proof trees perform side effects
- statement proof trees produce memory and control
- block proof trees sequence executed statements
- function proof trees enter/leave call frames and validate return control
- file proof trees execute `main()`

CIL-- expressions are pure. Expression conclusions therefore have no output
memory:

```ocaml
type e_concl = memory * Exp.t * value
```

All side effects are represented by instructions:

```ocaml
type i_concl = memory * instr * memory
```

`Call (None, ...)` means that the call instruction does not assign the return
value to a caller lvalue. It is not restricted to calls of `void` functions; a
non-void return value may be discarded.

`AddrOf` and `StartOf` are separate proof constructors. The current runtime
value representation maps both to a location pointer, but C semantics
distinguishes them by pointer type: `&a` points to the whole array object, while
`StartOf a` / array decay points to the first element. Exact pointer arithmetic
will likely require pointer values to carry pointee-type metadata.

Block proof trees use a flat sequence:

```ocaml
BTreeSeq of stree list * b_concl
```

The list contains only statements that actually executed. If a statement
returns, breaks, or continues, later source statements in the block are not
included. The final memory and control are stored in the block conclusion.

Fuel is an implementation cutoff, not part of the mathematical semantics.
`Instr` statements do not consume statement fuel; each instruction consumes fuel
in instruction derivation. Other statements consume fuel at statement
derivation.

## Synthesis Components

Synthesis component pools should store syntax/proof units that are built
bottom-up and reused by larger rules.

For syntax, a type should be a component when it is recursive itself or when it
contains a child that is a recursive synthesis component and therefore acts as a
bottom-up intermediate node. Administrative wrappers such as `option`, lists,
and thin records around optional data do not need separate component buckets
unless they become independent synthesis choices.

Current syntax component layers are:

- `exp`
- `lval`
- `offset`
- `instr`
- `stmt`
- `block`
- `fundec`
- `init`
- `global`
- `file`

`initinfo` is not a component by default because it is an optional-initializer
wrapper around `init`. `varinfo`, operators, constants, labels, and statement
kinds are generated by the rules that need them unless a later synthesis design
makes them independent search targets.

For Big-Step proofs, component layers follow the independent proof-tree layers:

- `etree`
- `ltree`
- `itree`
- `stree`
- `btree`
- `ftree`
- `ptree`

`callee_tree` is not a component bucket for now. Direct-call rules construct it
inside the call-instruction proof rule.

The selected synthesis design does not use a two-dimensional size for proof
components. Raw code and proofs live in independently scheduled pools:

- `CodePool` stores raw syntax components by ordinary static AST size;
- `ProofPool` stores schematic Big-Step proof components by
  one-dimensional `proof_size` only.

For a proof target of size `n`, the parent proof rule costs one and the sizes
of its actual proof-tree premises are positive integers summing to `n - 1`.
Static syntax appearing in a conclusion, including holes, receives no part of
that proof-size partition. Loops and calls therefore depend only on already
synthesized strict proof subtrees. The size of the materialized concrete
program is measured only after completion and may be used for reporting,
result ordering, or a separate output bound; it is not a proof construction
order.

The syntax wrapper `Syntax.ast` mirrors the syntax component layers for
documentation and future shared dispatch. The component pool still keeps
separate buckets for each layer because grow rules need typed inputs such as
`exp`, `lval`, `stmt`, and `ptree`.

## Big-Step Checker

`lib/language/semantics/proof/ground/bigStepChecker.ml` validates that a Big-Step proof
tree is consistent with its conclusion and with the CIL-- program structure.

There are two useful checking levels:

- subtree checks validate expression, lvalue, instruction, statement, block, and
  function proof fragments;
- `check_ptree` validates whole-program proof trees, including the file/main
  structure.

Whole-program checking verifies:

- optionally, `SyntaxChecker.check_file file`;
- exactly one `main` exists in the file;
- the proof's function is that `main`;
- `main` is called with no arguments;
- the function proof checks;
- the program conclusion memory and return value match the function proof.

`check_ptree` defaults to `use_check_file:true`. The option controls only
whether `SyntaxChecker.check_file` is run; proof-level program checks still run
either way. The CLI `-big` path already runs `SyntaxChecker.check_file` before derivation, so
it calls `check_ptree ~use_check_file:false` after constructing the proof tree.

Function return types are context-sensitive. Standalone statement/block checks
can omit a return type, but function checking passes the enclosing function
return type down to return statement checks. This keeps subtree checking useful
while still making complete function/file proof checking strict.

Direct callee proof trees must match both function identity and function
signature. For direct calls, the callee expression's function type must agree
with the callee `fundec` return type and formal parameter types.

`lib/language/semantics/typeUtil.ml` owns the scalar type side conditions used
by the proof checker. Current policy:

- no casts;
- no implicit conversions;
- exact type equality for assignments, call arguments, call return targets, and
  returns;
- unary `-` requires an integer operand and returns the same integer type;
- unary `!` requires an integer operand and returns `int`;
- arithmetic binary operators require matching integer operands and return that
  same integer type;
- comparison and logical binary operators require matching integer operands and
  return `int`;
- `BNot`, bitwise operators, shifts, pointer arithmetic, pointer/array/struct
  lvalues, `AddrOf`, and `StartOf` are unsupported until explicitly designed.

Two checker invariants are easy to break and should be preserved:

- `ETreeConst` must check the expression shape and the concrete value. A proof
  such as `1 ⇓ 2` is invalid.
- Function output memory is `Memory.leave_function body_out`, not `body_out`
  itself.

Regression tests live in `lib/test/bigstepcheck_test.ml`. They run the current
success examples and construct invalid proof trees to check representative
error messages across the expression, lvalue, instruction, call/type,
statement, block, function, and program layers.

## Sparrow Compatibility

Sparrow reportedly uses CIL 1.7.3. GoblintCil 2.0.9 is only a utility layer for
this project.

For soundness/completeness attacks, CIL-- Big-Step behavior must match the
concrete behavior of the exported C program as parsed and lowered by Sparrow's
CIL 1.7.3 frontend.

Before relying on a feature for attacks, check that:

```text
CIL-- Big-Step concrete execution
  = concrete behavior of exported C under Sparrow CIL 1.7.3 lowering
```

Only then can the result be compared against Sparrow's abstract analysis.

## Examples Policy

Example files use `.c` because CIL is an OCaml AST, not a source-file syntax.
Examples should be C source programs whose GoblintCil-lowered CIL belongs to
the supported CIL-- subset.

Success examples should avoid features outside CIL--. Unsupported examples
should be named clearly, such as `unsupported_cast_implicit.c`, and should have
an expected rejection reason.

Current examples include:

- `examples/simple.c`
- `examples/function_call.c`
- `examples/fibonacci.c`

Control-flow cases that cannot be represented as valid C source, such as
loop-free `break`, should be tested by constructing CIL-- ASTs directly in OCaml
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
Function `svar.vtype` stores the complete non-vararg `Typ.TFun`, including the
return type and formal parameter types. It is the canonical type of the
function variable at definitions and call sites.

`fundec.sformals` carries the corresponding formal varinfos. The AST checker
requires the parameter names and types in `svar.vtype` to match `sformals`.
`SyntaxUtil.function_return_type` extracts the return type from `svar.vtype`.
