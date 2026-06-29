# Language Design

이 프로젝트의 언어는 ISO C 전체가 아니다. 현재는 readable C-like syntax를 쓰지만,
장기 목표는 Sparrow가 CIL을 거쳐 분석하는 CFG command와 잘 대응되는 structural
core language다.

## Principles

- C surface syntax is a facade; CIL/Sparrow-facing semantics is the target.
- Parser, printer, synthesis, and Big-Step should share one semantic core.
- Do not add a feature just because C has it.
- Add a feature only after CIL lowering, Sparrow `IntraCfg.Cmd`, and Big-Step
  meaning are understood.
- Compare analyzer behavior at the CIL/CFG command level, not raw `.i` text.

Relevant pipeline:

```text
C source or .i -> CIL AST -> Sparrow CFG / IntraCfg.Cmd -> abstract interpretation
```

## Current Surface Syntax

Accepted grammar, summarized:

```text
program  ::= int main() block
block    ::= { stmt* }
stmt     ::= int x = expr;
           | x = expr;
           | if (expr) block else block
           | while (expr) block
           | return expr;
expr     ::= decimal integer | identifier | -expr | (expr)
           | expr (+|-|*|/|%) expr
           | expr (==|!=|<|<=|>|>=) expr
```

Notes:

- `main` is parsed as an identifier and checked by the parser action.
- Only one parameterless `int main()` function is accepted.
- Declarations must be initialized.
- `else` is mandatory.
- `if`/`while` bodies must be blocks.
- Empty blocks are accepted and represented as `[]`.
- Comments are lexical trivia.
- No preprocessor, typedef, storage class, qualifier, function parameter, or
  standalone block statement is supported.

## Current AST

The current AST lives in `lib/language/syntax.ml`.

- `Typ.t`: currently only `Int`.
- `id`: string.
- `binding`: `{ typ; name }`.
- `lval`: currently only `LVar`.
- `Exp.t`: `Int of Int64.t`, `Lval`, unary minus, and binary operators.
- `Stmt.t`: declaration, assignment, if/else, while, return.
- `Stmt.codeblock`: `Stmt.t list`.
- `program`: one `main` function record.

Integer literals are stored as `Int64.t` only to parse and reject runtime
`int` overflow cleanly. Runtime integers are signed 32-bit `int`, not
`long long`.

There are no source locations or labels in the AST. Add them later through a
separate pass if CFG output or analyzer integration needs them.

## Current Semantics

Judgments:

- Expression: `<memory, expr> ⇓ <memory', value>`
- Statement: `<memory, stmt> ⇓ <memory', control>`
- Block: `<memory, block> ⇓ <memory', control>`
- Program starts from `main` and returns a value.

Current expressions are pure, but memory is threaded so future calls or
side-effect expressions can fit the same judgment shape.

Runtime model:

- `Value.t` currently contains signed 32-bit `int`.
- Memory separates name binding from storage: local name -> location -> value.
- Proof output shows visible locals as `{x |-> 1}`.
- Current local scope is flat. Block scope/shadowing is outside the subset.
- Future function calls should push/pop frames.

Control:

```ocaml
Normal | Return of Value.t | Break | Continue
```

`Break` and `Continue` are reserved in Big-Step types but parser syntax is not
implemented yet.

Evaluation policy:

- deterministic left-to-right evaluation
- C/Sparrow truthiness: `0` false, nonzero true
- block execution stops after `Return`, `Break`, or `Continue`
- derivator uses statement-level fuel for nontermination

No-tree cases:

- signed integer overflow
- division/modulo by zero
- `INT_MIN / -1`, `INT_MIN % -1`
- runtime `int` literal overflow
- unbound variable or duplicate declaration
- missing `main` return
- out of fuel

These return a `Derivator` error instead of producing a proof tree.

## Proof Trees

- `etree`: expression proof.
- `stree`: statement proof.
- `btree`: block proof.
- `ptree`: program proof.

`BEmpty` represents an empty block and is visualized as `empty`.

Short-circuit tree constructors exist for future `&&`/`||`. They avoid making a
fake subtree for an unevaluated right operand; a future checker must verify the
left-operand side condition.

## CIL / Sparrow Mapping

Intended current mapping:

```text
int x = e;       -> Cset(x, e)
x = e;           -> Cset(x, e)
if (e) S else T  -> Cassume(e) / Cassume(!e) branch edges
while (e) S      -> CFG cycle with assume edges
return e;        -> Creturn(e)
```

Observed Sparrow/CIL facts:

- CIL instructions are flattened into commands such as `Cset`/`Ccall`.
- CIL `If` and `Loop` become CFG structure plus assumptions.
- CIL `Return` becomes `Creturn`.
- Sparrow sparse analysis runs abstract transfer over `IntraCfg.Cmd`.

The bridge for soundness discussion is:

```text
our Big-Step concrete execution
  -> corresponding CIL/IntraCfg path
  -> Sparrow abstract result
```

## CIL and CIL'

The project uses two related representations:

- CIL: the external OCaml CIL library representation, used for parsing,
  pretty-printing, type utilities, and other library support.
- CIL': the internal supported subset, used as the source of truth for
  synthesis, Big-Step semantics, proof trees, and attack objectives.

CIL' should follow CIL's type shape and constructor names where useful, but it
only contains constructors whose semantics are intentionally supported by this
project.

CIL' records are immutable for now because synthesis and Big-Step treat ASTs as
values. If later passes need to attach labels, statement ids, CFG metadata,
analysis results, or proof annotations after construction, make the relevant
fields mutable in the CIL style at that point.

Conversions:

- CIL' -> CIL must be total for well-formed CIL' programs.
- CIL -> CIL' accepts only the supported subset and otherwise returns an
  explicit unsupported-feature error.

When a CIL library function is useful, convert CIL' to CIL and call the library
function there. When a project-specific semantic, synthesis, or proof operation
is needed, implement it on CIL'.

Sparrow inputs are produced by converting synthesized CIL' to CIL, pretty
printing it as C, and giving that file to Sparrow. Sparrow may parse the printed
C using its own CIL version; the comparison target remains the CIL' Big-Step
final memory.

CIL' semantics is not justified by the newest CIL library alone. For
soundness/completeness attacks, CIL' must denote the same concrete behavior as
the subset accepted and lowered by Sparrow's CIL 1.7.3 frontend. The newest CIL
library is only a utility layer unless this compatibility condition is checked.

The supported CIL' subset should stay inside the conservative common subset of
newest CIL and Sparrow CIL 1.7.3. Features whose lowering or concrete meaning
may differ between the two CIL versions remain unsupported until tested against
Sparrow's frontend.

Before relying on a feature for attacks, check for execution-meaning differences
between CIL' Big-Step and the C code as parsed/lowered by Sparrow CIL 1.7.3.
The bridge that justifies an attack is:

```text
CIL' Big-Step concrete execution
  = concrete behavior of exported C under Sparrow CIL 1.7.3 lowering
  -> Sparrow abstract result
```

## Examples Policy

Example files use the `.c` extension because CIL is an OCaml AST, not a source
file syntax. However, examples should be written as CIL-compatible C: C code
whose parsed/lowered CIL belongs to the supported CIL' subset.

Do not use source-level C constructs whose C semantics may differ from CIL
lowering, such as unsequenced side effects (`a++ + a++`), side-effect
expressions, calls, pointer/array/struct operations, or other unsupported
features. If such a feature is intentionally studied, put it in a clearly named
error or compatibility example and record the expected unsupported behavior.

## Attack Observables

For CIL-core synthesis, source locals and CIL temporary variables are not
distinguished. Both are local memory bindings.

A concrete run is considered normally completed only when `main` returns `0`.
The return value itself is not an attack observable.

Soundness/completeness comparison uses all live local memory bindings at the end
of normal `main` execution:

- soundness failure: concrete value is not included in the analyzer result
- completeness/precision failure: analyzer result is wider than the singleton
  abstraction of the concrete value

## Restrictions

Excluded until designed against CIL/Sparrow:

- uninitialized declarations
- block scope and shadowing
- calls
- arrays, pointers, structs
- casts and non-int scalar types
- `&&`, `||`, `!`
- side-effect expressions
- `break`/`continue` parser syntax

## Development Policy

For each new feature:

1. inspect CIL lowering,
2. inspect Sparrow `IntraCfg.Cmd`,
3. define Big-Step rules and no-tree cases,
4. add parser/printer only if surface syntax is useful,
5. add success/error examples.

The feature matrix stays in `.agents/c-feature.csv`; do not update it unless
we intentionally revisit feature support.
