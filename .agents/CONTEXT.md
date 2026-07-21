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
-pp:  C source -> GoblintCil -> CIL-- -> SyntaxChecker.check_file -> CIL -> pretty C
-ast: C source -> GoblintCil -> CIL-- -> SyntaxChecker.check_file -> SVG AST
-big: C source -> GoblintCil -> CIL-- -> SyntaxChecker.check_file
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

- `lib/language/syntax/syntax.ml`: CIL-- AST.
- `lib/language/typ.ml`: CIL-- type subset.
- `lib/language/cilBridge.ml`: GoblintCil CIL <-> CIL-- conversion.
- `lib/language/syntax/syntaxChecker.ml`: thin CIL-- syntax checker.
- `lib/language/semantics/runtime/`: locations, values, value operations, and
  memory.
- `lib/language/semantics/proof/bigStep.ml`: proof tree types.
- `lib/language/semantics/proof/derivator.ml`: concrete Big-Step derivation.
- `lib/language/semantics/proof/bigStepChecker.ml`: proof tree checker.
- `lib/language/semantics/typeUtil.ml`: scalar type side conditions for the
  proof checker.
- `lib/test/syntaxcheck_test.ml`: direct CIL-- syntax checker tests.
- `lib/test/bigstepcheck_test.ml`: Big-Step checker regression tests.
- `lib/language/semantics/proof/size.ml`: the current, pre-migration
  `(program size, proof size)` implementation; the selected synthesis design
  replaces this with separate raw-syntax and proof-size accounting.

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
- `SyntaxChecker.check_file` is intentionally structural. Runtime definedness belongs
  in Big-Step derivation and proof checking.
- `-big` runs `SyntaxChecker.check_file` before derivation, then validates the proof
  with `BigStepChecker.check_ptree ~use_check_file:false`. That option only
  controls whether `SyntaxChecker.check_file` is called again; proof-level program
  checks still run.

## Recent Checker Status

2026-07-10 checkpoint:

- `SyntaxChecker.check_file` has 57 passing direct regression cases.
- `BigStepChecker` has 105 passing direct/end-to-end regression cases.
- `dune build`, `lib/test/syntaxcheck_test.exe`, and
  `lib/test/bigstepcheck_test.exe` pass.
- Detailed checker policies and test mappings are recorded in
  `.agents/syntaxcheck.md` and `.agents/bigstepcheck.md`.

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
  function checks and `SyntaxChecker.check_file`.

Regression coverage lives in `lib/test/bigstepcheck_test.ml`. It includes
representative invalid proofs for expression, lvalue, instruction, call/type,
statement, block, function, and program-level errors, including both
`ITreeCallAssign` and `ITreeCallVoid` callee-signature mismatches. Top-frame
coverage includes nested caller restoration, callee-local disposal, global
update propagation, and forged-memory rejection.

## Proof-Skeleton and Hole-Completion Search Design

This is the selected direction for reconnecting synthesis. It supersedes the
provisional plan to order proof components by `(program footprint, proof size)`.
The hole-syntax foundation has been implemented, while hole-aware proof types,
substitution, unification, and synthesis integration remain pending.

### Why Program Size Leaves the Proof Order

The original program-size dimension was introduced because a Big-Step proof
does not contain proof premises for syntax that the concrete execution skips.
An unselected `if` branch, a short-circuited expression, or an unexecuted block
suffix can therefore grow without increasing the proof tree. A separate static
bound was needed to keep each search layer finite.

That dimension works as a proof dependency order for loops: the recursive
`rest` subtree proves the same loop syntax as its parent and has smaller proof
size. It does not work for function recursion. A callee proof is a strict proof
subtree but may carry a larger completed function definition than the caller
component currently being assembled. Deduplicating repeated function syntax
through a unique footprint can also make the apparent program size decrease
when a recursive `FTree` is finally wrapped. A one-pass order over unique
program size and proof size therefore reverses valid dependencies.

The selected design separates executed proof growth from skipped static-code
growth:

```text
ProofPool
  key: proof_size
  payload: hole-aware Big-Step proof component

CodePool
  key: ordinary static syntax size
  payload: raw expression/block code fragments
```

The two pools advance fairly and are joined through typed syntax holes. Proof
components are ordered only by proof size; raw code components retain ordinary
AST size. This is not permission to finish every code size for one proof size
before advancing. The orchestration must dovetail both pools so that neither is
permanently starved.

For the initial implementation, the following search-universe bounds remain
fixed configuration rather than additional scheduling dimensions:

- the canonical function-name set;
- the formal/local variable set provided to every function;
- the available integer literals;
- the concrete memory values admitted into synthesized components.

These bounds may later be expanded fairly. Literal availability and admitted
memory values remain separate because arithmetic may produce values that do not
occur as literals.

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

## CIL-- Synthesis Reconnect Design

The temporary search objective is structural equality with
`examples/simple.c`, replacing the analyzer result only while the synthesis API
is reconnected. The generator itself is not restricted to the syntax appearing
in `simple.c`: it supports active int-only direct function calls, conditionals,
loops, `break`, `continue`, returns, and nested blocks from the start. Pointers,
arrays, and unsupported runtime features remain outside this reconnect.

The temporary function-name universe is finite:

- `main` is the required entry function;
- `f` and `g` are optional auxiliary functions;
- `main` may call `f` or `g`;
- `f` and `g` may call themselves or each other;
- the first auxiliary function is always `f`, and `g` is generated only after
  `f`, eliminating pure alpha-renaming permutations.

Integer literal candidates and other synthesized identifier domains are also
finite. Arithmetic evaluation may produce values outside the literal pool.

### Proof-Directed Termination

Big-Step proofs are synthesized directly and bottom-up. Arbitrary programs are
not sent to `Derivator` to discover whether they terminate. A direct function
call is available only when a finite callee `ftree` has already been
synthesized. Because the callee tree is a strict proof subtree, recursive and
mutually recursive construction is well-founded in `proof_size`.

This permits finite recursion without requiring an acyclic static call graph:

1. synthesize a base-case proof of `f` whose executed branch does not recurse;
2. synthesize a proof of `g` that calls that finite `f` proof;
3. synthesize a larger proof of `f` that calls the finite `g` proof;
4. continue only by increasing proof size.

If no finite base execution exists, no finite proof component is generated.
`Derivator` and `BigStepChecker` are final cross-validation tools for a completed
matching candidate, not proof generators.

This strict proof-subtree relation establishes logical well-foundedness, but it
does not by itself establish a one-pass order over `(local program size,
proof_size)`. A smaller-proof callee may have arbitrarily larger unexecuted
syntax than its caller.

### Search-Theoretic Baseline

For deterministic finite executions, the following searches enumerate the same
terminating programs:

```text
enumerate complete programs and dovetail bounded execution steps
                <=>
enumerate finite Big-Step proof trees
```

A program terminates exactly when it has a finite Big-Step derivation. Big-Step
synthesis therefore does not add computability or completeness beyond a fair
program-by-execution-bound diagonal search.

Its intended advantage is search speed and structure:

- proof components expose input/output memory, control, return values, and call
  boundaries before a whole larger candidate is formed;
- incompatible state and control boundaries can be rejected locally;
- finite callee and expression/statement proofs can be memoized and reused;
- dominance/equivalence pruning may preserve completeness;
- scores, beam limits, and fanout limits may prioritize promising attacks, but
  generally sacrifice completeness unless separately justified.

A plain bounded-execution dovetail remains a valid simpler baseline. With the
current recursive Big-Step `Derivator`, it would either rerun with increasing
fuel or require a new resumable small-step machine with explicit continuations.
The current design preference remains compositional Big-Step synthesis because
of its pruning and heuristic opportunities, not because dovetailing is
incorrect.

### Hole-Syntax Type Boundary

Hole syntax and proof types live beside the concrete `Syntax` and
`BigStep` types. Hole-independent leaf types such as `Typ.t`, `VarId`,
`varinfo`, constants, operators, fields, and labels are reused directly.
Recursive syntax types are mirrored in `HoleSyntax` exactly when they can
transitively contain a hole. `HoleBigStep` will mirror the concrete proof rules
with hole syntax in their conclusions. The only new syntax holes are
expression holes and statement-sequence holes.

### Hole Syntax and Proof Completion

A hole-aware proof conclusion may contain holes only where that proof has no
executed premise for the corresponding syntax. The active hole positions are:

```text
ExpHole      an unevaluated right operand of short-circuit LAnd/LOr
StmtSeqHole  either the whole statement list of an unselected If branch or an
             enclosing-block suffix skipped after non-normal control
```

A hole-aware block uses the native OCaml list type with an administrative item
type:

```ocaml
type stmt_seq_item =
  | Stmt of stmt
  | StmtSeqHole of hole_id

type block = {
  bstmts : stmt_seq_item list;
}
```

For each individual hole-aware block, its outer `bstmts` list contains at most
one direct `StmtSeqHole`, and that item must be last. This restriction does not
limit holes inside nested statements or blocks, nor occurrences in other proof
conclusions. Within one individual AST/conclusion every hole ID is unique. The
same hole ID may occur across multiple conclusions of one proof component to
express that they contain the same unknown static syntax position. Thus
`[StmtSeqHole h]`
denotes a wholly unknown statement list, while
`[Stmt s1; ...; StmtSeqHole h]` denotes a known prefix followed by an unknown
suffix. A hole-free list contains only `Stmt` items; `[]` is the complete empty
block.

A suffix immediately following a source `Return`, `Break`, or `Continue`
statement is not generated. This is an analyzer-respecting prune for obvious
unreachable code. It does not apply merely because an `If`, nested `Block`, or
`Loop` happened to produce non-normal control in one concrete execution; such
a suffix may be reachable on another path and remains the final
`StmtSeqHole` of that block.

During proof synthesis, reaching syntax that was previously a hole refines the
hole-aware program and adds the required proof premises. This refinement may
include executed calls. Recursive callees and recursive loop-rest proofs must
still be strict proof subtrees and therefore have smaller proof size.

After a complete hole-aware `ptree` has been synthesized, every remaining hole
denotes syntax that was never visited anywhere in that whole concrete proof.
Completion then fills those holes without adding proof premises:

- `ExpHole` is filled from type-compatible raw expression components;
- `StmtSeqHole` is filled by splicing the `bstmts` of a raw block component;
- the empty statement sequence is a valid completion;
- final completion fragments are call-free;
- final completion may use only variables already declared by the enclosing
  function.

The call-free restriction applies only to holes still open after the `ptree` is
complete. A hole that becomes executed while a recursive or loop proof is being
built may be refined with a call and its proof.

Completion extends the component substitution; it never mutates a component
already stored in a set or eagerly rewrites all of its conclusions. Once all
holes are gone, the whole proof is materialized with concrete CIL-- syntax in
every conclusion and is validated by `SyntaxChecker`, `Derivator`,
`BigStepChecker`, the CIL roundtrip, and finally Sparrow.

### Hole Identity Across Proof Conclusions

Inside one `HoleSyntax` AST, hole IDs identify distinct static positions and
therefore cannot repeat. Across different conclusions of one `HoleBigStep`
component, the same ID identifies the same unknown static position. This is the
reason IDs are present even though an isolated hole AST would not otherwise
need them. Hole IDs are component-local administrative names, not globally
meaningful identities.

Hole typing and completion context are derived from each occurrence's enclosing
syntax and function context rather than stored in a persistent descriptor
table. Occurrences of one hole ID across conclusions must induce compatible
requirements.

Independent components are freshened before composition. Positions determined
to be the same by repeated loop/function syntax are unified. A completed parent
is canonically renumbered in traversal order before pool insertion so that
alpha-renamed hole IDs do not create duplicate components.

### Proof Components and Substitution

Hole refinement follows the same broad organization as Algorithm W: a proof
component carries an immutable raw proof tree together with the substitution
under which that tree is interpreted.

```ocaml
type 'tree component = {
  tree : 'tree;
  substitution : HoleSubstitution.t;
}
```

Unification must not eagerly apply every refinement to every conclusion. OCaml
can physically share immutable AST values repeated in a proof tree, whereas
rebuilding every conclusion after each refinement duplicates all paths from a
changed hole to their roots. Keeping the raw tree and substitution separate
preserves that sharing while intermediate holes remain.

`HoleSubstitution` separates bindings by hole sort:

```ocaml
type t = {
  exps : HoleSyntax.exp IntMap.t;
  stmt_seqs : HoleSyntax.stmt_seq_item list IntMap.t;
}
```

An absent key is unbound. A hole-to-hole expression alias is represented by an
`ExpHole` right-hand side, and a statement-sequence alias by a singleton
`[StmtSeqHole h]` right-hand side; no separate link constructor is needed.
Applying a statement-sequence binding splices its list into the containing
block. Because statements can contain expressions, applying or composing an
expression binding must also traverse statement-sequence right-hand sides.

Composition has the explicit orientation

```text
apply (compose ~after:S2 ~before:S1) term
= apply S2 (apply S1 term)
```

Thus, when a component already carries `S0`, unification proceeds as

```text
delta = unify (apply S0 lhs) (apply S0 rhs)
Snew  = compose ~after:delta ~before:S0
```

The implementation may expose this safely as `unify_under S0 lhs rhs` so
callers do not reverse the composition accidentally.

Stored substitutions are normalized and idempotent:

```text
dom(S) ∩ FV(range(S)) = ∅
apply S (apply S term) = apply S term
```

Consequently, looking up a bound ID never requires following a chain of other
bound IDs; its right-hand side contains only genuinely unbound holes. The
incremental preservation argument is simple. Assume `S` is idempotent, choose
an unbound `H`, normalize `t0 = apply S t`, check `H ∉ FV(t0)`, and let
`B = {H ↦ t0}`. Then `compose ~after:B ~before:S` is idempotent after `B`
is pushed through all old right-hand sides. The empty substitution is the base
case. Arbitrary idempotent substitutions cannot simply be composed without
these compatibility and occurs checks.

Comparisons, checking, pretty-printing, and unification should use
substitution-aware views that dereference at holes without first allocating an
entire rewritten AST. The flat invariant makes each bound-ID lookup one map
step, although traversal of its resolved term is still required. A hard apply
(zonk/materialization) is reserved for final concrete `Syntax`/`BigStep`
construction and may memoize shared source nodes.

Before a component enters a pool, a freeze step normalizes its substitution,
removes unreachable bindings, canonically renumbers reachable hole IDs across
the whole proof component, and computes its resolved semantic key or
fingerprint. This gives component sets stable identity without sacrificing raw
tree sharing.

Repeated executions of one static loop or function must agree on all static
syntax, not only on holes. Two independently synthesized executions are joined
by hole-aware structural unification of their statements, blocks, or function
bodies:

```text
same concrete constructors  recursively unify their children
hole H and concrete term T   extend the substitution with H ↦ T
hole H1 and hole H2          bind one representative to the other
different concrete terms     reject only that grow combination
```

Unification requires an occurs check. Function identifiers, signatures,
formals, locals, and other function metadata are exact; the hole-aware body is
the part refined by unification. After final completion, ordinary
`SyntaxEqual.equal_fundec` and the existing concrete proof checker apply again.

### Completion Context and Canonical Syntax

Every function receives its configured formal/local variable set before its
proof is synthesized. Completion cannot add locals because function entry has
already allocated all formals and locals in the proof memory. Formal and local
names use separate canonical families when parameters are enabled.

Raw block fragments carry intrinsic control-context summaries rather than being
duplicated into "allowed" pools:

```text
free_break : bool
free_continue : bool
return_effect : NoReturn | ReturnsVoid | ReturnsInt
```

`If` and nested `Block` union these effects. Wrapping a body in `Loop` binds its
free `break` and `continue`; returns remain effects of the enclosing function.
A fragment is inserted only when its free loop control and return effect are
compatible with the hole context.

Generated syntax uses these initial canonicalization policies:

- `goto`, `case`, `default`, and labels are not synthesized;
- every synthesized statement has `labels = []`;
- empty `Instr` statements are not synthesized;
- consecutive `Instr` statements are represented as one maximal instruction
  list;
- redundant nested `Block` normalization is deferred.

### Initial File Boundary

The initial final-file policy includes `main`, every function whose `ftree`
occurs in the completed program proof, and required forward declarations. It
does not add unrelated unused function definitions or new top-level globals.
Because final hole completion is call-free, it introduces no additional
function-definition dependency.

This is an initial analyzer-respecting boundary, not a permanent
witness-preservation theorem. Whether Sparrow completely ignores call-graph
unreachable functions, and whether unused function/global completion is worth
searching, remains open.

### Considered Alternatives

The discussion considered and set aside these alternatives:

1. **Unique footprint as the proof-order dimension.** Recursive re-entry makes
   the unique static size non-monotone at intermediate components.
2. **A completed owner `fundec` before proof synthesis.** This pre-shapes the
   program and moves the design too close to bounded derivation over an already
   chosen program.
3. **A separate monotone construction/search cost.** This orders dependencies
   but is not an actual program measurement and became unnecessary once skipped
   syntax was represented explicitly by holes.
4. **Rectangular fixed-point/worklist saturation.** This can tolerate reversed
   program-size dependencies but is more complex than separating proof
   skeletons from raw completion code.
5. **Complete-program bounded execution.** This remains a valid baseline but
   gives up proof-directed construction and local proof compatibility pruning.

### Search and Pruning Guarantee

The project does not require enumeration of every concrete program. The basic
unpruned proof/code search should advance fairly within the configured attack
language. A pruning or scheduling policy is acceptable when its intended
attack-witness guarantee is justified for that specific policy. No general
eventual-success claim is made merely because a policy is called a heuristic.

### Open Design and Implementation Questions

- the exact fair orchestration and join indexes for `ProofPool` and `CodePool`;
- the final materialized program-size measurement, reporting order, and any
  minimality claim;
- whether unused top-level function/global completion should later be added;
- witness-preservation arguments for each future prune or heuristic;
- compatible forward declarations and definitions for mutual recursion;
- how global, array, pointer, and richer type support extend hole contexts and
  completion components;
- a future outer schedule that expands function, variable, literal, and memory
  bounds instead of using one fixed configuration.

### Partition Responsibilities

Raw code partitioning and proof partitioning now have separate roles:

1. Raw syntax parents partition ordinary static AST size among their syntax
   children. Fixed heterogeneous children use constrained fixed-length
   partitioning; homogeneous lists use arbitrary-length partitioning.
2. Proof constructors use only the one-dimensional `proof_size`. For a target
   size `n`, the parent rule costs one and the sizes of its actual proof-tree
   premises are positive integers summing to `n - 1`. Static syntax and holes
   receive no share of this partition.
3. Unexecuted syntax is not assigned a proof-size partition. It remains a typed
   hole and is joined later with an independently sized raw code component.
4. Recursive calls and loop-rest rules consume only already synthesized strict
   proof subtrees.

Hole-aware syntax unification, memory boundaries, control results, variable
scope, and fragment effects decide whether components can be joined. There is
no numeric execution-footprint partition.

### Function Declarations and Identity

Mutual recursion requires forward declarations. The intended checker policy is
to allow a compatible `GVarDecl` and `GFun` with the same function identifier
when their function signatures are exactly equal and there is at most one
definition. Ordinary global-variable/function collisions remain invalid. The
synthesizer emits at most one declaration and one definition per function.

Because generation uses the canonical names `main`, `f`, and `g` in canonical
introduction order, existing structural component identity may retain concrete
function identifiers. This preserves the important distinction between a
self-call and a call to another function without generating alpha-renamed file
duplicates.

### Temporary Pipeline

```text
Raw syntax-size schedule -> CodePool
Proof-size schedule      -> ProofPool of hole-aware Big-Step components
                         -> hole-aware join / syntax unification
                         -> completed hole-aware ptree
                         -> call-free completion of remaining holes
                         -> concrete CIL-- file and ptree materialization
                         -> SyntaxChecker / Derivator / BigStepChecker
                         -> temporary structural examples/simple.c objective
```

The raw-code and proof schedules are independent but must be dovetailed fairly.
A newly generated raw fragment is joined with waiting compatible holes, and a
new hole-aware proof exposes hole demands that are joined with already generated
raw fragments. Recursive function and loop executions grow only through strict
proof subtrees and unify their complete hole-aware static syntax.

### Implementation Phases

1. **Hole representation and unification**
   - `HoleSyntax`, its utilities, pretty-printer, checker, and dedicated tests
     are implemented while reusing hole-independent concrete leaf types.
   - Correct the checker so IDs are unique within one AST/conclusion; test
     cross-conclusion reuse later at the `HoleBigStep` level.
   - Add `HoleSubstitution`, idempotent extension/composition, substitution-aware
     views, `HoleSyntaxUnify`, freshening, canonical renumbering, and occurs
     checks.
   - Add `HoleBigStep`, whose immutable proof tree is paired with a persistent
     component-local substitution.
2. **Proof/code dual synthesis**
   - Add raw-fragment metadata for free loop control and return effects.
   - Separate raw static syntax size from proof size, update component pools and
     join indexes, and rewrite the corresponding partition rules.
   - Rewrite `grow_prog.ml` as the call-free raw expression/block generator and
     `grow_proof.ml` as the hole-aware finite-proof generator supporting loops,
     direct calls, recursion, and mutual recursion through strict proof
     subtrees.
3. **Completion, validation, and attack**
   - Reconnect `bottom_up.ml` as the fair `CodePool`/`ProofPool` orchestration and
     join layer, complete remaining holes, and materialize concrete CIL-- files
     and `BigStep.ptree`s.
   - Validate candidates with `SyntaxChecker`, `Derivator`, `BigStepChecker`, the
     CIL roundtrip, and Sparrow; then reconnect objectives and the attack loop.
   - Implement compatible function declaration/definition handling, migrate
     tests, re-enable the synthesis/analyzer libraries, and connect the CLI.

Current partial migration provides `Syntax.ast`, the `HoleSyntax` module family,
CIL-- component-set layers, and placeholder CIL-- objective types. The component
layers still carry concrete syntax/proof payloads and must be adapted to
`HoleBigStep` components paired with `HoleSubstitution`. `bottom_up.ml`,
`attack.ml`, the grow modules, synthesis dune re-enabling, and CLI connection
remain pending.

Each implementation step changes one file at a time. Before each change, show
the planned patch and wait for approval.

Presentation note:

- Show-and-tell title/abstract for this work are recorded in
  `.agents/Show&Tell.notice`.

## Next Actions

1. Reject duplicate hole IDs inside one `HoleSyntax` AST and update its tests.
2. Implement and test `HoleSubstitution`, including sort-separated bindings,
   statement splicing, occurs checks, composition orientation, and idempotence.
3. Implement and test `HoleSyntaxUnify` under an existing substitution.
4. Define `HoleBigStep` and its proof-component identity/freeze boundary for
   repeated loop and function executions.

## Deferred Semantics Work

- Add global variable allocation and initializer semantics.
- Add array index lvalue evaluation.
- Add pointer dereference and pointer arithmetic.
- Add runtime-error tests for uninitialized reads, division by zero, invalid
  locations, and fuel exhaustion.
- Re-audit `BigStepChecker` when pointer, array, and global execution semantics
  are added.
- Reconnect Sparrow comparison after exported C compatibility is tested.
