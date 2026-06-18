# Language Design

이 프로젝트의 합성 언어는 ISO C 전체가 아니라, Sparrow가 CIL을 거쳐
분석하기 쉬운 형태로 낮출 수 있는 structural core language이다. C-like
surface syntax는 입력/출력 편의를 위한 facade이며, semantics와 synthesis
target은 이 structural core AST다.

목표는 C 표준의 모든 의미를 모델링하는 것이 아니다. 목표는 우리가 Big-Step
proof tree로 정의한 concrete execution이 Sparrow의 abstract semantics와
비교 가능한 형태가 되도록, Sparrow-CIL 변환 이후의 core command와 잘 대응되는
언어를 정의하는 것이다.

## Design Principle

- Surface syntax는 C처럼 둘 수 있지만, faithful C surface semantics를 목표로
  하지 않는다.
- Internal AST와 Big-Step semantics는 Sparrow가 실제로 분석하는 CIL/CFG core에
  가깝게 둔다.
- Parser/printer는 사람이 읽기 쉬운 C subset을 다룬다.
- Analyzer wrapper는 이 C subset을 `.c` 또는 `.i` 파일로 출력해 Sparrow에
  전달할 수 있다.
- `.i`는 합성 언어가 아니라, 필요할 때 Sparrow에 넘기는 preprocessed C 입력
  형식으로만 본다.
- 새 feature는 C surface syntax를 넓히기 위해 추가하지 않는다. Sparrow CFG
  command로의 lowering과 Big-Step concrete meaning이 명확하고, analyzer attack
  목적에 필요할 때만 추가한다.

Sparrow의 흐름은 다음과 같다.

```text
C source or .i
  -> CIL Frontc.parse
  -> CIL AST
  -> Sparrow CFG commands
  -> abstract interpretation
```

따라서 우리가 맞춰야 하는 대상은 `.i` 텍스트 자체가 아니라, CIL 변환 이후
Sparrow가 해석하는 command 구조다.

## Initial Subset

초기 언어는 `int main() { ... }` 하나만 지원한다.

Statements:

- code block: `{ stmt+ }`, used only as `main`, `if`, and `while` body
- initialized local declaration: `int x = expr;`
- assignment: `x = expr;`
- conditional: `if (expr) block else block`
- loop: `while (expr) block`
- return: `return expr;`

Expressions:

- integer literal
- variable
- unary minus: `-expr`
- arithmetic binary operators: `+`, `-`, `*`, `/`, `%`
- comparisons: `==`, `!=`, `<`, `<=`, `>`, `>=`

초기에는 `!`, `&&`, `||`, casts, calls, arrays, pointers, structs,
assignment expressions, increment/decrement, compound assignment는 제외한다.
필요할 때 Sparrow 대응을 확인한 뒤 한 기능씩 추가한다.

## Concrete Syntax

Initial parser syntax is intentionally smaller than C. It accepts only one
function, `int main()`, and a small statement/expression subset that lowers
predictably through CIL.

```ebnf
program     ::= "int" ident "(" ")" block EOF
                (* Strict subset: exactly one function definition is accepted,
                   and its identifier must be main. No global declarations, no
                   multiple functions, no function parameters, no non-int
                   return type, no old-style function definition. *)

block       ::= "{" stmt* "}"
                (* Strict subset: block items are only our stmt grammar.
                   No labels, case/default labels, mixed arbitrary C declarations,
                   or attributes. *)

stmt        ::= decl
              | assign
              | if_stmt
              | while_stmt
              | return_stmt
                (* Strict subset: no expression statement except assignment,
                   no empty statement, no for/do-while/switch/goto/break/continue,
                   no standalone block statement, no labels, no asm. *)

decl        ::= "int" ident "=" expr ";"
                (* Strict subset: int locals only. No pointers, arrays, structs,
                   unions, enums, typedef names, storage classes, qualifiers,
                   multiple declarators, complex declarators, or uninitialized
                   declarations. *)
assign      ::= ident "=" expr ";"
                (* Strict subset: simple variable assignment only. No lvalue
                   forms with dereference, field, array index, compound assignment,
                   or assignment expression. *)
if_stmt     ::= "if" "(" expr ")" block "else" block
                (* Strict subset: else is mandatory. No dangling-else ambiguity
                   and no if-without-else form. Branch bodies must be blocks. *)
while_stmt  ::= "while" "(" expr ")" block
                (* Strict subset: while only. No for, do-while, break, or
                   continue. Loop body must be a block. *)
return_stmt ::= "return" expr ";"
                (* Strict subset: return value required. No bare return and no
                   function-specific return type variation. Return may appear
                   anywhere a statement may appear. *)

expr        ::= equality
                (* Strict subset: pure integer expressions only. No side effects,
                   calls, casts, sizeof, address-of, dereference, array access,
                   field access, conditional operator, comma operator. *)

equality    ::= relational (("==" | "!=") relational)*
                (* Strict subset: equality over integer expressions only.
                   Chaining is parsed in a C-like left-associative way. *)
relational  ::= additive (("<" | "<=" | ">" | ">=") additive)*
                (* Strict subset: relational operators over integer expressions
                   only. Chaining is parsed in a C-like left-associative way. *)
additive    ::= multiplicative (("+" | "-") multiplicative)*
                (* Strict subset: integer + and - only. No pointer arithmetic. *)
multiplicative
            ::= unary (("*" | "/" | "%") unary)*
                (* Strict subset: arithmetic multiplicative operators only.
                   Bitwise and shift operators are excluded initially. *)
unary       ::= "-" unary
              | primary
                (* Strict subset: unary minus only. No !, ~, *, &, ++, --,
                   sizeof, alignof, or casts. *)
primary     ::= integer
              | ident
              | "(" expr ")"
                (* Strict subset: no string/char/float constants, compound
                   literals, statement expressions, or function calls. *)

ident       ::= /[A-Za-z_][A-Za-z0-9_]*/
                (* Strict subset: lexer-level identifier only. No typedef-name
                   distinction is needed because typedef is excluded. *)
integer     ::= /[0-9]+/
                (* Strict subset: decimal integer literals only. No suffixes,
                   signs, hex/octal/binary literals, character constants, or
                   floats. Negative constants are parsed as unary minus applied
                   to a nonnegative integer literal, matching C syntax. *)

line_comment
            ::= "//" [^\n\r]* ("\n" | "\r" | "\r\n" | EOF)
block_comment
            ::= "/*" .* "*/"
                (* Comments are lexical trivia. They do not appear in the AST. *)
```

Parser notes:

- Declarations are syntactically statements and must have explicit
  initialization.
- `else` is mandatory for `if` in the initial subset. This avoids a dangling
  `else` design choice and matches the existing total command-style language.
- Empty blocks are accepted by the parser. Synthesis should still avoid
  generating empty blocks unless a later search policy explicitly wants them.
- `if` and `while` bodies must be blocks. This keeps the accepted syntax close
  to the printer output and avoids statement-body normalization choices.
- Standalone block statements are not part of the initial subset. Blocks appear
  only as the body of `main`, `if`, and `while`.
- Chained comparisons such as `a < b < c` are accepted with C-like parsing:
  `(a < b) < c`.
- `//` and `/* ... */` comments are accepted as lexer trivia.
- No preprocessor directives, typedefs, storage classes, type qualifiers, or
  function parameters are part of the initial grammar.

## Concrete Semantics

이 언어의 concrete semantics는 ISO C semantics가 아니라 이 프로젝트의
Sparrow-CIL core semantics다.

- Variables hold mathematical integers in the initial model.
- Conditions use C/Sparrow truthiness: `0` is false, nonzero is true.
- Expressions are pure.
- Expression evaluation order is deterministic left-to-right.
- Blocks initially do not introduce complex C scope behavior; generated
  variable names should be unique enough to avoid shadowing ambiguity.
- All declarations in the supported language must have explicit initializers.
  This policy applies to both local declarations now and future global
  declarations.
- Signed overflow, uninitialized read, division by zero, and other C undefined
  behavior are outside the initial language.
- Division and modulo are syntactically valid, but Big-Step semantics and
  synthesis must not evaluate or generate `/` or `%` expressions whose divisor
  evaluates to zero.

## AST Shape

The parser and synthesis should use the same AST type. The parser should build
the core AST directly instead of producing a separate parsed syntax tree.

Types are kept in a separate `Typ` module, implemented by `lib/language/typ.ml`.
The initial type language contains only `int`, but the module is separate
because pointer, array, struct, and function types will be added later.

Initial type shape:

```ocaml
(* typ.ml *)
type t =
  | Int
```

Identifiers are lexer-validated strings:

```ocaml
type id = string
type integer_literal = Int64.t
```

Typed names are represented by a shared binding type. Function parameters,
local declarations, and future global declarations should all use this shape.

```ocaml
type binding = {
  typ : Typ.t;
  name : id;
}
```

Assignment targets are lvalues. The initial subset only has variable lvalues,
but this type is intentionally separate so pointer, array, and struct lvalues
can be added later.

```ocaml
type lval =
  | LVar of id
```

Expressions stay in the existing `Exp` module style. Identifier expressions are
represented as `Lval (LVar x)`, not as a separate `Var x` constructor.

```ocaml
module Exp = struct
  type uop = Uminus

  type bop =
    | Eq | Ne | Lt | Le | Gt | Ge
    | Plus | Minus | Times | Div | Mod

  type t =
    | Int of integer_literal
    | Lval of lval
    | Uop of uop * t
    | Bop of bop * t * t
end
```

Integer literals are stored as `Int64.t` in the syntax tree so the parser can
preserve decimal literals larger than 32-bit `int`, such as the operand in
`-2147483648`. The initial runtime type is still only signed 32-bit `int`;
Big-Step semantics converts literals to runtime `Value.Int` values and rejects
out-of-range literals or arithmetic overflow as undefined behavior.

Statements use the `Stmt` module name, not `Cmd`. This avoids confusion with
Sparrow CFG commands. A C code block is represented as a statement list alias,
not as a record wrapper.

```ocaml
module Stmt = struct
  type t =
    | Decl of binding * Exp.t
    | Assign of lval * Exp.t
    | If of Exp.t * codeblock * codeblock
    | While of Exp.t * codeblock
    | Return of Exp.t

  and codeblock = t list
end
```

Empty code blocks are represented as `[]`. The parser accepts them, but
synthesis should avoid generating them unless a later search policy explicitly
wants empty blocks.

Functions store their source-level signature. The initial parser accepts one
`int ident()` function definition and requires that identifier to be `main`.
It therefore creates `ret_type = Typ.Int`, `name = "main"`, and `params = []`.

```ocaml
type func = {
  ret_type : Typ.t;
  name : id;
  params : binding list;
  body : Stmt.codeblock;
}

type program = {
  main : func;
}
```

There are no labels and no source locations in the core AST. Labels may be
added later by a separate labeling pass if pretty-printing, tables, or
visualization need them. Source locations are intentionally omitted because
synthesis creates AST values directly and dummy locations would pollute
comparison, hashing, and proof construction.

String/printer helpers should keep the existing project style:

```ocaml
Exp.string_of_t
Stmt.string_of_t
Stmt.string_of_codeblock
string_of_program
```

## Expected Sparrow Mapping

The intended correspondence is:

```text
int x = e;      -> Cset(x, e)
x = e;          -> Cset(x, e)
if (e) S else T -> Cassume(e) on true branch, Cassume(!e) on false branch
while (e) S     -> loop CFG with Cassume(e) body edge and Cassume(!e) exit edge
return e;       -> Creturn(e)
```

This matches Sparrow's current structure:

- C input is parsed by CIL `Frontc.parse`.
- CIL `Instr` nodes are flattened into `Cset` or `Ccall`.
- CIL `If` nodes get branch assumptions inserted.
- CIL `Loop` nodes are removed as commands after their CFG edges and assumptions
  are generated.
- CIL `Return` nodes become `Creturn`.

## Why Not Use `.i` As The Language

`.i` is not a semantic core language. It is preprocessed C text.

Using `.i` as the synthesis language would pull in textual preprocessing
artifacts such as line directives, macro expansion results, include output, and
compiler-specific details. Those details are not the level where Sparrow's
abstract semantics is defined.

For our purpose, a preprocessor-free C subset is better:

- It can be printed as `.c`.
- It can also be saved with `.i` extension if Sparrow wrapper needs that.
- It keeps proof trees readable.
- It keeps the concrete semantics under our control.
- It still lowers predictably to Sparrow's CIL/CFG core.

## Known Risks

- CIL may rewrite expressions by adding casts or temporaries. The initial subset
  should avoid constructs that trigger non-obvious lowering.
- Local `int x;` in C has uninitialized value semantics, while our proof system
  needs a definite concrete state. Prefer explicit initialization.
- Sparrow's interval semantics uses abstract transfer functions over CIL
  expressions, not a separately documented concrete semantics. We infer the
  intended concrete correspondence from the implementation.
- C integer overflow is not modeled initially. Attacks must not rely on
  overflow behavior until a policy is chosen.
- Division and modulo are included in the syntax, but their concrete semantics
  and undefined-behavior policy, especially division by zero, must be fixed
  before Big-Step support uses them.
- Short-circuit operators `&&` and `||` are excluded initially because they are
  expression-level control flow and can complicate the proof tree.
- Side-effect expressions such as `x++`, `x += 1`, and `(x = e)` are excluded
  because they require expression judgments with state changes.
- Scope and shadowing should be restricted. Generated variables should avoid
  reusing names in nested blocks.
- Function calls are excluded initially. Sparrow has library and user-function
  models, but they introduce interprocedural semantics.

## Development Policy

When adding a new syntax feature:

1. Check how CIL lowers it.
2. Check how Sparrow represents it in `IntraCfg.Cmd`.
3. Define its Big-Step rule in our language.
4. Add printer output that lowers predictably through CIL.
5. Add a small example and compare the expected Sparrow command behavior.

The safe default is to reject or not generate any C feature whose CIL lowering
or Sparrow abstract transfer is not yet understood.

## C Feature Matrix

The current support/addition matrix is tracked in `.agents/c-feature.csv`.
