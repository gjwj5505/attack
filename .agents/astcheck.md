# CIL-- AST Checker

## Purpose

`lib/language/astChecker.ml` validates directly constructed CIL-- syntax before
derivation, rendering, or synthesis debugging. It is a structural checker, not
a complete C typechecker and not a runtime-definedness checker.

The current active value type is `int`. `void` is used only for functions that
return no value, and `Typ.TFun` carries function signatures.

## Check Order

`AstChecker.check_file` stops at the first error and performs checks in this
order:

1. Function `svar.vtype` and `sformals` consistency.
2. Exactly one `int main(void)`.
3. Unique global names.
4. Unique formal/local names within each function.
5. No global/formal or global/local name collision.
6. Scoped variable declarations and references.
7. `break` and `continue` control-flow context.
8. Function return shape.
9. CIL-- -> GoblintCil -> CIL-- structural roundtrip.
10. GoblintCil `Check.checkFile` invariants.

## Structural Invariants

### Function signatures

- Every function `svar` has a complete `Typ.TFun (_, Some formals)` type.
- The names and number of parameters in that type match `fundec.sformals`.
- A function occurrence uses the same complete `varinfo` as its declaration.
- `SyntaxUtil.function_return_type` extracts the return type from the canonical
  `svar.vtype`.

### Program entry

- A file contains exactly one function named `main`.
- `main` returns `int`.
- `main` has no parameters.

### Names and scopes

- Global names are unique across functions, declarations, and definitions.
- Formal and local names are unique within one function.
- Different functions may use the same local name.
- A global name may not be reused by a formal or local.
- Global declarations use `VarId.Global`.
- Formals and locals use `VarId.Function function_name`.

### Variable references

- Every occurrence resolves by its scoped `VarId`.
- The occurrence and declaration must have identical `varinfo`, including
  `vglob`, `vtemp`, and the canonical function signature where applicable.
- The checker recursively visits the active int-only expression, instruction,
  statement, block, call, return, and single-initializer paths.

### Control and returns

- `break` and `continue` are valid only within a loop, including through nested
  `if` and block nodes.
- A `void` function cannot return a value.
- An `int` function cannot use `return` without a value.
- Return checks recurse through `if`, loop, and block nodes.

### Bridge and GoblintCil

- The CIL-- -> GoblintCil -> CIL-- roundtrip must preserve structural equality.
- GoblintCil checks remaining active CIL invariants such as call arity and use
  before declaration.
- GoblintCil warnings emitted by negative tests are expected when the resulting
  `Check.checkFile` result is `false`.

## Regression Coverage

The direct test suite is `lib/test/astcheck_test.ml`. The current suite contains
57 cases.

| Area | Tests | Expected result |
|---|---|---|
| Main and baseline | `accept_minimal_main`, `reject_missing_main`, `reject_multiple_main`, `reject_invalid_main_type`, `reject_main_with_parameters` | Valid main accepted; four malformed entry points rejected |
| Function signatures | `reject_invalid_function_type`, `reject_incomplete_function_type`, `accept_multi_formal_function_signature`, `reject_function_formal_name_mismatch`, `reject_function_too_few_formals`, `reject_function_too_many_formals` | Complete matching `TFun` accepted; invalid shape, name, or count rejected |
| Duplicate names | `reject_duplicate_global_name`, `reject_duplicate_formal_name`, `reject_duplicate_local_name`, `reject_formal_local_name_collision`, `accept_same_local_name_in_different_functions`, `reject_duplicate_function_and_global_name` | Duplicate names in one namespace rejected; same local name in different functions accepted |
| Global/local collision | `reject_global_and_local_same_name`, `reject_global_and_formal_same_name` | Global name reuse by a local or formal rejected |
| Scoped IDs | `reject_invalid_global_scope`, `reject_invalid_function_scope`, `reject_invalid_formal_scope`, `reject_invalid_local_scope` | Incorrect declaration scope rejected |
| Declaration/reference identity | `reject_cross_function_reference`, `reject_variable_temp_mismatch`, `accept_function_reference`, `reject_function_occurrence_signature_mismatch`, `reject_variable_vglob_mismatch` | Correct reference accepted; wrong scope or metadata rejected |
| Globals and initialization | `reject_undeclared_global_reference`, `reject_local_reference_in_global_initializer`, `accept_global_reference`, `accept_uninitialized_global` | Valid globals accepted; missing/global-initializer local references rejected |
| Int expressions | `reject_undeclared_in_unop`, `reject_undeclared_in_binop` | Missing variables inside unary and binary expressions rejected |
| Instructions and calls | `reject_undeclared_in_set_lval`, `reject_undeclared_in_set_exp`, `reject_undeclared_in_call_return_lval`, `reject_undeclared_call_callee`, `reject_undeclared_call_argument` | Missing variables found in every active instruction/call position |
| Statement recursion | `reject_undeclared_if_condition`, `reject_undeclared_if_then`, `reject_undeclared_if_else`, `reject_undeclared_in_loop`, `reject_undeclared_in_block` | Missing variables found through all active statement containers |
| Control flow | `reject_break_outside_loop`, `reject_continue_outside_loop`, `accept_break_continue_inside_loop`, `reject_break_in_nested_if`, `reject_continue_in_nested_block` | Loop context preserved through nesting |
| Return shape | `reject_return_value_in_void_function`, `reject_return_without_value_in_nonvoid_function`, `reject_nested_return_value_in_void_function`, `reject_nested_return_without_value`, `reject_block_return_value_in_void_function` | Invalid direct and nested returns rejected |
| Roundtrip | `reject_roundtrip_temp_loss` | Loss of `vtemp` metadata reported as `Bridge_error` |
| GoblintCil | `reject_goblint_call_arity`, `reject_goblint_call_before_declaration` | Bad arity and call-before-declaration rejected |

Latest verified result:

```text
dune build                                  PASS
dune exec lib/test/astcheck_test.exe        57 / 57 PASS
```

The negative GoblintCil cases intentionally print diagnostics such as `Not
enough arguments` and `Unknown id ... for f`.

## Deferred Type Coverage

The following types or operations are outside the current AstChecker guarantee:

- `unsigned int` and other integer kinds;
- pointers, `Mem`, `AddrOf`, and `StartOf` type correctness;
- arrays and index type correctness;
- compound types and field offsets;
- conversions involving any deferred type.

These constructors may remain syntactically present in bridge-facing CIL--, but
they are not part of the active checked/executable subset. When a deferred type
is activated, add its explicit checker rules and direct negative/positive tests
before considering it validated.

## Out of Scope

AstChecker does not prove runtime definedness. Uninitialized reads, division by
zero, invalid locations, nontermination, and future pointer/array runtime errors
belong to derivation and Big-Step proof checking.
