# CIL-- Big-Step Checker

## Purpose

`lib/language/semantics/proof/ground/bigStepChecker.ml` independently validates CIL--
Big-Step proof trees. It checks that a supplied subtree follows the rule encoded
by its constructor, that its conclusion matches its premises, and that memories
and control states compose correctly.

The current active value type is `int`. `void` is used only for functions that
return no value. `Typ.TFun` carries direct-call signatures.

## Proof Levels

The checker mirrors `BigStep.tree`:

```text
etree -> expression evaluation
ltree -> lvalue resolution
itree -> instruction execution
stree -> statement execution
btree -> block execution
ftree -> function execution
ptree -> whole-program main execution
```

Each level can be checked independently. `check_tree` dispatches the wrapper
constructors to the corresponding checker.

## Core Invariants

### Expressions

- The expression stored in the conclusion matches the proof constructor.
- Premise input memories match the conclusion input memory.
- Integer constants evaluate to their represented value.
- Lvalue reads use the resolved location and current memory.
- Unary and binary results match `ValueOp` evaluation.
- `LAnd` and `LOr` use their dedicated short-circuit constructors.
- Short-circuit constructors enforce the truth value of the left premise and
  evaluate the right premise only on the required branch.

### Lvalues

- The active lvalue form is a scoped variable lvalue.
- The variable is bound in the current memory.
- The proof location equals `Memory.loc_of_var`.

### Instructions and calls

- Assignment lvalue and expression premises share the instruction input.
- Assignment subjects match, and output memory equals `Memory.write`.
- Direct callees match the callee expression, scoped identity, `vglob`, and
  `vtemp`.
- A callee has a complete `TFun` whose formal names and count match
  `fundec.sformals`.
- Call arity, argument inputs, argument values, and return-target policy match.
- `ITreeCallVoid` may discard an `int` return value.
- `ITreeCallAssign` requires a returned value and writes it to the target.
- The function subtree used by a call is the same `fundec` and starts from the
  call input memory.

### Statements and blocks

- Instruction trees form a sequential memory chain.
- Return, break, and continue conclusions preserve memory and carry the correct
  control value.
- `if` constructors select the branch matching the condition truth value.
- Loop constructors enforce their required body control:
  `Normal`, `Continue`, `Break`, or a return control.
- Block wrappers preserve the child block's memory and control.
- A `BTreeSeq` matches a prefix of the source block, stops only after non-normal
  control, and cannot execute extra statements or silently skip a non-empty
  block.

### Functions and top-frame memory

- Every subtree boundary memory is checked by `Memory.check_well_formed` before
  rule-specific comparisons. Equal but malformed memories are invalid.
- Stack, global, and heap storages contain only objects from their own location
  namespace. Object IDs, sizes, bindings, store locations, and `next_object_id`
  must be coherent.
- In the active subset, allocated objects and stored values are `int`/`IInt`.
- Stack bindings belong to one function scope; global bindings use global scope;
  binding locations are unique and point to object bases.
- Function `svar.vtype` is a complete canonical `TFun` matching `sformals`.
- A standalone function has a global, non-temporary `svar`; its formals and
  locals have the function scope, are non-global, have unique names, and use
  `int`.
- Local occurrences in the complete function body match their declarations;
  references to another function's locals are invalid.
- Actual argument count matches the formal count.
- Actual argument values are `Value.Int IInt`.
- `Memory.enter_function` creates the callee top frame.
- Formal values and locals reconstruct the exact function-body input memory.
- The function body matches `fundec.sbody`.
- `Memory.leave_function ~caller_stack:caller_mem.stack` restores the caller top
  frame while preserving the callee's final global and heap state.
- `FTreeReturn` requires return control from the body.
- `FTreeNoReturn` requires normal body completion and is valid only for a
  no-value return policy.

The proof tree stores only the active top frame. Deeper call frames are owned by
the recursive derivator/checker context and are restored explicitly at function
return.

### Whole programs

- `SyntaxChecker.check_file` is optional through `use_check_file` and defaults to
  enabled.
- The proof function is the file's unique `main`.
- `main` receives no arguments and begins with empty program input memory.
- Every direct callee appearing in the proof exists in the program file.
- Program output memory equals the function output memory.
- Program result equals the value returned by `main`.

The CLI already runs `SyntaxChecker.check_file` before derivation, so its final
proof check uses `check_ptree ~use_check_file:false` without skipping any
proof-level invariant.

## Regression Coverage

The direct regression suite is `lib/test/bigstepcheck_test.ml`. It currently
contains 105 passing cases.

| Area | Tests | Expected result |
|---|---|---|
| End-to-end examples | `accept_simple.c`, `accept_function_call.c`, `accept_fibonacci.c` | Derived proof trees accepted |
| Memory well-formedness | `reject_memory_negative_next_object_id`, `reject_memory_wrong_object_area`, `reject_memory_invalid_object_id`, `reject_memory_object_size`, `reject_memory_stack_global_scope`, `reject_memory_dangling_binding`, `reject_memory_duplicate_binding_location`, `reject_memory_stored_location`, `reject_memory_stored_value_type`, `reject_memory_unsupported_object_type` | Equal but malformed boundary memories rejected before rule-specific checking |
| Integer expressions | `reject_const_value`, `reject_const_subject`, `reject_lval_subject`, `reject_lval_value`, `reject_unop_type`, `reject_unop_operand`, `reject_unop_value`, `reject_binop_type`, `reject_binop_left`, `reject_binop_value`, `reject_binop_logical_constructor`, `reject_lor_true_premise`, `reject_lor_false_premise`, `reject_land_false_premise`, `reject_land_true_premise` | Wrong subjects, operands, values, unsupported int operators, and invalid short-circuit premises rejected |
| Variable lvalues | `reject_ltree_var_unbound`, `reject_ltree_var_location` | Unbound variables and incorrect locations rejected |
| Assignment and calls | `reject_set_subject`, `reject_set_output`, `accept_call_void_discard_return`, `reject_call_callee_varinfo_mismatch`, `reject_call_callee_vglob_mismatch`, `reject_call_callee_vtemp_mismatch`, `reject_call_expected_function`, `reject_call_without_parameter_types`, `reject_call_arity`, `reject_call_assigning_void`, `reject_call_formal_name_mismatch`, `reject_call_arg_input` | Valid discarded return accepted; malformed assignments, callees, signatures, arity, and inputs rejected |
| Returns, branches, blocks, and flow | `accept_return_none_void`, `reject_return_none_type`, `reject_return_some_type`, `reject_return_some_subject`, `reject_return_none_output`, `reject_break_output`, `reject_continue_output`, `reject_if_true_false_condition`, `reject_if_false_true_condition`, `accept_block`, `reject_block_output`, `reject_block_control`, `accept_loop_return`, `reject_loop_return_normal_body`, `reject_block_prefix_statement`, `reject_block_stopped_normal`, `reject_instr_flow`, `reject_block_after_return`, `reject_block_too_many_statements` | Valid void return, block, and loop return accepted; invalid memory, control, branch, and sequence structure rejected |
| Function signature and top frame | `accept_function_argument_binding`, `reject_function_argument_binding`, `reject_function_argument_arity`, `reject_function_pointer_argument`, `reject_function_svar_scope`, `reject_function_svar_vglob`, `reject_function_svar_vtemp`, `reject_function_formal_scope`, `reject_function_formal_vglob`, `reject_function_formal_nonint`, `reject_function_duplicate_formal_local`, `reject_function_body_local_metadata`, `reject_function_body_other_scope`, `reject_function_nonfunction_type`, `reject_function_without_parameter_types`, `reject_function_formal_name_mismatch`, `reject_function_too_few_formals`, `reject_function_too_many_formals`, `reject_nonvoid_function_without_return_value`, `accept_function_restores_caller_stack`, `reject_function_changed_caller_stack`, `accept_nested_call_restores_intermediate_stack`, `reject_nested_call_changes_intermediate_stack`, `accept_function_discards_callee_local_storage`, `reject_function_leaks_callee_local_storage`, `accept_function_preserves_global_update_and_caller_stack`, `reject_function_loses_global_update` | Correct binding, nested restoration, callee-local disposal, and global propagation accepted; non-int arguments, malformed metadata/signatures/body inputs, caller corruption, local leakage, and lost global updates rejected |
| Function and program conclusions | `reject_function_output`, `reject_function_control`, `reject_function_body_input`, `reject_program_output`, `reject_program_value`, `reject_program_pointer_value`, `reject_program_file`, `reject_program_main_function`, `reject_program_no_return` | Incorrect function/program subjects, memories, controls, int values, and files rejected |
| Rule-regression cases | `reject_loop_repeat_continue_body`, `reject_loop_continue_normal_body`, `reject_function_wrong_return_constructor`, `reject_ghost_callee_function`, `reject_main_nonempty_input`, `reject_empty_execution_nonempty_block`, `reject_call_callee_signature_mismatch`, `reject_call_void_callee_signature_mismatch` | Previously fragile loop, return-constructor, file membership, main-input, empty-block, and call-signature cases rejected |

Latest verified result:

```text
dune build                                         PASS
dune exec lib/test/bigstepcheck_test.exe           105 / 105 PASS
```

All active int-only proof constructors occur directly in the test source:

- expression: constant, lvalue, unary, binary, and four short-circuit rules;
- lvalue: variable;
- instruction: assignment, call-without-target, call-with-target;
- statement: instruction, both returns, break, continue, both if branches, all
  loop controls, and block;
- block, both function constructors, and the program constructor.

## Deferred Type and Proof Coverage

The following proof forms are outside the current checked/executable subset:

- `ETreeAddrOf` and `ETreeStartOf`;
- `LTreeMem` and `LTreeIndex`;
- `unsigned int` and other integer kinds;
- pointers, arrays, fields, compound values, and their operations;
- conversions involving any deferred type.

These constructors remain in the proof datatype for future work, but the
int-only regression suite does not claim them as supported. When a deferred
type is activated, add its runtime semantics, checker rules, and direct
positive/negative tests together.
