# Project Agent Instructions

These instructions apply only to this project and supplement `~/.codex/AGENTS.md`.

When this file explicitly overrides a global instruction, follow this file within the stated scope.

## Rule priority

This document is organized into three levels:

1. **Critical project rules** protect private files and project-specific invariants.
2. **Operational workflows** define how project work should proceed.
3. **Reference rules** describe project-specific documentation responsibilities.

Within this file, Critical project rules take precedence over Operational and Reference rules.

# Part I — Critical project rules

## Protected private file

The file `.agents/생각 끄적끄적` is private and off-limits.

- Never read, inspect, modify, move, rename, delete, quote, summarize, or infer its contents.
- Do not use indirect evidence to reconstruct or reveal its contents.

## Project-specific command policy

This section explicitly specializes the global command policy.

- Read-only inspection commands remain allowed under the global rules.
- Do not run `dune build`, tests, example programs, Git commands, or other verification commands unless:
  - the user explicitly approves that command or command scope; or
  - an active continuous-work approval explicitly covers it.
- Do not treat permission to edit code as permission to run verification commands unless the approved scope includes verification.

## Semantic separation

Treat the following as separate design concerns unless the user explicitly asks to combine them:

- proof-tree shape;
- runtime semantics;
- checker policy;
- CLI wiring.

Do not merge changes across these concerns merely because they are related.

# Part II — Operational workflows

## Project startup

At the start of project work:

1. Read this file.
2. Read `.agents/CONTEXT.md`.
3. Inspect only the files relevant to the current request.

Read `.agents/README.md` when human-facing project background or usage information is relevant.

## Project documentation

Use the project documentation files as follows:

- `.agents/AGENTS.md`: durable project-specific workflow instructions and constraints.
- `.agents/CONTEXT.md`: current project state, recent changes, active hypotheses, blockers, and next actions.
- `.agents/LANGUAGE.md`: stable language and semantics design.
- `.agents/README.md`: human-facing project documentation.

When the user approves a durable workflow change specific to this project, update `.agents/AGENTS.md`.

Update `.agents/CONTEXT.md` at roughly the granularity of a meaningful Git commit:

- record coherent changes in project state;
- record relevant design decisions, hypotheses, blockers, and next actions;
- do not update it for every minor discussion or mechanical edit.

Record stable language or semantics decisions in `.agents/LANGUAGE.md`, not `.agents/CONTEXT.md`.

## Semantics-heavy design workflow

For work involving semantics or proof structure:

1. Discuss the design before implementation.
2. Present concrete options and tradeoffs when more than one reasonable design exists.
3. Record durable decisions in `.agents/LANGUAGE.md` or `.agents/CONTEXT.md`, as appropriate.
4. Implement the chosen design in small, approved atomic change sets.
5. Briefly explain the resulting code and design after implementation.

When implementation reveals unclear naming, duplicated responsibility, or an awkward proof or semantic structure:

- report the issue;
- propose a focused refactoring;
- do not silently mix it into the current change set unless approved.

## Analyzer attack workflow

When synthesis finds a successful analyzer attack:

1. Inspect why the analyzer produced the bad result.
2. Identify the analyzer weakness responsible for the attack.
3. Propose a focused strengthening step.
4. Strengthen the analyzer in small, approved atomic change sets.
5. Re-run the relevant attack, example, or tests after approval or within an active scope that covers verification.
6. Record the successful attack and fix in `.agents/analyzer-attack-log.md`.

Use this log format:

```text
date - name - metadata - attack program - analyzer weakness - strengthening method
```

Include Git version and analyzer engine in the metadata when available.

## Prune rules

When adding a prune rule:

- include a short code comment;
- show the form of program, expression, or command being removed;
- keep the comment focused on the matched form rather than restating the implementation.
