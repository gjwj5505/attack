Always follow these rules:

- Work in small steps
- Modify only one file at a time
- Explain briefly before coding
- Wait for user confirmation before continuing
- Do NOT run shell commands unless the user explicitly asks for that specific
  action. This includes `dune build`, tests, example runs, `git`, and other
  verification commands.
- You may freely read and explore files to understand the project
- Modify files only with `apply_patch`; do not use Python, shell redirection,
  heredocs, `cat > file`, or similar write methods for edits.
- When adding prune rules, include a short code comment showing the form of
  program/expression/command being removed.
- When the user gives a durable workflow instruction, add it to this
  `AGENTS.md` file after approval.
- During design discussions, keep durable conclusions, hypotheses, and next
  actions updated in `.agents/CONTEXT.md` as the conversation progresses.
- Do not delete or overwrite user-written content without explicit approval.
- Before modifying files, show the planned diff/patch and present options to
  the user; apply changes only after the user confirms.
- When explaining code or design, be concise and explain one function or concept
  at a time. Wait for the user to confirm understanding before moving to the
  next one.

Start by reading `.agents/CONTEXT.md`, then inspect only the files relevant to
the current request. Prefer concise status updates in Korean.

Attack workflow:
- When synthesis finds a successful analyzer attack, inspect why the analyzer
  produced the bad result.
- Strengthen the analyzer against that weakness in small approved steps.
- Re-run the relevant attack/example/tests after the fix.
- Record each successful attack and fix in `.agents/analyzer-attack-log.md`
  using the format: date - name - metadata including git version and analyzer
  engine when available - attack program - analyzer weakness - strengthening
  method.

Design/implementation workflow:
- For semantics-heavy work, discuss the design before coding.
- Present concrete options and tradeoffs when a design choice is open; let the
  user make the final decision.
- Record durable decisions in `.agents/CONTEXT.md` or `.agents/LANGUAGE.md`
  before or alongside implementation.
- Implement the chosen design in small patches.
- After implementation, walk through the code with the user one function or
  concept at a time.
- When the walkthrough reveals unclear naming, duplicated responsibility, or an
  awkward proof/semantic structure, refactor it before moving to the next major
  feature.
- Treat proof-tree shape, runtime semantics, checker policy, and CLI wiring as
  separate design concerns unless the user explicitly asks to combine them.
