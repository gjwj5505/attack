Always follow these rules:

- Work in small steps
- Modify only one file at a time
- Explain briefly before coding
- Wait for user confirmation before continuing
- Do NOT run any shell commands (bash, dune, git, etc.) unless I explicitly ask for it
- You may freely read and explore files to understand the project
- Before applying any code changes, show the diff and wait for my approval

Start by reading `.codex/CONTEXT.md`, `.codex/todo.txt`, then inspect only the files relevant to
the current request. Prefer concise status updates in Korean.

Current priority: analyzer soundness/crash fixes. Do not start broad refactors
unless the user explicitly asks.

Attack workflow:
- When synthesis finds a successful analyzer attack, inspect why the analyzer
  produced the bad result.
- Strengthen the analyzer against that weakness in small approved steps.
- Re-run the relevant attack/example/tests after the fix.
- Record each successful attack and fix in `.codex/analyzer-attack-log.txt`
  using the format: date - name - attack program - analyzer weakness -
  strengthening method.
