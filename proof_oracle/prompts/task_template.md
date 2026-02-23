# Proof Oracle — Task Template

## Workflow

Follow this exact workflow for proving the lemma:

### Step 1: Set Up the File

1. Check if the target file exists. If yes, read it. If no, create it.
2. Ensure the file has `import Mathlib` at the top.
3. If the lemma depends on definitions (listed in Dependencies below), verify they exist in the file. If any dependency is missing, report `END_REASON:ERROR`.

### Step 2: Write the Lemma Statement

1. Write the lemma statement using the suggested signature.
2. Initially use `sorry` as the proof body.
3. Check diagnostics with lean-lsp-mcp to confirm the statement type-checks.
4. If the statement has type errors, make minimal fixes and document why.

### Step 3: Prove the Lemma

Follow the proof search strategy from the system prompt:

1. **Try simple tactics first:**
   - `by simp [relevant_defs]`
   - `by ring`
   - `by omega`
   - `by decide`
   - `by norm_num`
   - Short chains: `by simp [defs]; ring`

2. **If simple tactics fail, search Mathlib:**
   - Use LeanExplore to find relevant lemmas.
   - Try `by exact relevant_lemma` or `by rw [relevant_lemma]`.

3. **If search-and-apply fails, try structured proof:**
   - Use `by` block with intermediate `have` steps.
   - Use `calc` for equational reasoning.
   - Use `induction` or `cases` if appropriate.
   - After each tactic, check the goal state with lean-lsp-mcp.

4. **After each attempt:**
   - Check diagnostics immediately.
   - If there are errors, read them carefully before trying the next approach.
   - Do not repeat the same failing approach.

### Step 4: Verify and Report

1. Once you believe the proof is complete, do a final diagnostics check.
2. Confirm: zero errors, no `sorry`, no `axiom`.
3. Output `END_REASON:COMPLETE`.

If you cannot complete the proof:
- Leave the best partial progress in the file (with `sorry` for gaps).
- Describe what you tried and what remains.
- Output `END_REASON:LIMIT`.
