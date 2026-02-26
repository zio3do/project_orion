# Project Orion — Retrospective

## What Is This Project?

Project Orion is an AI-assisted mathematical formalization engine for Lean 4.
It takes an underdeveloped area of Mathlib, decomposes it into a structured library blueprint, and proves every entry automatically — producing a complete, verified Lean 4 library with zero `sorry` and zero `axiom`.

The system is organized into five pillars:

1. **Edge Finder** — Identifies underdeveloped "pockets" in Mathlib via LLM concept generation, LeanExplore search, and algorithmic scoring.
2. **Proof Oracle** — Proves individual lemmas by spawning fresh Claude Code sessions with MCP tools, hard-gated by `lake env lean` verification.
3. **Library Architect** — Decomposes a mathematical theme into a dependency-ordered blueprint of definitions and lemmas, each with a complete `LemmaSpec`.
4. **Library Weaver** — Walks the blueprint's dependency DAG, accumulates Lean source files, and invokes the Proof Oracle per entry to produce the final library.
5. **Proof Foundry** (future) — Assembles verified proofs into Mathlib-conformant PRs.

The first end-to-end test target was **Graded Order Combinatorics** — level sets, rank generating polynomials, and saturated chains over graded posets. The pipeline produced 3 Lean files (250 lines total) containing 2 definitions and 16 theorems, all verified against Lean 4 v4.29.0-rc2 and Mathlib.

---

## Biggest Challenges Overcome

### 1. The Grounding Problem (Library Architect v1 → v2)

**What went wrong.** The v1 pipeline asked an LLM to generate Lean 4 signatures "from memory." The LLM had no access to actual Mathlib source code during generation. The result was four categories of errors:

- **Syntax errors** — malformed Lean 4 syntax.
- **Mathematical soundness errors** — signatures that stated false or trivially unprovable things.
- **Typeclass/instance errors** — missing or wrong typeclass constraints (e.g. `Preorder` where `PartialOrder` was needed).
- **API name errors** — hallucinated Mathlib names that do not exist (e.g. `Polynomial.coeff_sum` instead of `Polynomial.finset_sum_coeff`).

**How we fixed it.** The v2 pipeline introduced a two-pass grounding loop:

1. A *skeleton pass* generates a coarse blueprint with mathematical intent but no Lean syntax.
2. A *grounded expansion pass* uses LeanExplore to search for real Mathlib declarations, then feeds the LLM actual Mathlib source snippets and oracle-proven exemplars before asking it to write signatures.

Each signature is individually checked by `lake env lean` elaboration before the blueprint is considered valid.

**Result:** All 19 entries in the Graded Order Combinatorics blueprint passed elaboration. Zero hallucinated API names survived into the final blueprint.

---

### 2. False Positive Bug in the Verification Pipeline

**What went wrong.** The Proof Oracle's verifier checked that the *whole file* compiled with no errors, no `sorry`, and no `axiom`. But it did not check that the *specific target lemma* was actually present in the file. This meant the Oracle could report "success" when the Claude Code agent had failed to write the proof at all — or had accidentally deleted it while editing.

We discovered this when run 1 reported 10/18 entries as "proved," but manual inspection found only 7 were real. Three entries had empty or missing proofs that compiled only because the lemma was simply absent.

**How we fixed it.** We added a `_check_lemma_present()` function to `verifier.py` and a `lemma_name` parameter to the `verify()` method. After compilation succeeds, the verifier greps the file for the target theorem/def name. If the name is missing, verification fails regardless of compilation status.

**Lesson:** Never trust agent self-reports. The verification gate must check both *negative conditions* (no errors, no sorry, no axiom) and *positive conditions* (the target artifact exists).

---

### 3. The `rankGenPoly_coeff` Bottleneck

**What went wrong.** This polynomial algebra proof failed 10 consecutive Oracle attempts, consuming $4.30 and ~3 hours of wall time. The Oracle repeatedly made three mistakes:

- **Wrong API name:** Used `Polynomial.coeff_sum` (does not exist) instead of `Polynomial.finset_sum_coeff`.
- **Wrong tactic under binders:** Used `rw` instead of `simp_rw` when rewriting under `fun x =>` binders.
- **The nsmul trap:** For `Polynomial ℕ`, scalar multiplication is `nsmul`, not `•` over a ring. The Oracle did not account for this.

Each fresh Oracle session repeated the same mistakes because it had no memory of prior failures (by design — fresh sessions prevent context pollution, but they also prevent learning).

**How we fixed it.** We proved `rankGenPoly_coeff` manually in ~15 minutes at zero cost. The experience led directly to the creation of **theme-specific proof guides** (see challenge 6 below).

**Lesson:** When the cost of automated proof search exceeds the cost of human intervention, switch strategies. The Oracle is a tool, not a religion.

---

### 4. The `saturatedChain_exists` Proof (Hardest Lemma)

This was the most technically demanding proof in the library. It required:

- **Spec correction:** The original spec used `[Preorder α]`, but the proof requires `[PartialOrder α]` because `eq_or_lt_of_le` needs antisymmetry. The base case `a = b` is unreachable under a mere preorder.
- **Discovering automatic instances:** `WellFoundedLT α` is automatic from `[GradeOrder ℕ α]`, and `IsStronglyAtomic` is automatic from `WellFoundedLT`. This means `exists_covBy_le_of_lt` is available without any additional assumptions.
- **API migration:** `List.Chain'` is deprecated in current Mathlib; `List.IsChain` is the replacement. Dot notation on deprecated aliases fails for new method names.
- **Existential type structuring:** The original spec used `l.head (by assumption)` inside an existential, but `by assumption` cannot resolve `l ≠ []` from a conjunction that has not been destructured. The fix was to use nested existentials: `∃ (l) (hne : l ≠ []), ...`.
- **Strong induction:** The proof uses `Nat.strongRecOn` on the grade gap `grade ℕ b - grade ℕ a`, with `subst` for variable elimination in the base case.

This proof was written manually after the Oracle failed to find it.

**Lesson:** For proofs that require discovering non-obvious automatic instances and restructuring the goal statement, current LLM-based proof search is insufficient. The bottleneck is not tactic generation but *problem formulation*.

---

### 5. Two-Layer Architecture Decision

Early design considered replicating Numina's four-agent architecture (Coordinator, Blueprint, Sketch, Proof). We rejected this in favor of a simpler two-layer design:

- **Layer 1 (Python orchestrator):** Dumb. Manages the DAG walk, file accumulation, retry budget, and artifact logging. Contains zero mathematical reasoning.
- **Layer 2 (Claude Code agent):** Smart but untrusted. Given a complete prompt with the file, spec, and context. Writes and verifies proofs autonomously via MCP tools.

Key design choices:

- **Fresh session per retry.** Prevents context pollution from failed attempts. Each retry starts with a clean slate.
- **Agent self-reports are ignored.** Only `lake env lean` output is authoritative. The orchestrator parses compilation output, not agent messages.
- **No inter-agent communication.** The Python orchestrator is the only entity with state. Agents are stateless workers.

This two-layer design reduced implementation complexity by roughly 60% compared to the four-agent alternative, while achieving the same core capability.

---

### 6. Theme-Specific Proof Guides

After the `rankGenPoly_coeff` failure, we created `theme_graded_order_combinatorics.md` — a 388-line document containing verified tactic patterns, correct API names, and common pitfalls specific to graded order combinatorics.

The prompt builder was modified to auto-load guides by namespace slug convention: for namespace `Orion.GradedOrderCombinatorics`, it looks for `theme_graded_order_combinatorics.md` in the prompts directory.

**Result:** All 7 remaining easy lemmas in run 2 proved on first attempt, each with budget=1. Total run time: 1h 10m. Zero failures.

**Lesson:** A 388-line document of correct patterns is worth more than 10 Oracle retries. Theme guides are the highest-leverage intervention available in this system.

---

### 7. File Accumulation and DAG Ordering

Library Weaver must produce Lean files that compile incrementally. Each entry's proof may depend on definitions or theorems proved earlier in the same file. This requires:

- Walking the blueprint's dependency DAG in topological order.
- Accumulating proven entries into the target file before invoking the Oracle for the next entry.
- Handling the case where an entry depends on entries in *different* files (cross-file dependencies).

The `file_manager.py` module maintains a `{filepath: content}` mapping that grows monotonically. When the Oracle proves an entry, its code block is appended to the appropriate file. The next Oracle invocation receives the updated file as context.

This "snowball" pattern — where each proof attempt sees all previously proved results — is simple but effective. It means the Oracle never has to rediscover definitions or import paths; they are already in the file it is given.

---

## What the Pipeline Produced

### Graded Order Combinatorics Library (18/18 entries)

| File | Lines | Items |
|------|-------|-------|
| `Orion/GradedOrderCombinatorics/LevelSets.lean` | 47 | 1 def, 5 theorems |
| `Orion/GradedOrderCombinatorics/RankGenPoly.lean` | 84 | 1 def, 5 theorems |
| `Orion/GradedOrderCombinatorics/SaturatedChains.lean` | 119 | 0 defs, 7 theorems |
| **Total** | **250** | **2 defs, 16 theorems** |

All files compile cleanly under `lake env lean` with Lean 4 v4.29.0-rc2 and Mathlib. Zero `sorry`, zero `axiom`, zero warnings (after deprecation cleanup).

### Proof Methods

| Method | Count | Notes |
|--------|-------|-------|
| Oracle (run 1) | 7 | First automated weave |
| Manual proof | 3 | `rankGenPoly_coeff`, `rankGenPoly_natDegree`, `saturatedChain_exists` |
| Oracle (run 2, resumed) | 7 | With theme guide, all first-attempt |
| Pre-existing | 1 | `saturatedChain_length` (proved during spec validation) |

### Cost and Time

- Oracle run 1 (10 attempts on hard lemmas): ~$4.30, ~3 hours
- Oracle run 2 (7 entries, budget=1 each): ~$2.50, ~1h 10m
- Manual proofs: ~1 hour human time, $0
- Total automated cost: ~$6.80 for 14 machine-proved lemmas (~$0.49/lemma)

---

## Work Still To Be Done

### Near-Term (Next Iteration)

1. **Library Weaver Walkthrough Document**
   Phase 3 of the AGENTS.md protocol requires a `LIBRARY_WEAVER_WALKTHROUGH.md` covering mental model, call graph, execution lifecycle, critical invariants, and dangerous refactor mistakes. This is the immediate next deliverable.

2. **Parallel Proof Execution**
   The DAG structure reveals which entries are independent and can be proved concurrently. Currently the weaver processes entries sequentially. Adding parallelism (e.g., `asyncio.gather` over independent frontier nodes) could cut wall time by 2-4x for wide DAGs.

3. **Automatic Spec Repair**
   When `saturatedChain_exists` failed, the root cause was a wrong typeclass constraint in the spec (`Preorder` instead of `PartialOrder`). The elaboration checker could feed errors back to the LLM for automatic signature repair, closing the spec-level feedback loop.

4. **Proof Decomposition for Hard Lemmas**
   When the Oracle fails on a hard lemma, the system currently falls back to manual proof. An intermediate strategy: decompose the hard lemma into sub-lemmas, add them to the blueprint, and prove them individually. This trades one hard problem for several easy ones.

### Medium-Term

5. **Pillar 5: Proof Foundry**
   Assemble verified proofs into Mathlib-conformant PRs. This requires style linting, docstring generation, `#check` alignment, and integration with Mathlib's CI pipeline.

6. **Multi-Model Orchestration**
   Use multiple LLMs (Claude, GPT-4o, Gemini) as parallel proof search backends. Different models have different strengths — GPT-4o may handle algebraic manipulation better, while Claude may handle structural induction better. A portfolio strategy could reduce per-lemma failure rates.

7. **Edge Finder → Library Architect Pipeline**
   Currently the handoff between pillar 1 (Edge Finder identifies a pocket) and pillar 3 (Library Architect decomposes it) is manual. Automating this would allow the system to discover and formalize pockets without human intervention.

8. **Cross-Theme Learning**
   Theme guides are currently written per-theme. A meta-learning system could extract generalizable patterns from successful proofs across multiple themes — e.g., "when working with `Finset.sum`, prefer `simp_rw` over `rw` under binders" — and inject them into all future Oracle prompts.

### Long-Term

9. **Deep Retrieval / RAG for Mathlib**
   The Oracle's LeanExplore pre-search is helpful but shallow. It finds declarations by name but does not retrieve proof patterns or usage examples. A deeper RAG system over Mathlib's proof corpus could prevent the API name hallucination problem at its root.

10. **Proof Difficulty Prediction**
    The current difficulty labels ("easy", "medium", "hard") in the blueprint are assigned by the Library Architect LLM and are unreliable. A learned model that predicts proof difficulty from the signature alone could optimize retry budgets — spending more attempts on genuinely hard lemmas and fewer on easy ones.

11. **Formal Verification of the Pipeline Itself**
    The Python orchestrator is the trusted computing base. If it has bugs (like the false positive bug we found), the entire output is suspect. Formally specifying the orchestrator's invariants — or at minimum writing comprehensive property-based tests — would increase confidence in the pipeline's correctness.

---

## Key Architectural Insights

1. **Verification is the only truth.** Agent self-reports, compilation success, and even "no sorry" checks are insufficient individually. The verifier must check the conjunction of all positive and negative conditions.

2. **Theme guides are higher leverage than retry budgets.** A well-written 400-line guide prevented 7 failures. Ten retries without a guide produced 3 failures. The marginal value of *knowledge injection* exceeds the marginal value of *additional attempts*.

3. **Fresh sessions beat persistent context.** Allowing failed context to accumulate causes the LLM to repeat mistakes. A clean slate per retry, combined with a good prompt, is more effective than a long conversation with accumulated errors.

4. **The hardest part is problem formulation, not proof search.** The Oracle failed on `saturatedChain_exists` not because it couldn't find tactics, but because the spec was wrong and the goal structure was ill-posed. Fixing the spec made the proof straightforward.

5. **Two layers are enough.** A dumb orchestrator + a smart-but-untrusted agent + a hard verification gate is a complete architecture. Adding more agent layers increases complexity without proportional capability gain for this problem class.
