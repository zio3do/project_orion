# Numina Lean Agent Design
This is a design summary for a different, but related repo. Some design principles and technical details could be relevant for the system I want to build.

## 1. Overview and Design Philosophy

Numina is a multi-agent orchestration system for Lean theorem proving built around strict process discipline: a single source of truth (BLUEPRINT), explicit status tracking, automatic verification, and forced decomposition when a proof is too complex. The system is intentionally designed to prevent context explosion and to make progress measurable across long-running proof efforts.

Two core ideas show up everywhere:

1. **Orchestrate; do not prove directly.** The coordinator never writes proof code. It only delegates to specialized subagents.
2. **Make progress observable.** Every lemma has a status comment and an explicit attempt budget, and every run is logged.

These constraints are not optional; they are enforced through rules baked into prompts and through the runner’s loop/verification logic.

Key orchestration rules are defined in `prompts/docs/prompts/common.md` and `prompts/docs/prompts/coordinator.md`:

```markdown
## 1. No Axioms Policy

**NEVER use `axiom`. ALWAYS use `sorry` instead.**
...
## 2. Blueprint Synchronization

**BLUEPRINT.md is the SINGLE SOURCE OF TRUTH. Update it immediately after any progress.**
...
```

```markdown
## ⚠️⚠️⚠️ ABSOLUTE RULE: USE SUBAGENTS FOR ALL WORK ⚠️⚠️⚠️

```
┌─────────────────────────────────────────────────────────────────┐
│  YOU ARE FORBIDDEN FROM DOING PROOF WORK DIRECTLY.              │
│                                                                 │
│  ALL work MUST go through Task tool subagents.                  │
│  This is NON-NEGOTIABLE. No exceptions. Ever.                   │
└─────────────────────────────────────────────────────────────────┘
```
```

These constraints are not “nice to have.” They enforce modularity and make it possible to run long sessions without losing coordination or proof quality.

## 2. Required Tech Stack

This system assumes a Lean 4 + Mathlib project, Claude Code (for orchestration), and the lean-lsp-mcp server for Lean tools. The exact setup sequence is documented in `tutorial/setup.md` and is reproduced here verbatim.

```bash
# Install elan
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
# Refresh your shell environment
source ~/.elan/env

# Create Lean project
lake new myproject math && cd myproject
lake update && lake exe cache get && lake build

# Install Claude Code
curl -fsSL https://claude.ai/install.sh | bash

# Install uv
curl -LsSf https://astral.sh/uv/install.sh | sh
# Restart your terminal (or `source ~/.bashrc` / `source ~/.zshrc`, depending on your shell)

# Setup lean-lsp-mcp
git clone https://github.com/project-numina/lean-lsp-mcp ~/lean-lsp-mcp
chmod +x ~/lean-lsp-mcp/numina-lean-mcp.sh

# Add MCP (run from your project directory!)
cd myproject
claude mcp add lean-lsp -- ~/lean-lsp-mcp/numina-lean-mcp.sh

# Verify
claude mcp list
```

Two important operational notes from `tutorial/setup.md` and `tutorial/usage.md`:

- MCP configuration is **directory-scoped**. You must run `claude mcp add ...` from the project directory (or a parent directory) that you’ll use when running the system.
- A one-time Lean build (`lake update`, `lake exe cache get`, `lake build`) is recommended to avoid slow first-run LSP startup.

```markdown
> **MCP Setup (lean-lsp-mcp, required):** MCP configuration is **directory-scoped**. If you plan to run `run_claude` with `--cwd /path/to/project`, you must add the MCP **from that same directory** (or a parent directory):
...
> ```bash
> cd /path/to/project
> claude mcp add lean-lsp -- /absolute/path/to/numina-lean-mcp.sh
> ```
```

## 3. Multi-Agent Architecture

Numina’s architecture is strictly role-based and is orchestrated by a coordinator that delegates to specialized subagents. The system supports three subagents:

- **Blueprint Agent**: Refines and splits complex informal proofs using Gemini.
- **Sketch Agent**: Formalizes informal statements into Lean code with status comments and sorries.
- **Proof Agent**: Attempts to prove formalized lemmas using a structured, multi-method attempt budget.

This is summarized in the workflow diagram (`prompts/docs/technique/WORKFLOW_DIAGRAM.md`):

```markdown
Pattern A: Simple (already formalized)
... Proof Agent ...

Pattern B: Medium (needs formalization)
... Sketch Agent → Proof Agent ...

Pattern C: Complex (needs decomposition)
... Blueprint Agent → Sketch Agent → Proof Agent ...
```

The system distinguishes three levels of complexity and routes tasks accordingly:

```markdown
## High-Level Flow

```
┌─────────────────────────────────────────────────────────────────┐
│                     SESSION START                                │
│                                                                  │
│  1. Read BLUEPRINT.md (single source of truth)                  │
│  2. Find target: partial (resume) or todo (new)                 │
│  3. Check dependencies satisfied (uses field)                   │
│  4. Assess complexity → choose subagent flow                    │
└───────────────────────────┬─────────────────────────────────────┘
```
```

## 4. The Coordinator

The coordinator is the only agent that runs persistently. It reads BLUEPRINT, selects targets, spawns subagents, and synchronizes results. It is explicitly forbidden from doing proof work directly.

From `prompts/docs/prompts/coordinator.md`:

```markdown
## ⚠️⚠️⚠️ ABSOLUTE RULE: USE SUBAGENTS FOR ALL WORK ⚠️⚠️⚠️
...
**If you catch yourself doing ANY of these, STOP IMMEDIATELY:**
- Reading a .lean file to attempt proof fixes
- Using Lean tools for proof attempts
- Trying tactics and checking results
- Making any edits beyond BLUEPRINT updates
```

Selection and orchestration rules are fully spelled out, including dependency checks and orchestration patterns. The coordinator also contains Task tool templates that define how to invoke each subagent. Example (abbreviated) from the file:

```markdown
#### Flow A: Simple → Proof Agent
... (Task tool call template) ...

#### Flow B: Medium → Sketch Agent → Proof Agent
... (Task tool call template) ...

#### Flow C: Complex → Blueprint Agent → Sketch → Proof
... (Task tool call template) ...
```

These templates are operational instructions rather than just suggestions; they are the default routing patterns used to keep the system consistent.

## 5. Blueprint as Single Source of Truth

BLUEPRINT.md is a structured knowledge base that captures all planned statements, dependencies, proof status, attempt budgets, and file locations. The coordinator and subagents all synchronize through this document.

The blueprint format is defined in `prompts/docs/prompts/coordinator.md` and `prompts/docs/technique/WORKFLOW_DIAGRAM.md`:

```markdown
# [type] [label]

## meta
- **label**: [label]
- **uses**: [[dep1], [dep2], ...]
- **file**: `path:line` or (to be created)
- **status**: done | partial | todo
- **attempts**: N / M (if applicable)

## statement
[Informal statement]

## proof
[Informal proof - detailed for lemmas/theorems]
```

And the mandatory synchronization rule (from `prompts/docs/prompts/common.md`):

```markdown
## 2. Blueprint Synchronization

**BLUEPRINT.md is the SINGLE SOURCE OF TRUTH. Update it immediately after any progress.**
...
```

This “single source of truth” design prevents drift between what has been proven, what is still open, and what subagents are currently working on.

## 6. Blueprint Agent

The blueprint agent refines informal proofs, calls Gemini for detail, and splits lemmas when proofs are too complex. It is invoked for complex or exhausted targets.

From `prompts/docs/prompts/blueprint_agent.md`:

```markdown
## Your Mission

You are the Blueprint Agent. Your job is to:
1. **Analyze lemma complexity** - determine if lemmas need splitting or refinement
2. **Call Gemini** - get detailed informal proofs with step-by-step reasoning
3. **Split complex lemmas** - break into sub-lemmas when proof has 3+ distinct steps
4. **Update blueprint** - add sub-lemmas, update dependencies, fill informal proofs
5. **Create agent log** - document full Gemini interaction and decisions
```

Splitting is triggered if the Gemini-produced proof has 3+ distinct steps:

```markdown
### Step 3: Decide on Splitting

**Splitting Criteria:**
- If Gemini's proof has **3 or more distinct steps** → SPLIT
- If each step requires different techniques → SPLIT
- If proof is >20 lines informal → SPLIT
```

The blueprint agent uses explicit Gemini calls with structured templates. Example query template:

```markdown
I need a detailed informal proof for the following lemma:

**Statement**: [informal statement from blueprint]

**Context**:
- Available definitions: [list from 'uses' field]
- Available lemmas: [list from 'uses' field]

Please provide:
1. A detailed step-by-step informal proof
2. Break down into logical steps (each step should be provable independently)
3. For each step, explain the reasoning clearly
4. Identify any sub-lemmas that should be proven separately
```

This yields a detailed blueprint entry and, if needed, a new dependency graph of sub-lemmas.

## 7. Sketch Agent

The sketch agent formalizes informal statements into Lean code, adds status comments, and verifies compilation. It never proves the statement; it leaves `sorry` for proofs.

From `prompts/docs/prompts/sketch_agent.md`:

```markdown
## Your Mission

You are the Sketch Agent. Your job is to:
1. **Read informal statements** from blueprint
2. **Formalize statements** into Lean code
3. **Add status comments** with proper format
4. **Leave proofs as sorry** (proof agent will fill them)
5. **Note tmp file location** for future proof work
6. **Update blueprint** with file:line references
```

The agent must ensure the informal proof is detailed enough before formalizing. If it is insufficient, it must consult Gemini or report the need for splitting.

```markdown
### Step 1.5: Verify Informal Proof Quality (CRITICAL)
...
**If informal proof is insufficient**:

**Use `gemini_informal_prover` to get detailed proof:**
...
```

The status comment format comes from `prompts/docs/prompts/common.md` and is enforced uniformly:

```lean
/- (by claude)
State: ❌ todo
Priority: 1
Attempts: 0 / 20
tmp file:
-/
lemma base_case : f 0 = 1 := sorry
```

## 8. Proof Agent

The proof agent is the most structured and restrictive role. It uses a fixed attempt budget, mandatory Gemini checkpoints, and a five-category proof exploration strategy. It must work in temporary files, and it must ensure Lean code compiles at all times.

From `prompts/docs/prompts/proof_agent.md`:

```markdown
## CRITICAL: Mandatory Gemini Consultation at Start

```
┌─────────────────────────────────────────────────────────────────┐
│  BEFORE WRITING ANY LEAN CODE, YOU MUST CONSULT GEMINI FIRST!   │
│                                                                 │
│  Use: discussion_partner or gemini_informal_prover              │
└─────────────────────────────────────────────────────────────────┘
```
```

Attempt budgets and category requirements are explicit:

```markdown
## Attempt Budget System (CRITICAL)

| Proof Size | Min Attempts | Categories Required |
|------------|--------------|---------------------|
| <5 lines   | 20 attempts  | 3 method types |
| 5-20 lines | 35 attempts  | 4 method types |
| >20 lines  | 50 attempts  | 5 method types |
```

Mandatory Gemini checkpoints are also hard-coded:

```markdown
## Gemini Progressive Strategy (MANDATORY Checkpoints)

Checkpoint 0: BEFORE ANY CODE
Checkpoint 2: After 2 attempts
Checkpoint 4: After 4 attempts
Checkpoint 8: After 8 attempts
Checkpoint 16: After 16 attempts
Checkpoint 32: After 32 attempts
```

The proof agent must use specific Gemini tools, each with a specific role:

- `discussion_partner`: high-level strategy and targeted hints
- `gemini_informal_prover`: detailed mathematical breakdowns and decomposition ideas
- `gemini_code_golf`: simplification/optimization of partially working proofs

These names are explicitly required in `prompts/docs/prompts/proof_agent.md`:

```markdown
**Use**: `discussion_partner` or `gemini_informal_prover`
...
**Use**: `gemini_code_golf` or `discussion_partner`
```

The agent also follows a strict temporary file workflow to avoid polluting original files. From `prompts/docs/prompts/common.md` and `prompts/docs/prompts/proof_agent.md`:

```markdown
## CRITICAL: Temporary File Workflow

**DO NOT work directly in the original file. Use temporary files.**
...
Step 1: Note tmp file in original (FIRST!)
Step 2: Create tmp file
Step 3: Work in tmp file
Step 4: Copy back when proven
Step 5: Delete tmp file
```

## 9. Verification Gate

The system enforces verification at completion using a callback inside the runner. This callback uses `lake env lean` over files discovered by project context and can optionally ignore `sorry` depending on configuration.

The verification pipeline is in `scripts/runner.py` and `scripts/lean_checker.py`.

Condensed excerpt: the completion callback is built inside `run_task` and passed to the session loop:

```python
        def on_complete_callback() -> bool:
            if not task.check_after_complete:
                return True

            check_path = task.get_check_path()

            # Determine files to check based on task_type
            if task.task_type == "file":
                lean_files = [check_path] if check_path.suffix == ".lean" else []
            else:
                lean_files = find_lean_files(check_path)

            if not lean_files:
                return True

            print(f"[info] Verifying {len(lean_files)} .lean files...")
            results = check_lean_files_parallel(lean_files)

            # Filter errors based on allow_sorry setting
            if task.allow_sorry:
                errors = [f for f, e, _, _, _ in results if e]
                print(f"[info] allow_sorry=True, ignoring sorry warnings")
            else:
                errors = [f for f, e, s, _, _ in results if e or s]

            if errors:
                print(f"\n[error] {len(errors)} files have errors{'' if task.allow_sorry else '/sorry'}:")
                for f in errors:
                    print(f"  - {f}")
                return False

            print(f"[info] All {len(lean_files)} files verified successfully!")
            return True
```

The underlying Lean checking logic uses `lake env lean` and parallelism (`scripts/lean_checker.py`):

```python
def check_lean_file(file_path: Path) -> Tuple[bool, bool, str, str]:
    ...
    result = subprocess.run(
        ["lake", "env", "lean", str(file_path)],
        capture_output=True,
        text=True,
        timeout=60,
        cwd=str(project_root),
    )
    ...
    has_error = (
        "error" in stdout.lower()
        or "error" in stderr.lower()
        or result.returncode != 0
    )
    has_sorry_warning = "sorry" in stdout.lower() or "sorry" in stderr.lower()
    return has_error, has_sorry_warning, stdout, stderr
```

This gate is invoked when the session receives a `COMPLETE` signal from the model. If verification fails, the runner resends the original prompt.

## 10. Python Runner Infrastructure

The runner provides the session loop, end-reason parsing, auto-continue logic, optional git commits, per-round logging, and result serialization. It is split across `scripts/runner.py`, `scripts/task.py`, and `scripts/run_claude.py`.

### 10.1 Task Metadata and Config

Task parameters are defined by `TaskMetadata` (`scripts/task.py`):

```python
@dataclass
class TaskMetadata:
    task_type: Literal["file", "folder"]
    target_path: str | Path
    prompt: Optional[str] = None
    prompt_file: Optional[str | Path] = None
    cwd: Optional[str | Path] = None
    max_rounds: int = 20
    check_after_complete: bool = True
    allow_sorry: bool = False
    sleep_between_rounds: float = 1.0
    result_dir: Optional[str | Path] = None
    mcp_log_dir: Optional[str | Path] = None
    mcp_log_name: Optional[str] = None
    permission_mode: str = "bypassPermissions"
    output_format: Optional[str] = None
    track_statements: bool = True
    on_statement_change: Literal["error", "warn"] = "warn"
    git_commit: bool = False
```

The `TaskMetadata` object builds prompts by prepending the target path and builds a full environment with MCP log configuration:

```python
    def get_prompt(self) -> str:
        ...
        target_type = "file" if self.task_type == "file" else "folder"
        target_info = f"The target {target_type} is: {self.target_path}\n\n"
        return target_info + base_prompt

    def build_env(self) -> dict:
        env = os.environ.copy()
        if self.mcp_log_dir:
            Path(self.mcp_log_dir).mkdir(parents=True, exist_ok=True)
            env["MCP_LOG_DIR"] = str(self.mcp_log_dir)
        if self.mcp_log_name:
            env["MCP_LOG_NAME"] = self.mcp_log_name
        return env
```

Defaults inheritance is handled in configuration files, as documented in `tutorial/usage.md`:

```markdown
The `defaults` section in the config file defines default values for all tasks. Each task inherits from defaults and can override any parameter.

Final config = defaults + task (task takes priority)
```

### 10.2 Session Loop and End Reasons

The session loop is in `run_claude_session` (`scripts/runner.py`). It repeatedly calls Claude, watches for an `END_REASON` sentinel in stdout, and continues as needed. The sentinel is defined by a regex and parsed from output:

```python
PAT_REASON = re.compile(r"(?m)^\s*END_REASON:(LIMIT|COMPLETE|SELECTED_TARGET_COMPLETE)\s*$", re.I)

...
    m = PAT_REASON.search(out)
    reason = m.group(1).upper() if m else None
```

The loop sends an initial prompt, and then either continues the session, resets, or resends the prompt based on state. Condensed excerpts:

```python
stdout, reason, returncode = run_claude_once(base + [prompt], env=env, cwd=cwd)
...
while reason == "LIMIT" or reason is None or reason == "COMPLETE" or reason == "SELECTED_TARGET_COMPLETE":
    ...
    if reason == "COMPLETE":
        if on_complete:
            if on_complete():
                break
            else:
                # Verification failed, resend prompt
                stdout, reason, returncode = run_claude_once(base + [prompt], env=env, cwd=cwd)
                ...
                continue
        else:
            break
    ...
    if reason is None:
        stdout, reason, returncode = run_claude_once(base + [prompt], env=env, cwd=cwd)
    elif should_reset_session:
        stdout, reason, returncode = run_claude_once(base + [prompt], env=env, cwd=cwd)
    else:
        cmd = ["claude", "-c", "-p"]
        ...
        stdout, reason, returncode = run_claude_once(cmd + ["continue"], env=env, cwd=cwd)
```

The runner also supports optional git commits and immediate per-round result serialization. These features are activated via `TaskMetadata` settings (`git_commit`, `result_dir`).

### 10.3 CLI Entry Points

The CLI is documented in `tutorial/usage.md`, and it supports three commands: `run`, `batch`, `from-folder`.

```markdown
python -m scripts.run_claude <command> [options]

Three commands are supported:
- `run` - Run a single task
- `batch` - Run batch tasks from a config file
- `from-folder` - Scan a folder for .lean files and run tasks
```

Config examples are included, including `config/config_minif2f.yaml` which shows defaults inheritance and per-task overrides:

```yaml
defaults:
  task_type: file
  prompt_file: prompts/prompt_complete_file.txt
  cwd: .
  check_after_complete: true
  permission_mode: bypassPermissions
  result_dir: results/minif2f
  mcp_log_dir: mcp_logs/minif2f
  max_rounds: 2

tasks:
  - target_path: leanproblems/Minif2f/algebra_sqineq_2atp2bpge2ab.lean
    mcp_log_name: algebra_sqineq_2atp2bpge2ab
  - target_path: leanproblems/Minif2f/imo_1964_p1.lean
    mcp_log_name: imo_1964_p1
    max_rounds: 5
```

## 11. MCP Integration and Observability

Numina relies on lean-lsp-mcp for Lean tooling. It also logs and analyzes MCP tool usage via `scripts/mcp_stats.py`.

The environment wiring is performed in `TaskMetadata.build_env` (shown earlier) and `scripts/runner.py` obtains the log path using `get_mcp_log_path`:

```python
def get_mcp_log_path(
    mcp_log_name: Optional[str] = None,
    mcp_log_dir: Optional[str | Path] = None,
) -> Optional[Path]:
    base_path = Path(mcp_log_dir) if mcp_log_dir else Path("~/.lean_lsp_mcp").expanduser()
    log_name = f"{mcp_log_name}.log" if mcp_log_name else "mcp_lean_lsp.log"
    return base_path / log_name
```

MCP logs are parsed to count tool calls and failures. `scripts/mcp_stats.py` shows the mechanism:

```python
tool_pat = re.compile(r"🔧 Tool:")
tool_name_same_line = re.compile(r"🔧 Tool:\s*([a-zA-Z_]\w*)\(")
tool_name_next_line = re.compile(r"^\s*([a-zA-Z_]\w*)\(")
result_pat = re.compile(r"^\s*(✅|❌)")
warn_pat = re.compile(r"⚠️|❌")

stats = defaultdict(lambda: {"total": 0, "ok": 0, "fail": 0})
```

And the results are written to JSON:

```python
summary = {
    "by_tool": {k: dict(v) for k, v in stats.items()},
    "total": {"total": total_ok + total_fail, "ok": total_ok, "fail": total_fail},
}
json_file = out_path / "mcp_stats.json"
```

This gives immediate observability into which Lean tools were used and where failures occurred.

## 12. Statement Tracking

The system includes optional “statement change” tracking to ensure that theorems/lemmas are not silently edited during proof attempts. This is implemented in `scripts/statement_tracker.py` and `scripts/extract_sublemmas.py`.

Statement extraction uses `LeanCodeParser` to parse theorem/lemma blocks and pull out statements without proofs:

```python
def extract_statements_from_file(file_path: Path) -> Dict[str, str]:
    ...
    code = file_path.read_text(encoding="utf-8")
    parser = LeanCodeParser(code)
    blocks = parser.extract_all_blocks(keys=["theorem", "lemma"], allow_overlap=False)

    statements = {}
    for block in blocks:
        name = block["info"]["name"]
        statement = block["info"]["statement"]
        if name:
            statements[name] = statement
    return statements
```

The `StatementTracker` snapshots initial statements and compares them later:

```python
class StatementTracker:
    def __init__(self, files: List[Path]):
        self.files = [Path(f).resolve() for f in files]
        self.initial_snapshots: Dict[Path, Dict[str, str]] = {}
        self._capture_initial()

    def check(self) -> List[StatementChange]:
        ...
        for f in self.files:
            initial = self.initial_snapshots.get(f, {})
            current = extract_statements_from_file(f)
            ...
            if orig_norm != curr_norm:
                ...
                changes.append(StatementChange(...))
```

In `run_claude_session`, the tracker is consulted each round and can optionally stop the session when statements change:

```python
changes = tracker.check() if tracker else []
...
if changes:
    if on_statement_change == "error":
        print(f"\n[error] Statement changed in round {round_num}! Stopping.")
        statement_error = True
    else:
        print(f"\n[warn] Statement changed in round {round_num}:")
```

This is a guardrail to prevent silent changes in theorem statements while proof work is ongoing.

## 13. Key Design Decisions and Tradeoffs

This section explains why the system looks the way it does, and what tradeoffs it embraces.

1. **Strict orchestration-only coordinator**
   - Rationale: Coordinators can easily blow up context if they attempt proof work. Forcing all proof work into subagents isolates context, simplifies review, and makes logs reliable.
   - Tradeoff: You lose immediate “manual intervention” in the coordinator, so small fixes are slower. The system accepts this cost in exchange for robustness at scale.

2. **BLUEPRINT as a single source of truth**
   - Rationale: A single global state prevents drift between multiple agents and sessions. It also makes progress measurable and ensures handoffs are consistent.
   - Tradeoff: Requires strict discipline and constant updates. The system explicitly enforces this to avoid latent inconsistency.

3. **Attempt budgets and category requirements**
   - Rationale: Structured attempts encourage breadth and discourage premature failure. It forces the proof agent to exhaust multiple approaches instead of giving up after a few tactics.
   - Tradeoff: More attempts means more runtime and longer logs. The system trades speed for completeness and reproducibility.

4. **Mandatory Gemini checkpoints with named tools**
   - Rationale: The system treats a second LLM as a strategic advisor. Explicit checkpointing ensures that proof exploration doesn’t get stuck in a single unproductive tactic.
   - Tradeoff: Requires additional infrastructure and tool wiring (MCP to Gemini). The payoff is higher success rate and better proof quality.

5. **Temporary file workflow**
   - Rationale: Proof attempts can be messy. Working in tmp files preserves original files, avoids partial edits, and makes it clear when a lemma is “in progress.”
   - Tradeoff: More file management overhead. The system considers that acceptable to preserve code cleanliness and avoid accidental corruption.

6. **Verification gate via `lake env lean`**
   - Rationale: Running Lean on the exact file(s) avoids hidden inconsistencies and ensures that “COMPLETE” from the model is actually valid. It also supports optional “allow_sorry” modes.
   - Tradeoff: Verification adds latency. The system accepts this to prevent false positives.

7. **Statement tracking and change detection**
   - Rationale: Proof agents can inadvertently modify statements to make proofs easier. Tracking prevents this kind of silent regression and makes lemma integrity explicit.
   - Tradeoff: Extra parsing and processing per round. This is a deliberate guardrail for long runs.

These design decisions are oriented around correctness, reproducibility, and long-session stability rather than short-term speed.

## 14. Starter Checklist

This checklist outlines the minimal steps to set up and run the system end-to-end.

1. **Install and set up Lean + Mathlib**
   - Follow the `tutorial/setup.md` steps (elan, lake project, cache build).

2. **Install Claude Code and lean-lsp-mcp**
   - Run `claude mcp add ...` from your project directory.
   - Verify with `claude mcp list`.

3. **Install lean4-skills (inside Claude Code)**
   - `/plugin marketplace add cameronfreer/lean4-skills`
   - `/plugin install lean4-theorem-proving`

4. **Create or update BLUEPRINT.md**
   - Use the blueprint format described in Section 5.
   - Ensure `status`, `uses`, and `file` fields are correct.

5. **Choose a run mode**
   - Single task: `python -m scripts.run_claude run <target> ...`
   - Batch: `python -m scripts.run_claude batch <config_file>`
   - Folder scan: `python -m scripts.run_claude from-folder <folder>`

6. **Verify outputs**
   - Check `results/` for per-round JSON (if enabled).
   - Check `mcp_logs/` and `mcp_stats.json` for tool usage.
   - Ensure BLUEPRINT has been updated after each subagent run.

7. **Iterate**
   - Use the coordinator to select the next target and spawn agents in the correct order.
   - If a lemma is too complex or exhausted, route it through the blueprint agent for splitting.

With these steps completed, you can run the system continuously and safely scale to large proof collections.
