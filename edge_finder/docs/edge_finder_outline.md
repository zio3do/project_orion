🪐 Project Orion — Mathlib Edge-Finder Design Brief

🎯 Objective

Design an AI-assisted search and verification system that helps identify underdeveloped but structurally coherent mathematical pockets within Mathlib, suitable for mini-library expansion.

The system must:
	•	Avoid hallucinated gaps.
	•	Use verifiable search mechanisms.
	•	Distinguish between “not found in context” and “truly missing.”
	•	Produce structured candidate pockets with justification.
	•	Support dependency graph sketching.

The goal is reconnaissance and structural mapping — not automatic theorem generation.

⸻

🧠 Core Philosophy
	1.	AI should generate hypotheses.
	2.	Search tools must verify them.
	3.	Results must be structured and inspectable.
	4.	The system must reason at the level of:
	•	abstraction layers
	•	lemma density
	•	namespace structure
	•	missing middle layers

This is architectural reconnaissance, not casual searching.

⸻

🏗 System Architecture Overview

The Edge-Finder should consist of four logical components:

⸻

1️⃣ Concept Generator (Hypothesis Layer)

Purpose:
	•	Given a theme (e.g., combinatorics, finite sums), generate:
	•	key objects
	•	related operators
	•	identity families
	•	abstraction candidates

Output format:
	•	Structured list:
	•	Core primitives
	•	Expected intermediate abstractions
	•	Expected high-level theorems

This step generates “what should exist.”

⸻

2️⃣ Mathlib Verification Layer (Search-Backed)

Purpose:
	•	Check whether the generated objects/abstractions actually exist in Mathlib.

Must use:
	•	Lean LSP search
	•	Semantic search tool (e.g., Leandex)
	•	Grep-based fallback
	•	Namespace inspection

Important rule:
Never trust LLM claims without search confirmation.

Output:
	•	Verified exists
	•	Partially exists (scattered lemmas)
	•	Does not exist
	•	Exists but under different naming

This layer transforms speculation into grounded reality.

⸻

3️⃣ Density & Structure Analyzer

Purpose:
Determine whether the region is:
	•	Fully developed
	•	Primitive-heavy but structurally thin
	•	Deep but lacking intermediate abstraction
	•	Scattered across namespaces

Metrics to consider:
	•	Number of lemmas per namespace
	•	Presence of thematic files
	•	Existence of operator definitions
	•	Coherence of naming patterns
	•	Dependency centrality

Key heuristic:
If primitives exist but no unifying abstraction or operator exists → likely a pocket.

⸻

4️⃣ Pocket Synthesis Module

Purpose:
Produce a candidate mini-library blueprint including:
	•	Proposed abstraction(s)
	•	10–25 candidate lemmas
	•	Dependency DAG sketch
	•	Why it is nontrivial
	•	Why it is not redundant with Mathlib
	•	Risk level

Output must include justification referencing verified search results.

⸻

📐 Design Constraints
	1.	Must avoid hallucinated absence.
	2.	Must log all search queries.
	3.	Must separate:
	•	“not found in current search”
	•	“confirmed absent”
	4.	Must produce inspectable reasoning trace.
	5.	Must prioritize narrow, compositional domains.
	6.	Must avoid areas requiring heavy typeclass machinery.

⸻

🔎 Edge Identification Heuristics

The system should explicitly evaluate:

1️⃣ Middle-Layer Gap
	•	Many primitives exist.
	•	Deep results exist.
	•	But few structural composition lemmas.

2️⃣ Missing Operator Abstraction
	•	Repeated identity pattern.
	•	No defined operator capturing it.

3️⃣ Namespace Fragmentation
	•	Related lemmas scattered across files.

4️⃣ Lack of Thematic File
	•	Concept appears often but no dedicated module.

5️⃣ High Manual Proof Friction
	•	Structured identity families but no automation wrappers.

⸻

🛠 Tooling Considerations

Minimum viable tools:
	•	Lean LSP (for symbol lookup and diagnostics)
	•	Semantic search (e.g., Leandex)
	•	Grep fallback
	•	Claude / GPT for structured reasoning
	•	Controlled tool-calling loop

Important:
The AI must be constrained to:
	•	search
	•	namespace inspection
	•	file reading
	•	summarization

It must not invent.

⸻

🧪 Evaluation Criteria for Candidate Pockets

Each candidate pocket must be scored on:
	1.	Structural coherence
	2.	Confirmed absence of abstraction
	3.	Feasibility within 2 weeks
	4.	Mathematical maturity level
	5.	Alignment with combinatorics / finite sums (user strength)
	6.	Risk of hidden deep dependencies

Output should include risk classification:
	•	Low
	•	Moderate
	•	High

⸻

📊 Logging & Transparency Requirements

The system must log:
	•	All search queries
	•	All namespace scans
	•	All file inspections
	•	Confirmation evidence
	•	Contradictions found

This ensures epistemic robustness.

⸻

🧠 Meta-Level Insight Goal

The Edge-Finder system should ultimately allow the following reflection:
	•	How dense is Mathlib in certain combinatorics subdomains?
	•	Where does abstraction layering break down?
	•	How can AI assist in structural reconnaissance?
	•	What are the limitations of automated gap detection?

This meta-analysis is as important as the chosen pocket.

⸻

⚖️ Risk Considerations

Risks:
	•	False positives due to naming mismatch.
	•	Underestimating deep dependencies.
	•	Selecting domain that is trivial.
	•	Selecting domain that requires heavy upstream machinery.
	•	Overengineering the search tool.

Mitigation:
	•	Manual confirmation pass required before commitment.
	•	Start with small proof-of-concept subset.
	•	Avoid domains touching advanced algebraic hierarchy.

⸻

🚀 Development Phasing Guidance

Phase A:
Build lightweight AI-assisted search wrapper.

Phase B:
Test on 2–3 seed themes.

Phase C:
Select pocket.

Phase D:
Shift focus to library expansion.

Important:
Edge-Finder is reconnaissance infrastructure, not the final deliverable.

⸻

🎯 End-State Vision for Project Orion

Project Orion consists of:
	1.	Edge-Finder (AI reconnaissance tool)
	2.	Oracle (AI-assisted proof accelerator)
	3.	Mini-Library Expansion (primary artifact)
	4.	Structural Analysis + Reflection

The mini-library is the star.
The tools are supporting actors.