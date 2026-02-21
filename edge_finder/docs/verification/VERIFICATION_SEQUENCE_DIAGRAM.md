# Verification Layer — Sequence Diagram

*Two-pass verification flow including the Iteration 5 concept re-mapping step.*

The diagram below shows one complete pipeline run from concept generation to the final
`VerificationReport`. The verification layer's scope is the shaded region between
**theme-level search** and **density analysis**.

---

## Full pipeline sequence (verification layer highlighted)

```mermaid
sequenceDiagram
    participant CLI as cli.main()
    participant CG as Concept Generator<br/>(Module 1)
    participant LE as LeanExplore API
    participant RM as Concept Remapper<br/>(Iteration 5)
    participant VL as Verification Layer<br/>(Module 2)
    participant OA as OpenAI API

    CLI->>CG: generate_concepts(theme, model)
    CG->>OA: prompt: generate structured concept list
    OA-->>CG: JSON with primitives / operators / identity_families / search_queries
    CG-->>CLI: concepts dict

    CLI->>LE: search_queries(search_queries)
    note over LE: sequential, one call per query<br/>retry on 5xx (2 retries, 1s/2s backoff)
    LE-->>CLI: list[SearchResponse] (theme-level)

    CLI->>CLI: log_search_response() × N

    rect rgb(230, 245, 255)
        note over CLI,VL: Verification Layer scope

        alt --skip-remap not set AND not dry-run
            CLI->>RM: remap_concepts(concepts, responses, model)
            RM->>RM: extract unique declaration names<br/>from search results (up to 2000)
            RM->>OA: prompt: match each concept to best Mathlib name
            OA-->>RM: remapped primitives / operators / identity_families + mapping log
            RM->>RM: replace "null" strings with original names
            RM-->>CLI: (concepts_for_verification, remap_log)
            CLI->>CLI: write concepts_remapped.json + remap_log.json
        else skip or dry-run
            CLI->>CLI: concepts_for_verification = original concepts
        end

        CLI->>VL: verify_concepts(concepts_for_verification, responses)
        note over VL: Pass 1 — theme-level

        VL->>VL: extract_concepts()<br/>→ list[(name, ConceptKind)]
        VL->>VL: flatten + deduplicate results<br/>by declaration_id
        loop for each concept
            VL->>VL: _find_matches(concept, unique_results)
            note right of VL: exact → qualified_suffix →<br/>substring → informalization
            VL->>VL: _classify_status(matches)<br/>→ verified / partial / absent / name_mismatch
        end
        VL-->>CLI: initial VerificationReport

        alt --skip-targeted-search not set
            CLI->>VL: refine_verification(initial_report, concepts_for_verification, search_fn)
            note over VL: Pass 2 — targeted

            loop for each entry where status is absent or partial
                VL->>VL: generate_targeted_queries(concept, candidate_namespaces)
                note right of VL: bare name + namespace-prefixed variants<br/>+ space-separated semantic variant<br/>(deterministic, no LLM)
                loop for each targeted query
                    VL->>LE: await search_fn(query) → search_single()
                    note over LE: retry on 5xx (2 retries, 1s/2s backoff)
                    LE-->>VL: SearchResponse
                end
                VL->>VL: deduplicate targeted results by declaration_id
                VL->>VL: _find_matches(concept, unique_targeted)
                VL->>VL: merge with original matches<br/>(deduplicate by result_name)
                VL->>VL: _classify_status(combined_matches)
                note right of VL: may upgrade absent → verified<br/>or partial → verified
            end
            VL-->>CLI: (refined VerificationReport, new_responses)
            CLI->>CLI: log_search_response() for each new response
        end

        CLI->>CLI: write verification.json

    end

    CLI->>CLI: compute_density_report(all_responses)
    CLI->>CLI: classify_gaps(density_report, verification_report, all_responses)
    note over CLI: coverage_ratio from VerificationReport<br/>is the sole gap signal
```

---

## Pass 1 detail: matching heuristics

```mermaid
flowchart TD
    A[concept name] --> B{norm_name == norm_concept?}
    B -- yes --> C[exact match\nMatchEvidence type=exact]
    B -- no --> D{norm_name ends with\n.norm_concept?}
    D -- yes --> E[qualified suffix match\nMatchEvidence type=qualified_suffix]
    D -- no --> F{norm_concept in norm_name?}
    F -- yes --> G[substring match\nMatchEvidence type=substring]
    F -- no --> H{norm_concept in\ninformalization or docstring?}
    H -- yes --> I[informalization match\nMatchEvidence type=informalization]
    H -- no --> J[no match for this result]

    C --> K[_classify_status]
    E --> K
    G --> K
    I --> K
    J --> K

    K --> L{any exact or\nqualified_suffix?}
    L -- yes --> M[VERIFIED]
    L -- no --> N{any substring?}
    N -- yes --> O[PARTIAL]
    N -- no --> P{any informalization?}
    P -- yes --> Q[NAME_MISMATCH]
    P -- no --> R[ABSENT]
```

---

## Pass 2 detail: targeted query generation

```mermaid
flowchart LR
    A[concept name\ne.g. sum_add_distrib] --> B{is qualified?\ncontains dot?}

    B -- no --> C[1 bare name\nsum_add_distrib]
    B -- yes --> C2[1 bare name\ne.g. MonoidHom.comp]

    B -- no --> D[top-level candidate namespaces\nexclude sub-namespaces with dot\nexclude self-prefixing]
    D --> E[namespace-prefixed variants\nFinset.sum_add_distrib\nBigOperators.sum_add_distrib]

    A --> F{contains underscore?}
    F -- yes --> G[space-separated variant\nsum add distrib]
    F -- no --> H[skip]

    C --> I[deduplicate by lowercase]
    C2 --> I
    E --> I
    G --> I
    H --> I

    I --> J[1–5 targeted queries]
```

---

## Status transitions across passes

```mermaid
stateDiagram-v2
    [*] --> absent : pass 1 — no match found
    [*] --> partial : pass 1 — substring match only
    [*] --> verified : pass 1 — exact or qualified_suffix match
    [*] --> name_mismatch : pass 1 — informalization match only

    absent --> verified : pass 2 — targeted query finds exact/suffix match
    absent --> partial : pass 2 — targeted query finds substring only
    absent --> name_mismatch : pass 2 — targeted query finds informalization only
    absent --> absent : pass 2 — no targeted results match

    partial --> verified : pass 2 — targeted query finds exact/suffix match
    partial --> partial : pass 2 — no stronger match found

    verified --> verified : pass 2 skipped (already resolved)
    name_mismatch --> name_mismatch : pass 2 skipped (already resolved)
```

---

## Coverage ratio formula

The `coverage_ratio` property on `VerificationReport` is the number consumed by the gap
classifier as its sole gap signal:

```
coverage_ratio = (verified_count + partial_count) / total_count
```

`name_mismatch` counts as found (the concept exists, just under a different name).
`absent` is the only status that reduces coverage.

Gap thresholds (calibrated from Iteration 4 data, 6 themes):

| Coverage | Confidence |
|---|---|
| < 0.3 | `high` gap |
| < 0.5 | `moderate` gap |
| < 0.7 | `low` gap |
| ≥ 0.7 | `well_covered` (no gap) |

If search coverage (fraction of queries returning any results) < 0.7, confidence is downgraded
one tier — API failures make absence unreliable.
