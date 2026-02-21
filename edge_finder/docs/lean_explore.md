# LeanExplore MCP Server for AI Agents

I feel that LeanExplore could serve as a useful tool, and so I wanted to include some details about the MCP here for reference.


## Exposed Tools

The server exposes two tools. Both return declarations as SearchResult objects with the following fields:

id: integer — Unique identifier of the declaration.
name: string — Fully qualified Lean name (e.g., "Nat.add").
module: string — Module path (e.g., "Mathlib.Data.List.Basic").
docstring: string | null — Documentation string, if available.
source_text: string — The Lean source code of the declaration.
source_link: string — GitHub URL to the source code.
dependencies: string | null — JSON array of dependency names.
informalization: string | null — Natural language description, if available.


### Tool: search
Purpose: Find Lean declarations by natural language query.
Parameters:
query: string (required) — The search query (e.g., "continuous function").
limit: integer (optional, default: 10) — Maximum number of results.
packages: string[] (optional) — Filter by package names (e.g., ["Mathlib", "Std"]).
Returns: An object with:
query: string — The original query.
results: SearchResult[] — List of matching declarations.
count: integer — Number of results returned.
processing_time_ms: integer — Processing time in milliseconds.


### Tool: get_by_id
Purpose: Retrieve a specific declaration by its ID.
Parameters:
declaration_id: integer (required) — The declaration's unique ID.
Returns: A SearchResult object, or null if not found.
Example workflow: An agent uses search to find declarations related to a concept (e.g., "Frobenius homomorphism"), picks a relevant result, then calls get_by_id to retrieve the full source code and details.