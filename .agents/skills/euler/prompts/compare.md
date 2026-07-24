---
description: Compare multiple mathematical sources — papers, mechanizations, alternative definitions or encodings — and produce a grounded matrix of agreements, disagreements, and confidence.
args: <topic>
section: Research Workflows
topLevelCli: true
---
## Tool Discipline (Read First)

Tool names are literal. Use only tools visible in the current tool set.

- Web search and fetch: use the visible search/fetch tools; do not invent names
  like `google_search`, `WebSearch`, or `search_google`.
- Library search: use shell (`rg`, `grep`, `find`) or any visible
  LSP/navigation tools over the host library.
- To ask the user a question, write plain chat text and wait for the next user
  message, unless a visible user-question tool exists. Do not invent one.
- Do not use `Task` as an agent dispatcher. Use only the visible subagent tool
  when it exists.
- If a tool returns `Tool not found` or `Invalid URL`, do not retry the same
  invalid call. Map to a canonical visible tool and valid arguments, or record
  the capability as blocked.

Compare sources for: $@

Derive a short slug from the comparison topic (lowercase, hyphens, no filler
words, ≤5 words). Use this slug for all files in this run.

Requirements:

- Before starting, outline the comparison plan: which sources to compare,
  which dimensions to evaluate, expected output structure. Write the plan to
  `outputs/.plans/<slug>.md`. Briefly summarize the plan to the user and
  continue immediately. Do not ask for confirmation or wait for a proceed
  response unless the user explicitly requested plan review.
- Use the `researcher` subagent to gather source material when the comparison
  set is broad, and the `verifier` subagent to verify anchors and add inline
  citations to the final matrix.
- Build a comparison matrix covering: source (with anchor), key claim,
  formulation strength (hypotheses, conclusion, side conditions), evidence
  type (informal proof / mechanized / expository), caveats, confidence.
- When comparing encodings or definitions (e.g. bundled vs. unbundled,
  intrinsic vs. extrinsic, different equality notions), add an explicit
  dimension for what the choice changes about the meaning of downstream
  theorems — that is usually the real question.
- When "the same theorem" appears in multiple sources, check whether the
  formulations are actually equivalent. Non-equivalent formulations are a
  finding, not a nuisance: record exactly how hypotheses or conclusions
  differ.
- Generate charts only when a chart tool is visible and the comparison
  involves quantitative data; otherwise include a chart specification or
  source-backed table. Use Mermaid for concept or dependency comparisons when
  the structure is source-supported.
- Distinguish agreement, disagreement, and uncertainty clearly.
- Save exactly one comparison to `outputs/<slug>-comparison.md`.
- End with a `Sources` section containing direct anchors (URLs, file paths,
  theorem numbers) for every source used.
