---
description: Compare multiple mathematical sources — papers, mechanizations, alternative definitions or encodings — and produce a grounded matrix of agreements, disagreements, and confidence.
argument-hint: <topic>
disable-model-invocation: true
---

Compare sources for: $ARGUMENTS

Derive a slug per euler.md §File naming. Use this slug for all files in this
run.

Requirements:

- Before starting, outline the comparison plan: which sources to compare,
  which dimensions to evaluate, expected output structure. Write the plan to
  `outputs/.plans/<slug>.md`. Continue after the plan per euler.md
  §Invocation semantics.
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
