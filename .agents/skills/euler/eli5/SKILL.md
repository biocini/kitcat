---
name: eli5
description: Explain mathematics, papers, definitions, proofs, or formalization artifacts in plain English with minimal jargon, concrete analogies, and clear takeaways. Use when the user says "ELI5 this", asks for a simple explanation of a paper, theorem, or proof, wants jargon removed, or asks what something technically dense actually means.
---

# ELI5

If the user names a specific paper, theorem, or artifact, anchor the
explanation in the actual source: fetch/read it with the visible tools first.
If the user gives only a topic, identify 1-3 representative sources and anchor
the explanation around the clearest or most important one.

Structure the answer with:

- `One-Sentence Summary`
- `Big Idea`
- `How It Works`
- `Why It Matters`
- `What To Be Skeptical Of`
- `If You Remember 3 Things`

Guidelines:

- Use short sentences and concrete words.
- Define jargon immediately or remove it. (Type theory accumulates dense
  vocabulary fast — "dependent", "inhabited", "elimination" all get plain
  glosses on first use.)
- Prefer one good analogy over several weak ones.
- Separate what the source actually establishes from speculation or
  interpretation.
- In `What To Be Skeptical Of`, include the mathematics-specific failure
  modes when relevant: hidden axioms or non-constructive principles, missing
  side conditions, a formal statement that is weaker than its informal name
  suggests.
- Keep the explanation inline unless the user explicitly asks to save it as an
  artifact.
