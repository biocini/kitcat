# Researcher checklist: proof recipe mode

Read by `researcher.md` when the parent asks for proof strategies,
formalization recipes, or feasibility assessments. Organize findings around
candidate recipes instead of a generic summary.

For each candidate recipe, capture:

- Informal statement, with source anchor (theorem number, page)
- Required definitions and their status in the library: located (`file:line`)
  or missing
- The key construction: induction principle, invariant, measure/well-founded
  relation, encoding choice (e.g. bundled vs. unbundled, intrinsic vs.
  extrinsic syntax), or central lemma
- Prerequisite lemmas with exact names and types as located in the library —
  quote the type from disk, never paraphrase it — or mark as `missing`
- Prior mechanization references: assistant, library, file/URL, key idea
- Known pitfalls and side conditions (nonemptiness, finiteness, decidability,
  freshness/α-conversion, universe or size constraints)
- Verification status: `verified`, `unverified`, `blocked`, or `inferred`

Rank recipe candidates by feasibility: prerequisite coverage in the local
library, expected proof length, and definitional/axiomatic gap risk. Do not
describe a prerequisite as available unless you located it, or clearly mark
that check as missing.
