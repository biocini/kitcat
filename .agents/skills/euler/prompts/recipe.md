---
description: Find ranked, implementable proof strategies for a theorem or formalization goal, backed by literature, prior mechanizations, and the actual contents of the local library.
args: <theorem-or-goal>
section: Formalization Workflows
topLevelCli: true
---
## Tool Discipline (Read First)

Tool names are literal. Use only tools visible in the current tool set.

- Web search and fetch: use the visible search/fetch tools; do not invent names
  like `google_search`, `WebSearch`, or `search_google`.
- Library search: use shell (`rg`, `grep`, `find`) or any visible
  LSP/navigation tools over the toolchain block's `search-dirs`.
- The proof checker runs via shell using the project's check command. Never
  simulate, predict, or assume a check result; only a recorded run counts.
- To ask the user a question, write plain chat text and wait for the next user
  message, unless a visible user-question tool exists. Do not invent one.
- Do not use `Task` as an agent dispatcher. Use only the visible subagent tool
  when it exists.
- If a tool returns `Tool not found` or `Invalid URL`, do not retry the same
  invalid call. Map to a canonical visible tool and valid arguments, or record
  the capability as blocked.

Find implementable proof strategies for: $@

Derive a short slug from the target (lowercase, hyphens, no filler words,
≤5 words). Use this slug for all files in this run.

This is an execution request, not a request to explain the workflow. Continue
immediately.

A proof recipe links a target theorem to the exact strategy that should
discharge it in this library: the key construction, the prerequisite lemmas
that must exist, and the prior mechanizations that show the route is feasible.
Recipes start from evidence of feasibility, not from wishful outlines.

## Required artifacts

- `outputs/.plans/<slug>-recipe.md`
- `outputs/.drafts/<slug>-recipe-research.md`
- `outputs/<slug>-recipe.md`
- `outputs/<slug>-recipe.provenance.md`

## Workflow

1. **Plan** — Write `outputs/.plans/<slug>-recipe.md` with the target
   statement (as given, flagged if it is a paraphrase), candidate source
   types, feasibility constraints, and a task ledger. Continue automatically
   after writing the plan.
2. **Research** — Use the `researcher` subagent when the target needs a broad
   literature/mechanization sweep; for narrow targets, gather evidence
   directly. The research must cover both directions: informal routes (how the
   literature proves this) and mechanized routes (how existing libraries in
   any proof assistant proved this), plus the local library survey.
3. **Strategy extraction** — For each promising approach, link the target to
   the exact recipe that should discharge it. A useful entry has: informal
   statement with anchor; required definitions (located or missing); the key
   construction (induction principle, invariant, measure, encoding choice);
   prerequisite lemmas; prior mechanization reference; known pitfalls.
4. **Prerequisite validation** — For each candidate, check whether every
   prerequisite lemma already exists in the local library: locate it with
   search tooling and quote its actual type from disk with `file:line`. An
   unlocated prerequisite is a gap the recipe must budget for (as a lemma to
   prove), never an assumption. If a prerequisite's type was not directly
   quoted, mark it `unverified`; do not imply it matches.
5. **Implementation grounding** — For the top candidate, sketch the concrete
   path in the host library: target module per the toolchain block's
   `lib-layout`, statement sketch faithful to the informal source, the lemma
   decomposition, and where each piece comes from (exists at `file:line` /
   adapt from located declaration / prove new).
6. **Synthesis** — Write `outputs/.drafts/<slug>-recipe-research.md` first,
   then promote a concise final ranked brief to `outputs/<slug>-recipe.md`.
7. **Verification** — For any recipe you rank first, verify the key anchors:
   informal source locations, prior-mechanization URLs or paths, and every
   `file:line` claimed for prerequisites. Dispatch the `verifier` agent for
   this pass when the candidate set is large; for a small set, do it
   yourself. If a source or declaration cannot be checked, keep it in the
   brief only with an explicit `blocked` or `unverified` label.
8. **Provenance** — Write `outputs/<slug>-recipe.provenance.md` with date,
   sources consulted, sources accepted/rejected, verification status, and
   artifact paths.

## Required final shape

The final brief must include:

- **Recommendation:** the one recipe to try first and why.
- **Ranked recipe table:** one row per candidate with informal anchor, key
  construction, prerequisites (located/missing), prior mechanization, expected
  difficulty, and verification status.
- **Prerequisite notes:** exact names and types as quoted from disk, or the
  gap analysis for missing ones.
- **Implementation plan:** minimal steps to attempt the top recipe, including
  the lemma decomposition.
- **Known gaps:** missing prerequisites, unchecked prior-art claims, unclear
  side conditions, or fidelity risks in the encoding choice.
- **Sources:** anchors for every paper, mechanization, and library file used.

Do not claim a strategy is standard, mechanized before, or feasible in this
library unless the underlying checks prove it. Use `verified`, `unverified`,
`blocked`, and `inferred` precisely.
