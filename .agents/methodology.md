# .agents/methodology.md — the working discipline

The practiced discipline of this library, stated positively as the
way work is done here. The specific enforcements live where they
act — the root `CLAUDE.md`, the agent definitions in `.agents/`, the
skills under `.agents/skills/kitcat/` — and this file is the shared
account they draw on. Each principle carries a worked exemplar from
the repository's own record.

## P1 — Pin at decision time, with the reason

Every ruling and every abandoned approach is recorded the moment it
is made, with its reason, in the run's plan ledger — not
reconstructed later. A failed proof attempt is preserved before it
is reverted (the "preserve the attempt, then revert" discipline),
so the next session inherits the decision rather than re-litigating
it. Exemplar: the θ-core / op-invol arc kept its spike and its wall
with the obstruction transcribed, and the next session mined that
wall into a naturality across the polarity swap.

## P2 — Prose about a formal object is untrusted until it is run

A mathematical claim graduates only when a spike typechecks it
against the real foundation — never a toy model; the typecheck is
the pin, prose is not. A spike is dispatched with an oracle-shaped
contract: a verdict in {DERIVED, STUCK, PARTIAL}, the route closed,
and the exact goal residue at any wall — verbatim or labeled
content-exact per the oracle contract (root `CLAUDE.md`, Agent
Discipline). A definitional
reduction a proof leans on is re-asserted as a present-tense
`killcheck-<name> = refl` in the Test/ regression tier wired into
`All`, so a reduction that stops firing fails the next
`just check-all`. A claim about an unobservable
surface (harness internals, an external build) ships with its probe
or ships as CONJECTURED. Exemplar: the PcomConservation (T20) arc —
the conservation-law fork was pinned by `Test/CodepPcomFaces`
typechecking against the real `Cat.Codep.Coherence` before the
record edit, and promotion was withheld until it returned — the
spike then graduated to `Gloss.PcomConservation`, its durable home.

## P3 — Enshrine same-session, into one canonical home

A result proven in a session is graduated that same session into
its canonical home: a dated `docs/gloss.md` ledger entry with its
honest status marker, and — when the evidence's only durable home
is the artifact — a frozen `Gloss.*` certificate in the same move,
held in exact bijection with the ledger entry. The session log
carries state and next steps only; it points at the canonical home,
never duplicating it. A run artifact's durable content is promoted
to its home and the artifact retired; nothing load-bearing lives
only in a scratch file, a plan ledger, or the harness-private
memory. Exemplar: T11 (TEL-independence) became the `docs/gloss.md`
T11 entry and `Gloss.EightFieldWall` in one move.

When Lane holds a promotion rather than ruling it in-session, the
same-session bar is met by the evidence, not the entry: tracked,
committed evidence — a tracked `Test/` spike, the typechecked
module — satisfies the anti-rot intent, and the ledger entry or
certificate lands on Lane's ruling. The bar itself does not soften:
nothing load-bearing lives only in untracked scratch, a plan
ledger, or harness-private memory. A held promotion is never
silently dropped — it is surfaced at the run's close per the
contract's promotion decision block (`.agents/CLAUDE.md`,
Delegation) and carried in the session log's held list until ruled.
Exemplar: the 2026-07-13 faithful-stratum run, whose three gloss
candidates were held for Lane with the evidence committed as the
tracked spike `Test/CodepFaithful-20260713-140913`.

## P4 — Literature unfolded to serve the construction, at speed

When a proof turns on a source, the vendored copy is opened during
the derivation and the entry is built to serve that read at speed:
the canonical source markup (LaTeX preferred over PDF over
transcribed text), a line-anchored location→content map whose depth
tracks the source's load, so a citation resolves at `<file>:LINE`.
When a load-bearing claim rests on an unvendored source, the default
is to ingest it (`resources/README.md` is the format authority).
Exemplar: the chirality design was steered by reading Melliès's
*Dialogue categories and chiralities* against the construction —
the source now vendored at `resources/mellies-dialogue-chiralities`,
backing docs/gloss.md T16. (Its counterpart cautionary case is
Kelly 1964: the absorb-cell design leaned on Kelly's unit-coherence
theorem, but the paywalled source was never opened, which is exactly
why T15 stands at CONJECTURED — the gap the ingest-on-need default
closes.)

## P5 — Quality by worked exemplar and mechanical gating

A bar is set by a worked example to imitate, not by an adjective,
and enforced by a check that is *run*, not trusted: the reviewer
independently executes `just check` (exit 42 is failure, zero
warnings) and `just lint changed` (the non-regression width gate)
on every touched module rather than accepting the author's word, and a convention the tree can gate is
gated (the authoring lint over the skills tree, the `just sync`
drift gate). Exemplar: the killcheck witnesses in
`src/Test/CodepCoherentKillchecks.lagda.md` (`killcheck-apPost` /
`killcheck-apPre = refl`) — a definitional reduction a proof leans
on, pinned as a present-tense `refl` in the Test/ regression tier
imported by `All`, so a reduction that silently stops firing fails
the next `just check-all`. The gate lives in the tree and runs
every build; it is not a trusted claim.

## P6 — Uniform conventions over special cases

A convention is stated once over the widest category it truly
governs, and applied to every member of that category — because
uniformity is what lets protocol be described succinctly: each
special case a convention tolerates is an edge case every
description, every brief, and every check must thereafter account
for. The discipline has two halves: applying a category-wide
ruling begins by enumerating the category's members and sweeping
all of them (root CLAUDE.md, Agent Discipline), and an exception
that seems warranted is proposed to Lane with its reasoning, never
self-granted — an unproposed exception is not flexibility, it is a
fork in the protocol that someone else will pay to rediscover.
Exemplar: the dated-artifact convention (2026-07-13) — "every
notes artifact is date-prefixed" is one rule, one canary row per
pattern, and one sentence in any brief; the evening it was applied
non-uniformly (topic files excepted ad hoc, watches missed
entirely) each gap surfaced as a separate correction, and the
path-pattern canary caught the last stale site in the very
doctrine edit that fixed the previous one.

## The Agda pipeline (the symmetric bracket)

The library's most-run flow: `analyzer` prepares (structural
analysis + proof strategy) → `coder` implements → `analyzer` reviews
for accuracy + `reviewer` runs the mechanical gate. The `analyzer`
is consulted before any non-trivial proof (h-levels, coherence,
transport, fibers, univalence); routine proofs bypass it. Exemplar:
the first end-to-end /prove run (2026-07-13, the faithful-stratum
spike; run record `notes/plans/2026-07-13-faithful-stratum-spike.md`)
— the analyzer's prep caught two memo-prose defects (the
transport-refl trap, the missing extract-agree axiom) before the
coder ran, every annotated sketch line then closed first-try at
four checkpoints, and the accuracy review verified the
implementation by transplant-diff against the sketch. Research
deliverables pass four gates in order, none skippable on confidence:
plan → firsthand reading → verify-before-deliver → ingest a
firsthand-needed source.

## Provenance of this account

These practices were distilled by studying a mature reference
implementation of the same workflow discipline and translating each
proven convention onto this library's own demonstrated work
(like-with-like), then verified against the repository's record. The
account stands on this library's own exemplars; the external study
that shaped the method is recorded outside the repository.
