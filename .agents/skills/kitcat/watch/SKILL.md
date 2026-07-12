---
name: watch
description: Create a literature-front watch over a research area in type theory, category theory, univalent mathematics, or programming language foundations — arXiv listings (math.CT, cs.LO, math.LO, math.AT), specific nLab pages, 1lab modules, and author pages. Use when asked to monitor a field, track new papers or preprints, watch a page or library for updates, follow an author's output, or set up alerts on a research front. Produces a monitoring plan and a sourced baseline in notes/watches/; re-runs diff against the baseline and record dated deltas.
argument-hint: <topic-or-front>
args: <topic-or-front>
section: Research Workflows
topLevelCli: true
---

# Literature Watch

Create or refresh a literature watch for: $ARGUMENTS

Read `.agents/skills/kitcat/HARNESS.md` first; it maps every
capability named below to the tools in your harness.

Derive a short slug from the watch topic (lowercase, hyphens, no
filler words, at most 5 words). Every file this run writes uses that
slug. The run artifact for this skill is the watch file
`notes/watches/<slug>.md`; blocked capabilities and degraded
delegations are recorded there.

This is an execution request, not a request to explain the workflow.
Begin with the watch file, not with prose about the protocol.

If `notes/watches/<slug>.md` already exists, this is a re-run: go to
the re-run workflow below. Otherwise proceed as a new watch.

## What a watch covers

A watch monitors a literature front through concrete, re-checkable
sources: arXiv listings for the relevant categories (math.CT, cs.LO,
math.LO, math.AT — new-submission and recent listings, or a targeted
arXiv query), specific nLab pages (each by URL, with its revision
number when visible), 1lab modules (module pages by URL), and author
or lab pages. Every monitored source is a URL a later run can fetch
again and diff. Before choosing sources, consult what the repository
already tracks — `resources/` entries and `docs/gloss.md` — so the
signals watched are the ones that matter to the development, not
generic topic noise.

## Workflow — new watch

1. **Plan** — Write the monitoring plan to `notes/watches/<slug>.md`:
   the topic; the exact sources to monitor, each with its URL; which
   signals matter (new preprints, page revisions, new or changed
   modules, changed theorem statements); what counts as a meaningful
   change versus noise; the requested or a sensible check frequency;
   a task ledger for this run; and a dated run log. Summarize the
   plan briefly to the user and continue immediately; ask for
   confirmation only if the user explicitly requested plan review.
2. **Baseline sweep** — Sweep every monitored source now with the
   paper-search, web-search, and url-fetch capabilities. For a front
   wide enough to benefit from delegated triage, dispatch the
   `researcher` agent with a self-contained brief — its
   evidence notes go to `notes/watches/<slug>-research-*.md`, never
   inline; when it is absent in your harness, sweep lead-owned and
   record the delegation as degraded in the watch file. Capture
   each source's current state: the latest relevant arXiv postings
   (titles, authors, dates, arXiv ids), nLab page revision and
   last-modified signal, the 1lab module inventory for the watched
   area, latest items on author pages. Mark every planned source
   `done` or `blocked` in the task ledger — never silently skip
   one.
3. **Baseline artifact** — Save exactly one baseline to
   `notes/watches/<slug>-baseline.md`: the swept state of each
   source, dated; anything worth the user's attention now, with
   strict epistemic labels — mathematical claims harvested from
   literature are CONJECTURED, typically written `CONJECTURED,
   SOURCE-CHECKED against <ref>`; references surfaced by automated
   search are `[unvetted]` and support no load-bearing claim; a
   Provenance section recording date and who requested the watch,
   sources consulted vs accepted vs rejected (with reasons) and each
   accepted source's vetting status, any intermediate files used —
   each with its producer (which agent, or lead-owned degraded) —
   blocked capabilities and degraded delegations with what was done
   instead, and the verification status; and a closing Sources
   section with a direct
   URL for every source used. Sources worth permanent vetting are
   proposed in the Provenance section as candidate `resources/`
   entries, never created.
4. **Verify** — Run an adversarial pass over the baseline: sources
   cited but never actually opened, claims or status labels stronger
   than their evidence, sources named in the plan but missing from
   the baseline, and sections surviving from earlier drafts that the
   final evidence no longer supports. Grade findings FATAL / MAJOR /
   MINOR; fix FATAL before delivery and run one more pass after the
   fixes; note MAJOR in an Open Questions section; accept MINOR.
   Record the verification status in the Provenance section — PASS
   (clean final pass), PASS WITH NOTES (MAJOR findings remain in
   Open Questions), or BLOCKED (a required check could not run; name
   it).
5. **Schedule** — Only after the baseline artifact with its Sources
   section exists on disk. When the scheduling capability is visible
   in your harness, create the recurring follow-up at the planned
   frequency; its prompt re-invokes this skill with the same topic
   so the re-run resolves to the same slug; record what was created
   and at what cadence in the watch file. When no scheduling tool is
   visible, write `scheduling: BLOCKED — no visible tool` in both
   the watch file and the baseline, and give the manual instruction:
   invoke this skill again with the same topic to refresh the watch.
   Never claim a schedule that was not created, and never schedule
   before the baseline exists.
6. Verify on disk that both `notes/watches/<slug>.md` and
   `notes/watches/<slug>-baseline.md` exist before stopping.

## Workflow — re-run

1. Read the watch file, the baseline, and any prior delta entries.
   Re-sweep every monitored source with the same capabilities as the
   baseline sweep.
2. Diff the fresh sweep against the baseline and the most recent
   deltas: new postings, revised pages, added or changed modules,
   dead sources (an unreachable URL is itself a delta, recorded as
   blocked, not summarized from memory).
3. Append a dated delta entry to `notes/watches/<slug>.md`: what
   changed, what did not, changes flagged as meaningful against the
   plan's own definition, the same epistemic labels as the baseline,
   and a direct URL for everything cited. No change is a valid,
   recorded result. Update the run log; never rewrite prior entries.
4. Run an adversarial pass over the fresh delta entry: sources
   cited in the delta but not opened this run, claims or status
   labels stronger than their evidence, and sources named in the
   plan but missing from the sweep. Grade findings FATAL / MAJOR /
   MINOR; fix FATAL before the entry stands and run one more pass
   after the fixes; note MAJOR in the entry's open questions;
   accept MINOR. Record the pass outcome in the delta entry.
5. When the front has moved — sources consistently dead, or the
   signal concentrated somewhere the plan does not cover — amend the
   source list in the watch file with the change dated and its
   reason recorded, never silently.

## Scope

A watch run writes only under `notes/watches/`. It never edits
`docs/`, `src/`, `resources/`, or any other `notes/` tree. Spikes,
`docs/gloss.md` entries, and `resources/` entries suggested by a
sweep are proposals recorded in the watch file or delta entry —
never executed as a side effect.

## Honesty rules (binding)

- A source appears in the baseline or a delta only if it was opened
  this run via the url-fetch capability and states what it is cited
  for — record that as SOURCE-CHECKED. A reference surfaced by
  automated search remains `[unvetted]` — supporting no load-bearing
  claim — until a human confirms the opened document or a
  `resources/` entry covers it; record each promotion (who, or which
  entry) in the Provenance section.
- VERIFIED applies only to claims machine-checked in this repository
  (name the module or Gloss certificate); everything harvested from
  literature is CONJECTURED.
- Novelty language is "we are not aware of prior work", accompanied
  by the searches actually performed — never "new" or "first".
- Blocked capabilities and failed checks are reported as BLOCKED
  with the manual command a human could run; a missing check is
  never smoothed over, and a schedule is never claimed unless it was
  actually created.
