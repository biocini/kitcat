# Provenance: duploid source audit, statement-level

- **Date:** 2026-07-28
- **Rounds:** 1 research round (2 parallel researcher subagents), 1
  verification pass, 1 review pass, 1 revision pass.
- **Sources consulted:** 2 vendored primary sources
  (`resources/mmmm-classical-notions/article.tex`,
  `resources/munch-maccagnoni-duploids/duploids.pdftext` and its
  source `duploids.pdf`), 2 resources `README.md` entries, the
  `resources/README.md` contract, `src/Cat/Logic/TODO.md`. No
  external web search was performed or needed — both sources were
  already vendored and hash-identified.
- **Sources accepted:** all of the above.
- **Sources rejected:** none.
- **Verification:** PASS WITH NOTES. No FATAL findings from the
  reviewer. Four MAJOR findings (a miscounted/mis-anchored citation
  inventory and an incomplete comparison space in the Q3 cross-paper
  correspondence discussion; a blanket "no dead or stale anchors"
  claim falsified by several of the verified draft's own imprecise
  citations; a mischaracterized Proposition 8 digest in the
  supporting research file) were fixed in the revision pass and
  confirmed fixed by on-disk `rg`/`grep` checks (see the revised
  document's Verification Record). Three MINOR findings (hash-scoping
  imprecision, an overstated cross-check coverage claim, one drifted
  headline anchor) were also fixed in the same pass rather than left
  open, since the revision pass was already rewriting the affected
  sections.
- **Prose lint:** `prose-lint.py outputs/duploids-statement-audit.md`
  scores 6.96 violations/100w (48 em dashes across 3361 words, mostly
  structural parenthetical use consistent with existing repo prose;
  not a `docs/` file, so the 2.0 gate does not apply). Not swept for
  style after the fact-checking passes, to avoid re-disturbing a
  document that has already been through three rounds of anchor
  verification.
- **Plan:** `outputs/.plans/duploids-statement-audit.md`
- **Research files:**
  `outputs/.drafts/duploids-statement-audit-research-mmmm.md` (T1,
  7/7 CONFIRMED), `outputs/.drafts/duploids-statement-audit-research-duploids.md`
  (T2, 24/24 anchors confirmed and digested; corrected post-review for
  a Proposition 8 mischaracterization).

## Barrier-removal actions taken after this audit

Per `resources/README.md`'s Vetting contract, a completed statement
audit licenses (but is distinct from writing) a `Statements verified:`
field in each entry's own `README.md` — the field, not this report, is
what the contract names as removing the load-bearing-citation
barrier. Following this audit:

- `resources/mmmm-classical-notions/README.md` — `Statements verified:
  7/7 CONFIRMED (digest-level), 2026-07-28, by Claude (Sonnet 5), @
  8d9edc19055a` added to the Vetting section.
- `resources/munch-maccagnoni-duploids/README.md` — `Statements
  verified: 24/24 CONFIRMED (digest-level), 2026-07-28, by Claude
  (Sonnet 5), @ a39faa7cfe1f` added to the Vetting section, and a
  Content digests section (previously absent) added for all 24
  numbered statements, sourced from the corrected research file.

Neither entry's `Vetted: <date>, Lane` line was written — that remains
Lane's exclusive discretion.

`TODO.md`'s "The two duploid source audits, statement-level" line is
proposed for checkoff, contingent on confirmation, since this audit is
the thing it names.

## Open items this audit did not resolve

- Q3: whether mmmm's universal-property duploid definition is
  equivalent to Munch-Maccagnoni's Definition 7/9 pair. Unverified,
  explicitly flagged as an open question, not asserted either way.
- Whether Proposition 8's "Hence `wrap_N` is linear" is a known
  erratum in the published FoSSaCS 2014 paper. Confirmed as a genuine
  error in the published text (checked against the rendered PDF page,
  not just the extraction), but its status as a known/reported erratum
  was not investigated.
- `src/Cat/Logic/TODO.md`'s duploid-dictionary section still frames
  the audit as pending; updating that module-ledger note is outside
  this run's `resources/`-scoped work.
