# Provenance: resources-notation-unicode

Run date: 2026-08-05. Manual dispatch (direct grep-and-read audit),
not a bundled `/audit`, `/lit`, or `/deepresearch` invocation.

## Nature of this artifact

A notation-format inventory and remediation plan for `resources/`
entries, not a formalization or a proof-obligation audit. It carries
no kernel-layer verification component. Every claim anchors to a
`file:line` this task read directly or a shell command this task ran
and recorded below.

- **Sources consulted:** 21 tracked or about-to-be-tracked files under
  `resources/` (19 entry `README.md` files, `resources/README.md`,
  `selinger-graphical-languages/CLAUDE.md`), plus
  `kelly-maclane-conditions/kelly-mclane-conditions.pdftext.patch` and
  `munch-maccagnoni-duploids/pdf-scan.py`.
- **Sources accepted:** all 21, read or grepped in full.
- **Sources rejected:** none.
- **Verification:** PASS WITH NOTES.
- **Research files:** none (single-pass manual audit, no intermediate
  drafts).

## Method

1. `git ls-files resources/` and `git status --ignored --porcelain
   resources/` to establish the tracked (vendored, non-gitignored)
   surface versus the gitignored fetched/derived sources.
2. `rg` for `\$[^$]+\$`, `\\[a-zA-Z]+`, `\^\{`, `_\{` across every
   tracked `.md` file plus the untracked `resources/catlog/README.md`,
   to find candidate LaTeX-notation spots.
3. Manual read of every match's surrounding context to sort matches
   into three patterns: genuine LaTeX math left unconverted (the
   defect), the `_{...}`/`^{...}` multi-character sub/superscript
   bridge over otherwise-Unicode prose (a sanctioned convention,
   confirmed present and consistent across eight entries), and a
   source's own LaTeX macro name quoted as commentary about the
   source's apparatus (legitimate, matches the Files/Vetting/
   Section-map sections' own purpose).
4. Read `resources/README.md` in full for the entry-format doctrine
   the Content-digests bullet currently states, to locate the gap that
   let the defect pattern through and to draft an addition closing it.

## Checker runs performed

None. This artifact makes no claim that any code checks, builds, or
passes a proof obligation.

## Obligation (sorry) inventory

Not applicable. No formal code was produced or modified.

## Prose-lint record

Skill: `writing` (STE-flavored mode), self-lint applied before
delivery, then measured with the bundled linter.

```
$ python3 .claude/skills/writing/prose-lint.py outputs/resources-notation-unicode.md
outputs/resources-notation-unicode.md  words=1282 total=33 per100w=2.57 em_dash=0
```

Initial draft carried 2 em dashes, both removed by restructuring the
two sentences that used them. The remaining violations are chiefly
`long_sentence(>20w)` inside the Surface-found table, where each cell
is a single dense fragment the schema requires. This file lives under
`outputs/`, where the euler contract requires recording the score, not
clearing the `docs/` `--max-per100 2.0` gate.

## Verdict

**PASS WITH NOTES.** Every finding anchors to a `file:line` a reader
can open directly, or to a shell command reproduced above. The one
open item is a discretionary doctrine call (whether the
`_{...}`/`^{...}` bridge counts as sanctioned notation or as a further
target for remediation), stated explicitly in the report's "Open call
for Lane" section rather than resolved unilaterally. No kernel-layer
verification applies to this task.
