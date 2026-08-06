# LaTeX notation in resources/ entries: surface and remediation plan

Survey date: 2026-08-05. Scope: every non-gitignored file under
`resources/`, checked for mathematical notation written in LaTeX
syntax instead of Unicode.

## Why the vendored surface is narrow

`resources/README.md` gitignores every fetched or derived source file
(the tarball, the `.tex`, the `.pdftext`). Only the entry `README.md`
files, plus a handful of small support files, leave the machine. A
`git ls-files resources/` plus a `git status --ignored` check confirms
this. The tracked (or about-to-be-tracked) surface is:

- 19 entry `README.md` files, plus `resources/README.md` itself.
- `resources/selinger-graphical-languages/CLAUDE.md`.
- `resources/kelly-maclane-conditions/kelly-mclane-conditions.pdftext.patch`.
- `resources/munch-maccagnoni-duploids/pdf-scan.py`.
- `resources/catlog/README.md`, untracked, ingested today, still
  PROVISIONAL.

The contamination this task is about is therefore entirely a prose
question: does an entry's Section map and Content digests prose render
formulas in Unicode, the way a reader sees them in a terminal or in
literate Agda, or does it carry raw LaTeX through from the source
`.tex`.

## Three patterns, one real problem

A blanket grep for `\command` and `$...$` over the tracked files turns
up three different things. Only one of them is the contamination the
user asked about.

**Pattern A: genuine LaTeX math left unconverted.** Dollar-delimited
formulas or bare backslash commands standing in for a symbol, inside
prose meant to read as Unicode math. This is the defect.

**Pattern B: `_{...}` / `^{...}` as a multi-character sub/superscript
bridge.** Entries write `pr₁^{a,λ}`, `η_{GFP}`, `χ_{X,Y,Z}`. Every
surrounding symbol is already Unicode (`η`, `χ`, `∘`, `→`, `Σ`). The
brace group appears only where the subscript or superscript itself has
more than one character. Unicode has no combining subscript for an
arbitrary string, and its subscript letter block covers few of the
letters these sources need (no `λ`, no comma). This is not LaTeX
notation displacing Unicode. It is Unicode notation using a bracket as
the only available grouping mark. Every entry with a deep
Content-digests section uses this convention, consistently.

**Pattern C: a source's own LaTeX macro name, quoted as data about the
source.** `\label{def:transport}`, `\newtheorem`, `\input`, `\title`,
`\bibliography`, `\qed`. These describe the `.tex` file's own
apparatus (duplicate labels, missing `\ref`s, the theorem-numbering
scheme) for an entry's Files, Vetting, and Section-map sections, which
exist to record exactly that. They are not math notation shown to a
reader. Leave them as they are.

Two entries already model the correct end state for the real defect.
`mmmm-classical-notions/README.md:165-166` renders `⟑` and `⟇` as the
symbols throughout its digest, then adds, once, "`⟑` and `⟇` render
the source's `\tensorialand` and `\tensorialor` macros" as a
parenthetical aside. `bentzen-naive-cubical/README.md:154-158` does
the same for `∙`/`∙ᵣ`/`∙ₗ` against the source's `\sq`/`\rsq`/`\lsq`.
Pattern A entries need to reach this same shape: Unicode in the
running prose, the LaTeX macro name quoted only as a labeled aside
where it helps a reader cross-reference the source.

## Surface found (Pattern A only)

| Entry | Extent | Example |
|---|---|---|
| `resources/catlog/README.md` | Severe. Untracked, PROVISIONAL, ingested 2026-08-05. Roughly lines 196-876 of 901 (the bulk of Section map and all of Content digests) carry the source's own macros unconverted: `\sig`, `\ptens`, `\cG`, `\dN`, `\types`, `\d`, `\ep`, `\Gamma`, `\Delta`, `\equivsym`, `\dA`, `\dT`, `\nAut`, `\mu`, `\alpha`, `\case`, dollar-delimited throughout | l.372-373: `` a set $\sig_1$ of **operations** with an **arity** function $\ay:\sig_1\to\dN$ `` |
| `resources/kraus-infty-cwf/README.md` | Moderate. 8 lines scattered through otherwise-converted prose | l.17: `` A definition of $\infty$-categories with families ($\infty$-CwF's) ``; l.231: `` not of the form $\Sigma(a{:}A).\,a=a_0$) ``; l.265: `` semicategory $\CC$ `` |
| `resources/rijke-hott/README.md` | Light. 3 spots. Notable: `resources/README.md:190` names this entry the format exemplar | l.207: `` congruence relations on $\N$ ``; l.248: `` identity types of $\Sigma$-types ``; l.460: `` elementhood relation \in on W(A,B) `` |
| `resources/bentzen-naive-cubical/README.md` | Trace. 1 spot, self-resolving on the next line | l.155-156: `` transport `a^{\lto{i}{j}}_A` (squiggly arrow) as `a^{i⇝j}_A` ``. The source macro name leaks into the first backtick span instead of staying in the explanatory aside |

No other tracked entry shows Pattern A. The eight remaining entries
with Section-map or Content-digests prose
(`mellies-dialogue-deformation`, `mellies-ribbon-tensorial-logic`,
`mmmm-classical-notions`, `munch-maccagnoni-duploids`,
`petrakis-dep-arrows`, plus the three already listed) use Pattern B
cleanly and no Pattern A. The remaining entries
(`capriotti-kraus-semi-segal`, `kelly-maclane-conditions`,
`kiselyov-having-effect`, `mellies-braided-dialogue`,
`mellies-dialogue-chiralities`, `mellies-micrological-negation`,
`petrakis-codep-slides`, `sterling-reflexive-graph-lenses`) carry
outline-depth entries with no math prose to contaminate, matching the
house rule that digest depth tracks the source's load
(`resources/README.md:178-181`). The `kelly-maclane-conditions`
`.pdftext.patch` is plain OCR-repair text, no math markup.

## Doctrine gap

`resources/README.md`'s Content-digests bullet (lines 174-182) says
digests state "what the source states... in the source's own terms
and notation" but never says which character set that notation uses.
This is the gap that let Pattern A through. Nothing in the entry
format currently tells a writer to render in Unicode rather than
transcribe the `.tex`.

Proposed addition, to the Content-digests bullet in
`resources/README.md`:

> Render notation in Unicode, matching literate Agda and CLI reading,
> never in raw LaTeX. Write a multi-character subscript or superscript
> as `_{...}`/`^{...}` when Unicode has no combining form for it. Quote
> a source's own LaTeX macro name only as a labeled aside connecting a
> Unicode symbol back to the source, for example "`⟑` renders the
> source's `\tensorialand`", never as the symbol itself.

This states Pattern B as the sanctioned bridge, not a defect, and
states Pattern C as a permitted aside, not a target for removal, while
closing the gap that produced Pattern A.

## Remediation plan

Four entries, in priority order.

1. **`resources/catlog/README.md`.** Rewrite lines 196-876 (Section
   map body plus all of Content digests) to Unicode notation, source
   macro names moved into labeled asides. This is the majority of the
   file and the only piece large enough to warrant a dedicated pass
   rather than a hand edit. Best timed now: the entry is still
   PROVISIONAL and unvetted (no `Vetted:` line, no `Statements
   verified:` field yet), so no citation currently depends on the
   current text and no re-audit is voided by rewriting it. Waiting
   until after vetting would force a second statement-audit pass for
   the same content.
2. **`resources/kraus-infty-cwf/README.md`.** Eight line-level edits:
   `$\infty$` to `∞`, `\CC` to `𝒞`, `$\Sigma(a{:}A).\,a=a_0$` to
   `Σ(a:A). a=a₀`, and the remaining five in the same family (l.17,
   32, 223-224, 231, 265, 291, 400, 406). This entry has a recorded
   `Statements verified` field, so a notation-only edit (no claim
   changes) should be flagged to the field's owner as requiring
   re-confirmation, per `resources/README.md`'s rule that any digest
   edit voids `N` until the audit re-runs.
3. **`resources/rijke-hott/README.md`.** Three spots (l.207, 248,
   460). Small, but this entry is the format's stated exemplar
   (`resources/README.md:190`), so it is worth fixing first among the
   light cases: a new entry author who copies this file as a template
   should not copy forward `$\N$`.
4. **`resources/bentzen-naive-cubical/README.md`.** One spot (l.155).
   Move the source macro name into the aside shape the same file
   already uses one line later, matching its own l.154 and l.158
   pattern.

Each edit is prose-only, inside an already-tracked or about-to-be-
tracked file. None touches the frontmatter identity fields (`sha256`,
`fetch-url`), so no re-fetch or re-hash follows. Items 2-4 change a
`Statements verified` field's standing per `resources/README.md`'s
voiding rule; item 1 has no such field yet to void.

## Open call for Lane

The proposed doctrine text above keeps Pattern B (`_{...}`/`^{...}`)
as the sanctioned bridge rather than folding it into the same fix as
Pattern A. Reasoning: it carries no backslash commands and no dollar
delimiters, every symbol around it is already Unicode, and it is the
only available plain-text answer to a real Unicode gap (no combining
subscript for `λ`, no subscript comma). Treating it as contamination
would mean redesigning eight already-clean entries' notation from
scratch with no clear replacement in view. This is a discretionary
call on entry-format doctrine, not a mechanical fact, so it is stated
here as a recommendation for confirmation rather than folded silently
into the plan above.
