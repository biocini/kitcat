# Duploid source audit: statement-level, both vendored papers

## Executive summary

Both duploid sources in `resources/` — `mmmm-classical-notions`
(Mangel, Melliès & Munch-Maccagnoni) and `munch-maccagnoni-duploids`
(Munch-Maccagnoni) — were statement-audited against the bar
`resources/README.md` sets for load-bearing citation [5].
`mmmm-classical-notions`'s seven existing content-digest claims are
7/7 CONFIRMED against `article.tex` [1, 7]. `munch-maccagnoni-duploids`
had no content digests at all; all 24 numbered statements in its
section map were located, anchor-confirmed with no drift, and
digested for the first time [3, 4, 8]. Two source-level textual
anomalies were found (a diagram typo in one paper, a proof-text error
in the other, both confirmed against rendered PDF pages, not extraction
artifacts); neither affects any load-bearing claim [1, 3]. One
cross-paper correspondence — mmmm's duploid definition against
Munch-Maccagnoni's two equivalent duploid definitions, which mmmm
explicitly credits as "a slight variant of" — is a plausible but
*unverified* equivalence, flagged as an open question rather than
asserted [1, 3].

This audit itself establishes the CONFIRMED verdicts below, but as of
this pass neither resources entry's `README.md` yet carries a written
`Statements verified:` field on disk: `mmmm-classical-notions`'s
Vetting section still reads "no independent statement audit has been
run" [2, l.49-54], and `munch-maccagnoni-duploids`'s still reads "No
statement audit has been run, so this entry carries no `Statements
verified:` field and supports no load-bearing citation" [4, l.47-49].
Writing that field is a follow-up edit to the resources entries, not
performed by this pass; see Q4 below and the caveats.

## Findings by question

### Q1 — mmmm-classical-notions's seven digest claims

All seven CONFIRMED against `article.tex` [1, 7]:

1. Non-associative category / unital magmoid (digested at l.1526,
   `\begin{definition}`): confirmed verbatim, including the `M^op`
   reversal (l.1536-1537) [1, l.1526-1537; 7].
2. Association, thunkable, linear (l.1084-1093 intro; l.1552-1562
   §2): confirmed verbatim in both locations [1, l.1084-1093, l.1552-1562; 7].
3. Polarity (l.1694): confirmed verbatim, including the "may be
   both" and `(−)^op` clauses [1, l.1694-1706; 7].
4. Shifts (l.1712): confirmed verbatim, including the universal
   factorization property [1, l.1712-1719; 7].
5. Duploid (l.1819-1822): confirmed verbatim; the composition-
   notation split is a fair paraphrase of l.1836-1837, not a direct
   quote, but faithful [1, l.1819-1822, l.1836-1837; 7].
6. The adjunction-duploid theorem (l.1857, theorem body continuing
   past l.1860): confirmed verbatim, both directions of the
   correspondence [1, l.1857-1873; 7].
7. The Hasegawa-Thielecke theorem (§11, l.3036 header; statement at
   l.3044-3047): confirmed [1, l.3036, l.3044-3047; 7]. The
   "double-negation monad" corollary phrase in the digest is sourced
   from the abstract (l.442-443), not from §11 itself — same claim,
   different location than the digest's single cited anchor.

Two anchor-precision notes, neither verdict-changing: claim 2's cited
range `l.1551-1570` overshoots the actual content (l.1552-1562) by
about 8 lines into unrelated epi/mono material; claim 6's cited
`l.1860` sits inside the theorem's body rather than at
`\begin{theorem}` (l.1857) [1, l.1857].

**A source-level typo, not a resources-entry defect**: the
composition law's diagram, in the `\ccomp_{X,Y,Z}` line at
`article.tex:1531` (inside the Definition environment opened at
l.1526), literally renders codomain `M(X,Y)` where the surrounding
prose (and every later use) requires `M(X,Z)` [1, l.1531]. The
README's digest already gives the corrected form silently; this note
exists so a reader diffing digest against source line-for-line is not
puzzled by the mismatch [7].

### Q2 — munch-maccagnoni-duploids's 24 numbered statements

All 24 anchors (Definitions 1, 2, 3, 5, 7, 9, 18, 20, 23, 26, 27;
Propositions 6, 8, 10, 12, 13, 14, 19, 21, 22, 24, 25; Remark 11;
Theorem 28) confirmed correct against `duploids.pdftext` by direct
`grep -n` match on each statement's opening line — no drift anywhere
[3, 4, 8]. Content digests for all 24 are now written (they did not
exist before this audit) at the depth standard `resources/README.md`
sets for a load-bearing source [5], matching `mmmm-classical-notions`'s
existing digest style [2]. Full text (as corrected by this revision —
see the discrepancy note below):
`outputs/.drafts/duploids-statement-audit-research-duploids.md` [8].

**A second source-level anomaly**, confirmed against the rendered PDF
page, not just the extracted text: Proposition 8 states "For any N,
`wrap_N` is thunkable. Dually, for any P, `force_P` is linear," at
l.434, but its own proof concludes "Hence `wrap_N` is linear" at
l.436 [3, l.434-436]. The proof's derived equation is
`h ◦ (g • wrap_N) = (h ◦ g) • wrap_N` — `wrap_N` sits in the
first-applied position of a length-3 associativity pattern, which is
exactly Definition 2's *thunkable* shape (`h(gf) = (hg)f`), not its
linear shape (`f(gh) = (fg)h`) [3, l.233-241]. Definition 2's
automatic-polarity cases do not rescue the "linear" reading either:
`wrap_N : N → ⇓N` has negative domain and positive codomain, outside
those cases. The proof names `wrap_N` throughout, so the proposition's
own duality clause ("the other result follows by symmetry") covers
`force_P`, not this sentence — no reading of the proof makes "linear"
locally correct. The proposition's own *statement* is correct and
matches the entry's section-map label ("`wrap_N` thunkable; dually
`force_P` linear") [4]; the closing sentence of the *proof* is the
one word that appears wrong. This is a genuine slip in the published
paper's own text, confirmed by rendering `duploids.pdf` page 8
directly (the published page itself reads "Hence wrap_N is linear")
and by regenerating the extraction with `pdftotext 26.06.0`, which is
byte-identical to the vendored `duploids.pdftext` — not a PDF-
extraction or vendoring problem.

**Discrepancy note**: the research file this section points to
(`duploids-statement-audit-research-duploids.md`) originally
mischaracterized the derived equation as matching Definition 2's
*linearity* clause and hedged the "linear" ending as possible
extraction noise. Both points were wrong. The file has been corrected
in place (2026-07-28) to match the analysis above; the correction is
recorded in the file itself. Any future promotion of these digests
into `resources/munch-maccagnoni-duploids/README.md` must carry the
corrected wording, not the original.

### Q3 — does mmmm's duploid definition actually correspond to Munch-Maccagnoni's duploid definitions?

Unverified — flagged as an open question, not asserted. `article.tex`
cites the `munchduploids` bibkey eight times total: three earlier
mentions in passing (l.712, l.835, l.1071) and five within §3 itself
(l.1682, l.1685, l.1817, l.1855, l.1857) [1]. The most direct of
these, immediately before the duploid definition, reads: "At this
stage, we are ready to recall **(a slight variant of)** the
definition of duploid from `\citet{munchduploids}`" (l.1817) [1,
l.1817]. mmmm explicitly concedes variance here, not identity — this
is the strongest primary-source evidence for treating the two
definitions as related-but-unverified rather than identical, and it
comes from the paper itself, not from this audit's own comparison.

Munch-Maccagnoni's paper gives *two* stated duploid definitions, not
one, and declares them equivalent to each other: the equational
Definition 7 (`duploids.pdftext:418-433` — explicit `delay_P`,
`force_P`, `wrap_N`, `unwrap_N` maps subject to four equations) and
Definition 9 (l.440-442 — the same shift mappings, but replacing the
four equations with the requirement that `force_P` and `wrap_N` are
each invertible, linear and thunkable respectively), introduced as
"the following equivalent definition of a duploid" (l.439) with
Proposition 8 as the stated bridge between them [3, l.418-442].

mmmm's own duploid definition (l.1819-1822, via the general shift
definition at l.1712-1719) is a third presentation again: a
*universal property* — an object `⇓X` with a thunkable epi
`ω_X : X → ⇓X` universal among maps out of `X` for factorization
through a linear map — rather than either of Munch-Maccagnoni's
named-map forms [1, l.1712-1719, l.1819-1822].

The honest framing of the open question is therefore mmmm's
universal-property variant against Munch-Maccagnoni's Definition
7/Definition 9 pair (which the source paper itself already proves
equivalent to each other, via Proposition 8), not a two-way comparison
against Definition 9 alone. This audit did not attempt to show mmmm's
universal property unwinds to either of Munch-Maccagnoni's forms —
that is exactly the "slight variant" gap mmmm's own l.1817 sentence
names but does not itself close for the reader. A future equivalence
pass should target the equational Definition 7 as the more likely
bridge (matching mmmm's own factorization-property style more closely
than Definition 9's bare invertibility does), and should locate
whichever definition mmmm's "(a slight variant of)" actually refers
to — this audit did not determine that either.

No specific numbered result inside Munch-Maccagnoni's paper is cited
by mmmm for the adjunction-correspondence theorem (l.1857): all
citations there and at l.1682/l.1685 are whole-paper `\citet`/`\cite*`
references, naming no internal theorem or proposition number.

### Q4 — the `Statements verified:` bar, and whether both entries clear it

`resources/README.md`'s Vetting contract states: "an entry supports
load-bearing citation once its identity is hash-verified and its
statement audit is recorded... `Statements verified: N/M CONFIRMED
(<depth>), <date>, by <agent>, @ <canonical-hash prefix>`... **Load-
bearing use requires this field.**" [5, l.119-130]. This is distinct
from the Lane-exclusive `Vetted: <date>, Lane` line, which this run
does not write [5, l.134-136].

Both entries' identities are already hash-verified at the level of
their canonical artifact, and this audit additionally confirms the
chain from that canonical hash down to the file actually read line-by-
line, for both entries:

- `mmmm-classical-notions`: canonical artifact `sha256: 8d9edc19055a...`
  (the tarball) [2, l.3]. The audited file is the extracted
  `article.tex`, confirmed byte-identical to the tarball member
  (`sha256: 20275f3bec8c...`) and consistent with the frontmatter's
  recorded `sha256-inner` for the decompressed tarball. 7/7 CONFIRMED
  [7].
- `munch-maccagnoni-duploids`: canonical artifact `sha256:
  a39faa7cfe1f...` (the PDF) [4, l.3]. The audited file is
  `duploids.pdftext` (`sha256: 3fbaa6dc2473...`, not previously
  recorded in the entry), confirmed to regenerate byte-identically
  from the hashed PDF via `pdftotext 26.06.0` per the entry's own
  documented extraction chain [4, l.60-63]. 24/24 CONFIRMED, newly
  digested [8].

This pass establishes the CONFIRMED counts and hash chain an audit
needs to license a `Statements verified:` line, but as of this pass,
neither entry's `README.md` has that field written: `mmmm-classical-
notions`'s Vetting section still reads "no independent statement audit
has been run" [2, l.49-54], and `munch-maccagnoni-duploids`'s still
reads "No statement audit has been run" and "supports no load-bearing
citation" [4, l.47-49]. Per the contract's own wording, an entry with
no recorded `Statements verified:` field "supports nothing" for
load-bearing use [5, l.122-123]. Neither entry clears the bar on disk
yet; writing the field into both `README.md` files is outstanding
follow-up work, not performed by this audit pass. Neither carries a
`Vetted:` line either — that remains Lane's discretion to add
separately [5, l.134-136].

### Q5 — agreement with `src/Cat/Logic/TODO.md`'s informal duploid dictionary

`src/Cat/Logic/TODO.md`'s "Settled: the duploid dictionary,
statement-checked" section records an informal pass run 2026-07-27
over "the brief's §9 anchors, in both vendored sources," and states
explicitly that it does not constitute the full statement audit: "The
full statement audits remain pending, and the PROVISIONAL standing of
both entries is unchanged" [6, l.292-293]. Of its claims, four were
checked against this audit's findings and agree: the pre-duploid
triple (`••`, `◦◦`, `•◦`-associativity) [6, l.274-275; 3, l.180], the
applicative-vs-diagrammatic transcription convention (Munch-Maccagnoni
composes applicatively, kitcat diagrammatically — the order reverses
when transcribing) [6, l.276-282], `P` as the Kleisli category of the
monad [6, l.287; 3, l.581], and the duploid-of-an-adjunction
associative-iff-idempotent correspondence [6, l.288-289; 1,
l.1857-1873]. The TODO section makes further claims this audit did
not check — notably that the shift unit `ω` has a two-sided pointwise
inverse yet is not itself an isomorphism (directly relevant to Q3's
invertibility comparison, but out of this pass's scope) and that the
"∗-autonomous" leg of a separate collapse chain was not found in
either source [6, l.283-284, l.290-291]. The four checked claims
agree; the rest are unchecked, not confirmed or refuted here. That
module TODO entry's own "pending" framing is now addressed by the
present audit's CONFIRMED verdicts, though the `Statements verified:`
fields it depends on have not yet been written to either `README.md`
(see Q4); the TODO entry should be cross-referenced against this
report rather than left implying no audit has happened at all.

## Caveats and disagreements

- The two source-level anomalies above (mmmm's l.1531 codomain typo,
  Munch-Maccagnoni's Proposition 8 proof-text error) are noted but
  not corrected in the primary sources — they are the papers' own
  text, read as vendored, and confirmed against rendered PDF pages,
  not merely the text extraction [1, l.1531; 3, l.434-436]. Both are
  judged not to affect any load-bearing claim: in each case the
  *stated* definition/proposition is correct and matches what the
  resources entry records; only an internal diagram rendering or a
  proof's closing sentence is affected.
- Q3's cross-paper correspondence is the one substantive open item,
  and this revision widens it from a two-way to a three-way
  comparison: mmmm's universal-property duploid definition against
  Munch-Maccagnoni's own equivalent pair (Definition 7, Definition 9)
  [1, l.1712-1822; 3, l.418-442]. mmmm's own text concedes "(a slight
  variant of)" rather than identity (l.1817), which is evidence for
  treating the correspondence as unverified, not evidence against a
  future equivalence proof. This is not a defect in either paper or
  either resources entry — it is a genuine mathematical question this
  audit's scope does not answer.
- Q4's `Statements verified:` field is not yet written into either
  `README.md`, despite this pass's CONFIRMED counts. The CONFIRMED
  verdicts in this document are not themselves a substitute for that
  field: per the contract, the field is what makes load-bearing use
  mechanical and auditable, not the existence of a report describing
  an audit [5, l.119-130].
- An earlier revision of this document's Verification Record claimed
  "no dead or stale anchors found" while several of its own citation
  ranges were themselves imprecise (a research artifact of drafting
  under time pressure, not of the underlying source-reading). That
  claim has been withdrawn; the anchors in this document have been
  re-checked and corrected in this revision, and the Verification
  Record below states exactly what was re-checked rather than
  asserting blanket completeness.

## Open questions

- Which of Munch-Maccagnoni's two duploid definitions (the equational
  Definition 7, or the invertible-maps Definition 9) does mmmm's "(a
  slight variant of)" at `article.tex:1817` actually refer to? Not
  determined here; a future pass should read enough of §3's
  surrounding prose (or the paper's later sections, where the
  variant's precise nature might be spelled out) to answer this before
  attempting the equivalence proof itself.
- Does mmmm prove, anywhere in the paper, that its shift-based duploid
  definition coincides with either of Munch-Maccagnoni's forms? Not
  checked here.
- `src/Cat/Logic/TODO.md`'s duploid-dictionary section still reads as
  if the full audit were pending, and carries claims (the `ω`
  two-sided-inverse note, the "∗-autonomous" leg) this audit did not
  check. Updating that note is outside this run's scope (module-ledger
  territory, not `resources/`) but is flagged for whoever next touches
  that file.
- Neither `resources/mmmm-classical-notions/README.md` nor
  `resources/munch-maccagnoni-duploids/README.md` has had its
  `Statements verified:` field written as of this pass. Writing those
  fields (with date, agent, and canonical-hash prefix per the
  contract) is outstanding work, separate from this report.

## Sources

1. `resources/mmmm-classical-notions/article.tex` (vendored arXiv
   e-print v4, `sha256: 8d9edc19055a23bd32a40d4e613b4462235b1a8497b6ce4310a028bc5a319a6d`
   for the tarball; extracted `article.tex` confirmed byte-identical
   to the tarball member, `sha256: 20275f3bec8cbfa3dcad3d0d3a7710af78b41b74ba6a413b052f6a53e4f880aa`;
   canonical hash recorded in `resources/mmmm-classical-notions/README.md:3`).
2. `resources/mmmm-classical-notions/README.md`.
3. `resources/munch-maccagnoni-duploids/duploids.pdftext` (vendored
   HAL v1 deposit `duploids.pdf`, `sha256:
   a39faa7cfe1f882fcb70c4263ce9d9108a431f3698fe98759587316216cb5ac9`;
   extracted `duploids.pdftext` confirmed to regenerate byte-
   identically from that PDF via `pdftotext 26.06.0`,
   `sha256: 3fbaa6dc24730558994968dff073f3f6b1bab1fe50be6b582b04799507d4cd57`;
   canonical hash recorded in `resources/munch-maccagnoni-duploids/README.md:3`).
4. `resources/munch-maccagnoni-duploids/README.md`.
5. `resources/README.md` (Vetting-section contract, read in full).
6. `src/Cat/Logic/TODO.md` (the "duploid dictionary, statement-
   checked" section, for cross-check).
7. `outputs/.drafts/duploids-statement-audit-research-mmmm.md`
   (researcher T1 output).
8. `outputs/.drafts/duploids-statement-audit-research-duploids.md`
   (researcher T2 output, corrected 2026-07-28 for the Proposition 8
   mischaracterization — see Q2's discrepancy note).

## Verification Record

**Toolchain**: this task is a source-fidelity audit of prose research
artifacts, not a formal-proof deliverable. `.euler/TOOLCHAIN.md`
governs Agda kernel checks; no formal declarations are asserted here,
so no kernel-layer check applies. All obligations below are
source-layer.

**Checks performed across the verification and review passes**
(2026-07-28):

- `sed -n '410,440p' resources/munch-maccagnoni-duploids/duploids.pdftext`
  — confirmed Proposition 8 (l.434) states "wrap N is thunkable...
  force P is linear," and its proof (l.436) ends "Hence wrap N is
  linear."
- `grep -n "^Proposition 8\." resources/munch-maccagnoni-duploids/duploids.pdftext`
  and `grep -n "Hence wrap" resources/munch-maccagnoni-duploids/duploids.pdftext`
  — confirmed exact line numbers 434 and 436.
- Rendered `duploids.pdf` page 8 directly and confirmed the published
  page itself reads "Hence wrap_N is linear." — the anomaly is in the
  paper, not the extraction.
- Regenerated the extraction with `pdftotext` (Poppler 26.06.0) from
  the vendored PDF; the output is byte-identical to the vendored
  `duploids.pdftext`.
- `cat resources/munch-maccagnoni-duploids/README.md` — confirmed the
  Files section states "Native text layer; no OCR chain was needed or
  run" at l.58-59 (not l.65-68 as an earlier draft cited), and
  confirmed the Vetting section (l.40-49) says no statement audit has
  been run and the entry "supports no load-bearing citation."
- `sed -n '1521,1537p' resources/mmmm-classical-notions/article.tex`
  — confirmed the unital-magmoid definition (`\begin{definition}` at
  l.1526) and the composition-law diagram's `M(X,Y)` codomain typo,
  located precisely at l.1531 (the `\ccomp_{X,Y,Z}` line), not l.1526
  as an earlier draft stated.
- `sed -n '1690,1720p' resources/mmmm-classical-notions/article.tex`
  — confirmed the Polarity definition (l.1694) and the positive-shift
  definition (l.1712), verbatim as digested.
- `sed -n '1815,1840p' resources/mmmm-classical-notions/article.tex`
  — confirmed the duploid definition (l.1819-1822), the `⊳`/`⊲`
  composition-notation sentence (l.1836-1837), and the "(a slight
  variant of)" sentence at l.1817, missed by an earlier draft despite
  being inside this exact checked window.
- `sed -n '3030,3050p' resources/mmmm-classical-notions/article.tex`
  — confirmed the Hasegawa-Thielecke section header (l.3036) and
  theorem statement (l.3044-3047).
- `sed -n '440,446p' resources/mmmm-classical-notions/article.tex`
  — confirmed the abstract's double-negation-monad parenthetical at
  l.442-443.
- `rg -n "munchduploids" resources/mmmm-classical-notions/article.tex`
  — confirmed the full citation inventory: l.712, l.835, l.1071,
  l.1682, l.1685, l.1817, l.1855, l.1857 (eight mentions total, five
  in §3). An earlier draft's list of "three citations
  (l.1682, l.1687-1688, l.1857)" was wrong: l.1687-1688 contains no
  citation (the second §3 citation sits at l.1685), and l.1817/l.1855
  were omitted.
- `grep -n "sha256" resources/mmmm-classical-notions/README.md
  resources/munch-maccagnoni-duploids/README.md` — confirmed the
  frontmatter canonical-artifact hashes.
- `shasum -a 256 resources/munch-maccagnoni-duploids/duploids.pdftext
  resources/mmmm-classical-notions/article.tex` — recorded the hashes
  of the files actually read line-by-line in this audit (distinct
  from, but chained to, the canonical-artifact hashes above).
- `gunzip -c` + `shasum` on the tarball, and `tar -xzOf ... article.tex
  | shasum`, confirming the on-disk `article.tex` matches both the
  frontmatter `sha256-inner` and the tarball member exactly.
- `sed -n '95,136p' resources/README.md` — confirmed the Vetting
  contract's `Statements verified:` field wording (l.119-130) and the
  "supports nothing" clause (l.122-123) — an earlier draft's citations
  for these ([4, l.65-68], [5, l.118-119]) were off by several lines.
- `grep -n "Statements verified\|PROVISIONAL\|Vetted:" resources/mmmm-classical-notions/README.md
  resources/munch-maccagnoni-duploids/README.md` — confirmed neither
  entry currently has a `Statements verified:` line; both remain
  PROVISIONAL on disk.
- `grep -n "duploid dictionary" -A 30 src/Cat/Logic/TODO.md` —
  confirmed the pre-duploid triple, transcription convention, Kleisli
  claim, idempotence claim, `ω`-inverse note, and "∗-autonomous"
  unchecked-leg note as digested in Q5, and confirmed the "full
  statement audits remain pending" sentence at l.292-293.

**Anchors confirmed**: all `file:line` anchors quoted in this document
were checked directly against the two vendored primary sources
(`article.tex`, `duploids.pdftext`), `resources/README.md`,
`src/Cat/Logic/TODO.md`, and both entry `README.md` files, in either
the original verification pass or this revision. Six anchor errors
found in the prior verified draft (the "Native text layer" citation,
the "supports nothing" citation, the codomain-typo location, the
citation-inventory anchors, and two smaller clipped quotations) are
corrected in this revision; each correction is called out at its
point of use above rather than left as a blanket claim.

**Discrepancies found and corrected across all passes**:

1. (Verification pass) The initial draft's Q4 section and executive
   summary asserted "Both clear the bar for load-bearing citation"
   without qualification; downgraded to reflect that the field is not
   yet written on disk.
2. (This revision, per adversarial review) Q3's citation-structure
   claim was factually wrong (miscounted citations, wrong line for one
   of them) and omitted Definition 7 from the comparison space;
   rewritten on the verified citation inventory and widened to a
   three-way comparison.
3. (This revision) The Verification Record's blanket "no dead or
   stale anchors" claim was itself false against six of the prior
   draft's own citations; withdrawn and replaced with the itemized
   list above.
4. (This revision) The research file backing the 24 duploids digests
   mischaracterized Proposition 8's derived equation and hedged an
   extraction-artifact explanation that direct PDF rendering rules
   out; the research file has been corrected in place, and this
   document's Q2 section now carries an explicit discrepancy note
   pointing to that correction.
5. (This revision) Hash scoping in Q4 was imprecise (naming the
   canonical-artifact hash for text actually read from a derived
   file); Q4 now records the full hash chain — canonical artifact to
   audited file — for both entries.
6. (This revision) Q5's "agrees throughout" overstated the checked
   coverage; rescoped to the four claims actually checked, with the
   TODO section's other claims listed as unchecked rather than
   implicitly endorsed.
7. (This revision) Q1 claim 1's headline anchor (l.1521) did not match
   the digest's own cited anchor (l.1526); corrected.

No material was deleted in any pass — every correction narrows a claim
to what the evidence supports; the underlying CONFIRMED tallies (7/7,
24/24) are unaffected throughout and remain supported by the anchor
checks above.

**Obligation inventory**: not applicable (no formal proof obligations
in scope for this source-fidelity audit).

**Word-choice audit**: "CONFIRMED" is used only for statements
independently re-checked against `article.tex` or `duploids.pdftext`
in either the original research passes, the verification pass, or
this revision. "Clears the bar" / "load-bearing" claims are scoped
throughout to what is established (the audit tallies and hash chain)
versus what is outstanding (the `README.md` field).
