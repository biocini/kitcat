---
artifact: duploids.pdf
sha256: a39faa7cfe1f882fcb70c4263ce9d9108a431f3698fe98759587316216cb5ac9
format: pdf
fetch-url: none
metadata-url: https://inria.hal.science/hal-00996729v1
doi: 10.1007/978-3-642-54830-7_26
version: v1
fetched: 2026-07-27
secondary-artifact: duploids.pdftext
secondary-sha256: eb36ae85af65e85c000226857d923d20104b7bb89ebae4d83655b2a2490afd9a
---

# Munch-Maccagnoni — Models of a Non-Associative Composition

## Citation

Guillaume Munch-Maccagnoni. *Models of a Non-Associative
Composition*. FoSSaCS 2014, the 17th International Conference on
Foundations of Software Science and Computation Structures, April
2014, Grenoble, France. pp. 396–410.
DOI 10.1007/978-3-642-54830-7_26. HAL Id hal-00996729, version 1
(submitted 26 May 2014), <https://inria.hal.science/hal-00996729v1>.

The vendored copy's own citation block (l.5-6) gives the conference,
the pages and the DOI. It names no book series, no volume number and
no editors, so this record names none either. A future citation that
needs the series has to source it outside the artifact.

The vendored copy is the HAL author deposit, which carries the HAL
cover page ahead of the article proper. The article's own title page
starts at `l.24`.

From the abstract: "We characterise the polarised evaluation order
through a categorical structure where the hypothesis that composition
is associative is relaxed. Duploid is the name of the structure, as a
reference to Jean-Louis Loday's duplicial algebras. The main result is
a reflection Adj → Dupl where Dupl is a category of duploids and
duploid functors, and Adj is the category of adjunctions and pseudo
maps of adjunctions."

This is the originating duploid paper, cited as the duploids reference
by [`mmmm-classical-notions`](../mmmm-classical-notions/README.md).

## Vetting

Directed agent ingestion, 2026-07-27. **PROVISIONAL.**

Statements verified: 29/29 CONFIRMED (digest-level), 2026-07-29, by
Claude (Opus 5), @ a39faa7c / eb36ae85. Two prefixes, because the
Section map's anchors index the corrected extraction, not the raw one.
The first pins `duploids.pdf` (frontmatter `sha256`), the second pins
`duploids.pdftext` after the correction patch below (frontmatter
`secondary-sha256`). Either a re-fetch or a further patch change voids
this field. The full audit is `outputs/duploids-entry-audit.md`.

What was opened and checked: the HAL cover page, and the article's
title page and abstract, read to build the bibliographic record above.
The section map's line anchors were produced mechanically over the
extraction and checked against the numbered statements they name.

A field claiming 24/24 was issued 2026-07-28 and withdrawn the same
day. The pass that issued it also wrote the digests it certified,
which `resources/README.md` does not permit. An independent read then
found six digests drifting from the source, and coverage at 24 of the
paper's 28 numbered statements.

Eleven reads have now touched the file. The counts a reader can check
against the current text are these. The Section map section states its
own coverage of the numbered statements, the section headings and the
unnumbered passages a digest treats as items of their own. The Content
digests section carries 29 bullets: 28 statement-level digests, one per
numbered statement, plus one for the unnumbered shift-data passage. So
no statement lacks a digest.

The fidelity count is the field above. The eleventh read's audit
re-derived it from scratch. The six named corrections landed. So did
the four digests that the coverage gap named, for Proposition 4,
Corollary 15, Proposition 16 and Proposition 17.

The third read refused to re-issue the field. It found that the
Proposition 16 digest had been typed from the flattened two-column
extraction in line order, repaired both of its equations against a
page render, and recorded the interleaving in the digest. That read
left a flag over Proposition 14 and Proposition 16 for a fourth
reader.

The fourth read closed the flag over Proposition 14. The digest had
dropped the qualifiers "(in C1)" and "(in C2)" that the source
attaches to the two equations at `duploids.pdftext:647-649`. Both are
restored, and a page render of PDF page 11 confirms them. That same
read wrote four other things: 27 section-map entries, the Files
section's defect table, the Source errata section, and the "What the
source establishes" section. An independent review then found three
faults in that new material. The defect table missed one place. The
map lacked §2.3 and the shift data. The Files section named the
paper's composition glyph wrongly.

The fifth read wrote the correction patch below and applied it. That
changed `duploids.pdftext` and its `secondary-sha256`. Under
`resources/README.md` this counts as a re-extraction. It would void a
`Statements verified:` field, and the entry has none to void. The
`l.NNN` anchors survive it, because every hunk stays inside a
line. The same read
added §2.3, the shift-data range and the thesis footnote to the map.
It split the Remark 11 digest. It rewrote the digests to use the
paper's own `⊙` where they had used bare juxtaposition. It restored
the quantifier ranges in Definition 23, the arrow directions in
Definition 26, and the second errata item. No second reader has seen
any of that. Treat the correction patch, the three new map entries and
the notation change as unreviewed.

The sixth read extended the correction patch to a third class of drawn
mark. That is the overline and underline that separate two copies of an
object on PDF page 6. The extension changed `duploids.pdftext` and its
`secondary-sha256` again, so it is again a re-extraction. The read
also scanned the path operators of all 16 page content streams. It then
revised three claims that overreached: the split-display count, the
interleaved-display list, and the notation key's rule on juxtaposition.
No second reader has seen the over/underline hunks or the revised claims.

The seventh read replaced that hand scan with `pdf-scan.py`, a script in
this directory. Every drawn-mark count in the Files section
now comes from a run of it, not from a procedure retyped each round.
That left the font `ToUnicode` count as a hand scan. The table that
carries it says so.

That run corrected three claims. The drawn-mark total rose by one,
because the hand scan had missed a decorative rule on the HAL cover
page. The interleaved-display list gained four ranges, two of which the
script found and no earlier read had named. The list also drops its
claim to be complete, because the script's third report is a candidate
list rather than a closed inventory. The read then
put the polarity-superscript definitions into the Proposition 10 digest,
and gave every digest that reads a flattened display a note that says
so. It changed no hash. The patch and the extraction are untouched, and
a reader can rerun the script.

The eighth read closed an accounting gap the seventh left. The
stroked-path table's line numbers for Definition 3's ditto rules correct
the script rather than reproduce it, and the table now says so. The read
also regrouped the sentence that discharges the ten regions no digest
reads, which had put Figure 2 in the page-7 group. It gave the script a
`--check` mode that compares this file against a fresh scan. It wrote
the shift-data digest's six definitions with the source's `≝`.

That read added one caveat and answered five points a review had raised
against the script. The caveat is the line-map dependence of two
stroked-path categories, which the Files section states in full. Two of
the five points were undocumented limits of the PDF reader, the `/ObjStm`
scan and the literal-string tokenizer. The other three were a missing
dropped-fill count, a dead branch, and two unguarded file reads.

Five smaller changes came with it. The read pinned the script's own run
to `nix develop`. It corrected `--help` and the module docstring to say
that the category names are tuned to this document. It narrowed the
over/underline table's "differ only where" sentence to the four `l.307`
rows. It rephrased the Files section's note on the script's git status.
It defined what "reads" means for the interleaved-display table's third
column. It changed no anchor, no hash and no patch hunk.

The ninth read widened `--check` and pinned it. The coverage paragraph in
Files lists what the mode reads and gives the comparison count, so this
narration restates neither. The eighth read's version made 33
comparisons. The mode also asserts its own count, so deleting a claim
fails the run instead of quietly removing a test.

The same read rewrote the paragraph that describes the mode, which had
claimed every count below. It also corrected two older claims. The
Vetting section had called `pdf-scan.py` tracked, and git reports it
untracked and not ignored. The Proposition 10 digest had written `=` for
the source's `≝` in three places, and had set the composition operator
as a subscript. A render of PDF page 10 gives the three definitions that
digest now carries.

An independent review then ran the mode against 69 mutations of this
file. Forty failed and 29 passed. Its findings against the mode were
these. Two coverage bullets named a whole table where the mode read some
of its columns. One of the two page-6 rule counts went unread. The
exception list named three items where the mutations found more, and no
comparison enforced the disclosure of the one declared correction.

The tenth read answered every one. The mode now reads the glyph table's
extraction column against a fresh extraction, and its patch column
against that column. It also reads the arithmetic that places the
glyphs, both page-6 rule counts, and the note that discloses the
declared correction. Deleting that note now fails the run. The read
rebuilt the exception list, so the list of what the mode reads is now
the entry's account of coverage.

The eleventh read was the audit `resources/README.md` calls for: every
digest re-derived from scratch, independent of every prior read's
verdict, at digest-level depth. It found 28 of the 29 digests faithful,
and one drift. The Theorem 28 digest and "What the source establishes"
both wrote the reflection's triangle as `⊳`. A 600 dpi render of PDF
page 15 shows `◁`. It traced the cause into the PDF's own font maps,
not into Poppler: two fonts carry a `ToUnicode` entry for the wrong
triangle, in opposite directions, so the mark reaches the extraction
mirrored. That defect now has its own paragraph under "What the patch
does not repair," naming the affected lines and the two fonts
responsible.

The same read closed the flag on Proposition 16, since an independent
reader had now checked its digest, and found two smaller drifts
elsewhere: the digest's own `=` for the source's `≝` in both
assignments, and two "are the image of" glosses in Proposition 24
where the source reads "are in the image of". A third Source errata
item followed, for a notation slip at `l.858` the audit found along the
way. All four were corrected, and a second, independent pass then
re-read the corrected text and confirmed it before the tally closed at
29/29.

The same read corrected a spacing artifact in the Proposition 10
digest's hom-set definition, in two places, against a render of PDF page
10. It stated the entry's rule for transcribing the source's script
capitals, in the notation key. It marked the subscript on the boxed
arrow that PDF page 9 sets. It changed no anchor, no hash and no patch
hunk. No second reader has seen the widened check mode.

The flag over Proposition 16 is closed. The eleventh read's audit
checked its digest independently and confirmed it, and the two `=`
signs it wrote for the source's `≝` are corrected.

The identity is hash-verified and the extraction reproduces
byte-identically (`pdftotext`, Poppler 26.06.0, then the correction
patch). All 28 section-map anchors to numbered statements resolve to
the line that opens the statement, re-checked after the patch. So the
entry is sound as a pointer into the paper, and a digest read as the
statement carries the audit above behind it.

Whether `mmmm-classical-notions`'s duploid definition, credited "a
slight variant of" this paper's (`article.tex:1817`), coincides with
Definition 7 or Definition 9 is open. That sentence credits the paper,
not either definition.

## Source errata

No errata audit has run over the paper. Three inconsistencies turned up
in the course of building the digests below. All three are recorded
against a direct render of the PDF page rather than against the
extraction alone. The list is what the entry found, not a count over
the paper.

- **Proposition 8's proof, closing sentence** (PDF page 8). The
  proposition states that `wrap_N` is thunkable, and the derivation
  above the closing sentence establishes Definition 2's shape. The
  closing sentence nonetheless reads "Hence `wrap_N` is linear". The
  proposition's own statement is correct, and the paper's later text
  reads the proposition as thunkable (`duploids.pdftext:703-704`). The
  digest below states the proposition, not the closing sentence.
- **A cross-reference names the wrong kind of item** (PDF page 13).
  `duploids.pdftext:796` reads "This is the essence of proposition
  15". Item 15 is Corollary 15, not a proposition. The reference
  points at the right result. This is a smaller slip than the one
  above, and it changes no mathematics.
- **A negative superscript switches notation** (PDF page 14).
  Proposition 24's second condition writes `g ∈ C1(N, A⁻)`, with the
  ordinary minus sign, where §3.2 fixes the negative superscript as
  `A⊖` and uses it everywhere else. The digest below transcribes `A⁻`
  faithfully, since that is what the page shows. The source itself is
  the one that switches marks.

## Files

- `duploids.pdf` — the canonical artifact, the HAL v1 deposit. This
  is the format of record. The entry is `format: pdf` because no
  source markup was supplied.
- `duploids.pdftext` — greppability fallback, and the file the
  section map's `l.NNN` anchors index. Native text layer. No OCR
  chain was needed or run. A tracked correction patch is the last step
  of the chain (below). Pinned in the frontmatter as
  `secondary-artifact`, so a silent re-extraction is detectable.
- `pdf-scan.py` — the measuring tool for every drawn-mark count below.
  Original to this entry, not derived from the source, so no `.gitignore`
  rule covers it. Python standard library only, plus Poppler for the line
  map.

Extraction provenance, regenerable byte-identically. Write the sed
script below to a scratch path outside this directory, such as
`/tmp/duploids.patch.sed`, then run:

```
pdftotext duploids.pdf duploids.pdftext
sed -f /tmp/duploids.patch.sed duploids.pdftext > tmp && mv tmp duploids.pdftext
```

Run both steps inside `nix develop`, which pins `pdftotext version
26.06.0` (Poppler) and GNU sed 4.10. The patch uses no GNU extension.
BSD sed, as shipped by macOS, produces the same bytes, checked
2026-07-29 against a temp-directory regeneration. 975 lines, before
and after the patch. Every hunk is a substitution inside one line, so
the patch moves no line and voids no `l.NNN` anchor.

Every drawn-mark count below comes from one run of

```
python3 pdf-scan.py duploids.pdf
```

Run it inside `nix develop` as well. That pins Python 3.14.6 and the
same `pdftotext version 26.06.0` (Poppler) the extraction step uses.

The script decompresses all 16 page content streams, tokenizes the path
operators while it tracks the CTM, and prints three reports: the filled
circular clusters that draw the `⊙` glyph, an inventory of every stroked
path, and the regions where the extraction leaves a two-column display
out of reading order. It maps each mark to an extraction line through
`pdftotext -bbox-layout`, and it aligns the layout to the extraction by
text rather than by position. Rerun it to regenerate any drawn-mark
count below. The third report is a candidate list rather than a closed
inventory, and the section on interleaved displays says what that costs.

Two of the ten stroked-path categories below rest on that line map
rather than on geometry alone. The over/underline rules of §2.2 and
Proposition 13's subterm markers share a stroke width and overlap in
length. So the script separates them by a hardcoded pair of extraction
line numbers. Under `--no-line-map` the two collapse into one category
of 12. A Poppler version that moved the line map could therefore move
the 6/6 split.

`python3 pdf-scan.py duploids.pdf --check` compares this file against a
fresh scan. It exits non-zero on a difference. What it reads:

- the headline sentence of each of the three reports, with the page set
  or the page count that sentence gives
- the glyph table: every row's line, page and count, its extraction
  column against a fresh extraction, and its patch column against that
  extraction column
- the arithmetic that places those glyphs, and the list of the lines
  that end in one
- the stroked-path table: every count, every page set, and every line
  reference, including the one row that gives a range
- both page-6 rule counts, the sentence that turns the drawn rules into
  combining characters, and the widths that tell a group rule from a
  single-character one
- the interleaved-display table: every row's range holds at least one of
  the script's regions, and the arithmetic accounts for every region
- the line numbers of the one declared correction, against the script's
  own declaration and against the note that discloses it
- its own comparison count, so a deleted claim fails the run instead of
  quietly removing its own test

A clean run makes 90 comparisons. Not every one of them ends at the scan.
The count of interleaved rows a digest reads, the comparison count in the
sentence above, and the disclosure of the declared correction go against
the script's own record or against another part of this file, because no
scan settles them.

One difference is deliberate, and the script declares it with its reason.
The script also holds the pattern that finds the note under the
stroked-path table, and it fails the run when that note goes missing or
stops matching the declaration. So a `--check` failure means the entry
and the script have drifted apart.

The list above is what the mode reads. Everything else in this entry
stands on other evidence, and these are the parts a reader is most
likely to take for checked:

1. The font `ToUnicode` counts under "What the patch does not repair",
   and their total. Those come from a separate hand scan that no tool in
   this directory reproduces, and that table says so.
2. What the patch writes, where a page render is the evidence rather
   than a path count. That covers the ditto table with its paragraph,
   the over/underline table, and the trailing-`⊙` pairing table. It also
   covers the render resolutions those sections name, and the paragraph
   that sets 49 drawn marks against 48 characters.
3. The extraction provenance above: the `sed` fence, the command chain,
   and the line count. `just resources-verify` checks the two
   frontmatter hashes, which is what pins the extraction the `l.NNN`
   anchors index.
4. The line-map caveat above, which reports what a second run under
   `--no-line-map` gives. A `--check` run scans once, with the map on.
5. Which digests read or cite an interleaved range. The mode counts the
   rows marked "yes" against the prose and reads no further. A row's own
   range can also drift by a line at each end, unless the split-display
   sentence names that row.
6. The section map and the digests, which index the extraction rather
   than the drawn marks.
7. The Vetting and Source errata sections, which record what a read
   found rather than what the scan counts.

### What the patch repairs

**The composition glyph.** Definition 1 gives the polarity-agnostic
composition its own operator, a ring with a filled dot at its center.
That is `⊙`, U+2299 CIRCLED DOT OPERATOR. It is not `◦` (U+25E6, the
paper's negative-middle composition) and it is not `•` (U+2022, the
positive-middle one). A 1200 dpi crop of PDF page 4 shows all three
marks within four lines of each other.

The PDF draws `⊙` as a vector path, not as a character in any font.
So `pdftotext` emits nothing at all for it. What the drop leaves
behind varies. In most places the two operands stay side by side with
a space. At `l.221` it leaves "neutral for ." with no operands. At
`l.408` it leaves the dangling "• - and ◦- associativity".

The paper draws that path exactly 40 times. The path signature is two
concentric circle subpaths and a smaller filled dot subpath, all
sharing a center. The first report of `pdf-scan.py` finds 40 such
clusters, on PDF pages 4 (1), 5 (19), 8 (2), 11 (8), 12 (6) and 13 (4).
Every cluster holds three subpaths, and no cluster holds any other
number, so no cluster is a partial match. The scan finds no second
path-drawn character in the document. It does find drawn rules. Those
are the subject of the next two headings and of "What the patch does
not repair".

The table below carries all 40, and it reproduces the script's per-line
report. A `pdftoppm -png` render of the named page confirms each one.
The Count column gives the number of `⊙` the patch writes on that line,
and it sums to 40.

| Line | The extraction reads | The patch writes | Page | Count |
| --- | --- | --- | --- | --- |
| `l.183` | `a morphism g f ∈` | `a morphism g ⊙ f ∈` | 4 | 1 |
| `l.221` | `neutral for .` | `neutral for ⊙.` | 5 | 1 |
| `l.235` | `f (g h) = ( f g) h` | `f ⊙ (g ⊙ h) = ( f ⊙ g) ⊙ h` | 5 | 4 |
| `l.237` | `h (g` | `h ⊙ (g ⊙` | 5 | 2 |
| `l.239` | `f ) = (h g)` | `f ) = (h ⊙ g) ⊙` | 5 | 2 |
| `l.262` | `(h) = g h f .` | `(h) = g ⊙ h ⊙ f .` | 5 | 2 |
| `l.263` | `(g1 g2 ) h ( f 2 f 1 ) = g1 (g2 h f 2 ) f 1 ` | `(g1 ⊙ g2 ) ⊙ h ⊙ ( f 2 ⊙ f 1 ) = g1 ⊙ (g2 ⊙ h ⊙ f 2 ) ⊙ f 1 ` | 5 | 8 |
| `l.408` | `to • - and ◦- associativity.` | `to •⊙- and ⊙◦- associativity.` | 8 | 2 |
| `l.691` | `( f force A ) ◦ (delay A g) = f` | `( f ⊙ force A ) ◦ (delay A ⊙ g) = f ⊙` | 11 | 3 |
| `l.692` | `( f unwrap A ) • (wrap A g) = f` | `( f ⊙ unwrap A ) • (wrap A ⊙ g) = f ⊙` | 11 | 3 |
| `l.697` | `delay A` | `delay A ⊙` | 11 | 1 |
| `l.698` | `wrap A` | `wrap A ⊙` | 11 | 1 |
| `l.710` | `⇑ f = delay B` | `⇑ f = delay B ⊙` | 12 | 1 |
| `l.712` | `f` | `f ⊙` | 12 | 1 |
| `l.716` | `⇓ f = wrap B` | `⇓ f = wrap B ⊙` | 12 | 1 |
| `l.720` | `f` | `f ⊙` | 12 | 1 |
| `l.769` | `F (g f ) = Fg F f .` | `F (g ⊙ f ) = Fg ⊙ F f .` | 12 | 2 |
| `l.785` | `from F h Fg F f = F (h g f ) which` | `from F h ⊙ Fg ⊙ F f = F (h ⊙ g ⊙ f ) which` | 13 | 4 |

Ten of the 40 fall at a display that `pdftotext` broke across lines.
The right operand then lands on a later line. The patch writes such a
`⊙` at the end of the line that carries its left operand. That is an
editorial placement, not source content, and it is the first of the two
editorial choices the patch makes. The second is the per-character
marking of the over/underline rules, below. Ten lines therefore end in
`⊙`: `l.237`, `l.239`, `l.691`, `l.692`, `l.697`, `l.698`, `l.710`,
`l.712`, `l.716` and `l.720`.

The patch writes the other 30 inside a line. Three of those name the
operator rather than apply it, so they have no operands at all: one at
`l.221`, two at `l.408`. One more, the first `⊙` on `l.237`, opens the
group `(g ⊙ f )` that closes on `l.239`, so its right operand is off the
line as well. The remaining 26 carry both operands on the line they sit
on. Four of the 26 sit on `l.691` and `l.692`, beside a trailing `⊙`.

A trailing `⊙` needs its right operand, and line order does not give
it. The pairings, all confirmed against a render of the named page:

| Trailing `⊙` | Its right operand | Page |
| --- | --- | --- |
| `l.237` (Definition 2, thunkable law) | `f ) = (h ⊙ g) ⊙` at `l.239` | 5 |
| `l.239` (same law) | `f` at `l.241` | 5 |
| `l.691` (`( f ⊙ force A ) ◦ (delay A ⊙ g) = f ⊙`) | `g` at `l.694` | 11 |
| `l.692` (`( f ⊙ unwrap A ) • (wrap A ⊙ g) = f ⊙`) | `g` at `l.695` | 11 |
| `l.697` (`delay A ⊙`) | `force A = id A` at `l.700` | 11 |
| `l.698` (`wrap A ⊙`) | `unwrap A = id A` at `l.701` | 11 |
| `l.710` (`⇑ f = delay B ⊙`) | `f ⊙` at `l.712` | 12 |
| `l.712` (still `⇑f`) | `force A` at `l.718` | 12 |
| `l.716` (`⇓ f = wrap B ⊙`) | `f ⊙` at `l.720` | 12 |
| `l.720` (still `⇓f`) | `unwrap A` at `l.722` | 12 |

Pairing by line order fails on all four page-11 rows. A reader who
pairs `l.691` forward reaches `l.692`, which heads the other equation.

**Definition 3's ditto rules.** The definition is a four-row table.
Row 1 reads out in full. Rows 2, 3 and 4 replace "is the sub-category
of" with a long horizontal ditto rule. `pdftotext` emits nothing for a
rule. A render of PDF page 5 shows all three rules. The patch writes
out what each rule abbreviates.

| Line | The extraction reads | The patch writes | Page |
| --- | --- | --- | --- |
| `l.249` | `thunkable morphisms of D.` | `is the sub-category of thunkable morphisms of D.` | 5 |
| `l.250` | `linear morphisms of N .` | `is the sub-category of linear morphisms of N .` | 5 |
| `l.252` | `thunkable morphisms of P.` | `is the sub-category of thunkable morphisms of P.` | 5 |

The definition runs to `l.253`, not `l.250`. For the `N_l` and `P_t`
rows the extraction also emits the row label after the row text. So
`l.250` carries text and `l.251` carries its label. Correcting that
needs a line move, which would shift every later anchor, so the patch
leaves it. Pair `l.250` with `l.251` and `l.252` with `l.253` when
reading the raw extraction. The Sub-categories digest below reads all
four rows correctly.

**The overline and underline of §2.2.** Definition 5's pre-duploid
gives the negative objects as a disjoint copy `⇑|P|` of the positive
ones. The source names the two copies of one object apart by a drawn
rule. An overline marks the negative-side name, an underline the
positive-side name. Six such rules fall on PDF page 6, and `pdftotext`
drops every one. The extraction leaves a chain of bare `P`s that reads
as nonsense.

The patch writes an overline as U+0305 COMBINING OVERLINE and an
underline as U+0332 COMBINING LOW LINE. Unicode has no combining mark
that spans two characters, so a rule over a two-character group reaches
the corrected file as one mark per character. That is the second
editorial choice the patch makes, and the first is the trailing `⊙`
above. Two of the six rules span a group, so the six drawn rules become
eight combining characters, on two lines.

The source column below shows the group each rule covers, at the extent
the render gives it.

| Line | The rule | The source shows | The patch writes | Page |
| --- | --- | --- | --- | --- |
| `l.300` | over `A` | `𝒫(A̅, B̲)` | `P ( A̅, B̲)` | 6 |
| `l.300` | under `B` | `𝒫(A̅, B̲)` | `P ( A̅, B̲)` | 6 |
| `l.307` | over `P` | `P̅ = P̲ ≝ P` | `P̅ = P̲ = P` | 6 |
| `l.307` | under `P` | `P̅ = P̲ ≝ P` | `P̅ = P̲ = P` | 6 |
| `l.307` | over the group `⇑P` | `⇑̅P̅ ≝ LP` | `⇑̅P̅ = LP` | 6 |
| `l.307` | under the group `⇑P` | `⇑̲P̲ ≝ P` | `⇑̲P̲ = P` | 6 |

In the four `l.307` rows the source and patch columns differ only where
the source reads `≝` and the extraction reads `=`. The paragraph after
the table explains that. The two `l.300` rows differ further. The source
sets a script capital `𝒫` where the extraction emits `P`, and the
spacing of the argument list differs too.

A 500 dpi crop of PDF page 6 carries all six. `pdf-scan.py` finds ten
stroked paths on that page: these six, plus the four edges of the box
around the hom-set display. The two group rules measure 12.2 points
against 6.7 to 6.9 for the four single-character rules, which is how the
table reads the extent. The script matches each rule against the word
boxes of `pdftotext -bbox-layout`, so the table assigns a rule to a
character rather than to a line alone.

The source's `≝` reaches the extraction as `=` on both lines. The
`def` above it lands on a line of its own (`l.301`, `l.303`, `l.305`).
The patch leaves that alone, so the corrected lines still read `=`
where the source reads `≝`.

### The patch

```sed
183s/, a morphism g f ∈/, a morphism g ⊙ f ∈/
221s/neutral for \./neutral for ⊙./
235s/^f (g h) = ( f g) h$/f ⊙ (g ⊙ h) = ( f ⊙ g) ⊙ h/
237s/^h (g$/h ⊙ (g ⊙/
239s/^f ) = (h g)$/f ) = (h ⊙ g) ⊙/
249s/^thunkable morphisms of D\.$/is the sub-category of thunkable morphisms of D./
250s/^linear morphisms of N \.$/is the sub-category of linear morphisms of N ./
252s/^thunkable morphisms of P\.$/is the sub-category of thunkable morphisms of P./
262s/(h) = g h f \./(h) = g ⊙ h ⊙ f ./
263s/(g1 g2 ) h ( f 2 f 1 ) = g1 (g2 h f 2 ) f 1 /(g1 ⊙ g2 ) ⊙ h ⊙ ( f 2 ⊙ f 1 ) = g1 ⊙ (g2 ⊙ h ⊙ f 2 ) ⊙ f 1 /
300s/= P ( A, B) ✁/= P ( A̅, B̲) ✁/
307s/we define P = P = P and ⇑P = LP and ⇑P = P\./we define P̅ = P̲ = P and ⇑̅P̅ = LP and ⇑̲P̲ = P./
408s/to • - and ◦- associativity\./to •⊙- and ⊙◦- associativity./
691s/^( f force A ) ◦ (delay A g) = f$/( f ⊙ force A ) ◦ (delay A ⊙ g) = f ⊙/
692s/^( f unwrap A ) • (wrap A g) = f$/( f ⊙ unwrap A ) • (wrap A ⊙ g) = f ⊙/
697s/^delay A$/delay A ⊙/
698s/^wrap A$/wrap A ⊙/
710s/^⇑ f = delay B$/⇑ f = delay B ⊙/
712s/^f$/f ⊙/
716s/^⇓ f = wrap B$/⇓ f = wrap B ⊙/
720s/^f$/f ⊙/
769s/F (g f ) = Fg F f \./F (g ⊙ f ) = Fg ⊙ F f ./
785s/from F h Fg F f = F (h g f ) which/from F h ⊙ Fg ⊙ F f = F (h ⊙ g ⊙ f ) which/
```

Twenty-three commands over 23 lines, every one line-addressed, so no
pattern can fire anywhere else. The line count above holds after the
patch for that reason.

Two words carry the arithmetic here, and they name different things. A
**drawn mark** is a feature of the source: a vector path or a drawn rule
that `pdftotext` dropped. A **character** is what the patch writes into
the corrected file. The two do not stand one to one.

The patch restores 49 drawn marks, in three classes: 40 occurrences of
the `⊙` glyph, 3 ditto rules and 6 over/underline rules. Those 49 marks
reach the corrected file as 48 characters and 3 phrases. Each `⊙` costs
one character, so 40 of U+2299. The 6 over/underline rules cost 8
combining characters, 4 of U+0305 and 4 of U+0332, because two of the
rules span a two-character group. Each ditto rule costs a spelled-out
phrase rather than a character. Those counts hold on disk.

### What the patch does not repair

The extraction garbles a further class of symbol, and this patch
leaves that class alone. A Type 1 symbol font here carries no
`ToUnicode` entry for some of its codes. Poppler falls back to the
font's own glyph names for those. Several such codes then reach the
output as the wrong ASCII letter. A scan of every page content stream
against each font's `ToUnicode` map gives these counts.

| The source shows | The extraction emits | Count | Pages |
| --- | --- | --- | --- |
| `::=` (grammar productions) | `F` | 13 | 7, 9 |
| `∉` | `<` | 5 | 7, 9 |
| `≠` (`l.411`) | `,` | 1 | 8 |
| `↦` (`l.407`, `l.509`) | `7→` | 3 | 8, 9 |
| `⟨` | `h` | 17 | 7, 9 |
| `⟩` | `i` | 17 | 7, 9 |
| the proof-end box | U+0004 | 10 | 5, 8, 10-14 |
| the large `⟨ ‖ ⟩` display delimiters | nothing | 16 | 7, 9 |

Every one of these eight rows sits in §2.3, in §3.1, or at the end of a
proof. No digest below reads any of them, which is why they wait for a
pass of their own. Renders of PDF pages 7, 8 and 9 confirm the first
four rows. The counts come from a hand font scan that `pdf-scan.py`
does not reproduce, and no reader has checked all 82 occurrences
against a render. Treat this one table as unverified against a
rerunnable tool.

A ninth defect lives in the same font layer, and it is a different
mechanism: two fonts carry a `ToUnicode` entry that is simply wrong,
not missing, so the extraction emits a real but mirrored character
rather than a fallback ASCII letter. PDF objects 241 and 240 (font
`rtxmi`, code `0x2F`, glyph name `/triangleleft`) map to U+22B3 `⊳`
where the page renders `◁`. PDF objects 245 and 244 (font `txsya`,
code `0x42`, glyph name `/triangleright`) map to U+22B2 `⊲` where the
page renders `▷`. The two fonts flip in opposite directions.
`pdftotext` follows each map faithfully, so the fault is the PDF's own,
not the extractor's.

This affects the reflection mark at `l.154` and `l.900` (page renders
`◁`, extraction reads `⊳`) and the rewrite-relation mark at `l.372`,
`l.373`, `l.375`, `l.376`, `l.380`, `l.472`, `l.474`, `l.475`, `l.477`
and `l.478` (page renders `▷`, extraction reads `⊲`). Unlike the eight
rows above, this class is not confined to §2.3, §3.1, or a proof end:
`l.900` sits in §4.3, and the Theorem 28 digest reads it directly. A
reader who greps the extraction for either triangle gets the mirror
image of the source's mark. The Theorem 28 digest below is written from
the render, not the extraction, for this reason.

The extraction also interleaves two-column displays. The patch cannot
repair those either, because the repair is a line move.

This class has no closed count, and the entry does not claim one. The
third report of `pdf-scan.py` finds 20 regions where the extraction
leaves a display out of reading order, over PDF pages 1, 3, 5, 7, 8, 9,
10, 11 and 12. That report reads the layout `pdftotext` itself computed,
so a display the layout analysis reads as one column never reaches it.
It is a candidate list, not an inventory. The table below is the subset
that carries mathematics a digest could reach, after a read of all 16
page renders. Treat it as the best current list rather than as a
complete one.

| Range | The display | A digest reads it |
| --- | --- | --- |
| `l.421-433` | Definition 7's two boxes, equations against morphism typings | yes |
| `l.522-534` | §3.2's oblique-morphism composition, two derivations side by side | no |
| `l.536-557` | §3.2's polarity superscripts, the boxed `A⁺ →_D B⊖` against the four defining equations | yes, and the Proposition 10 digest now carries the four equations |
| `l.584-589` | the two shift definitions `⇑P ≝ FP` and `⇓N ≝ GN`, side by side inside the shift-data passage at `l.583-603` | yes |
| `l.666-689` | the shift table, the two `⇓A`/`⇑A` cases against `delay`/`force`/`wrap`/`unwrap` | yes |
| `l.691-701` | the four equations that fix the extension to all objects, two columns | yes |
| `l.707-722` | Proposition 16's two definitions | yes |
| `l.736-758` | the two adjunction diagrams after Proposition 17 | no |

The eight rows cover ten of the script's 20 regions. A row gives the
range of the whole display, and the script splits a display that spans
two rendered blocks. So `l.421-433` covers the script's `l.422-426` and
`l.429-433`, and `l.736-758` covers its `l.736-754` and `l.756-758`.

The other ten regions carry no mathematics a digest reads. They are the
HAL cover page (1), Table 1 (1) and Definition 3's ditto rows (1). The
paragraph on those rows above gives the pairing. The rest are Figure 1
with §2.3's rewrite-rule and equation displays (3), Figure 2 with §3.1's
rule and equation displays (3), and Proposition 13's proof chain (1).
Figure 1 sits on PDF page 7 and Figure 2 on PDF page 9, beside their own
section's displays.

Four digests read the six ranges the table marks "yes": Definition 7,
Proposition 10, the shift-data passage, and Proposition 16. Each of the
four names its interleaving in its own text.

To read a range is to transcribe content out of it. Three further
digests cite `l.583-603` as a location without transcribing from it:
Proposition 12, Proposition 22 and Theorem 28. That range contains the
flattened `l.584-589`, so the warning at the head of the digest section
covers them.

`l.522-534` also loses eight drawn inference bars, four per derivation
(PDF page 9, confirmed by render). Without them `l.526` and `l.527`
read as two independent assertions rather than as a conclusion and its
restatement.

Besides the 40 `⊙` clusters, the second report of `pdf-scan.py` finds 86
stroked paths over all 16 page content streams. The table below accounts
for all 86, and it reproduces the script's category report.

| Kind | Strokes | Where | Patched |
| --- | --- | --- | --- |
| box edges around a display | 48 | 12 boxes, PDF pages 4, 5, 6, 7, 8, 9, 11, 12, 15 | no |
| inference bars | 8 | PDF page 9, `l.522-534` | no |
| Proposition 13's subterm markers | 6 | PDF pages 10, 11, `l.624`, `l.625`, `l.632` (two), `l.633`, `l.637` | no |
| the over/underline of §2.2 | 6 | PDF page 6, `l.300`, `l.307` | yes |
| footnote separators | 4 | PDF pages 2, 3, 8, 15 | no |
| adjunction-diagram arrows | 4 | PDF page 12, after Proposition 17 | no |
| Definition 3's ditto rules | 3 | PDF page 5, `l.249`, `l.250`, `l.252` | yes |
| Table 1's rules | 3 | PDF page 3 | no |
| figure column separators | 3 | PDF pages 7, 9, Figures 1 and 2 | no |
| the HAL cover-page rule | 1 | PDF page 1, beside the "To cite this version:" block | no |

One line number in that table does not come from the script. A fresh run
puts Definition 3's first ditto rule at `l.247`. The rule belongs to the
row whose text is `l.249`, and the table carries that corrected number.
Page 5 sets the row in two word groups: the label `D_t` at one x-range,
the row text at another. The rule falls in the gap between them.

The line map matches a mark to a row by horizontal overlap with a word
box. The owning row scores nothing there, so the wide row above it wins.
The raw output also marks the other two ditto rules `l.250~` and
`l.252~`. That `~` says the line came from vertical distance alone
rather than from a confident match. `--check` declares this one
correction with its reason, and it fails on any other divergence.

The subterm markers point at the part of an equation that the next
step rewrites. They change no equation, so their loss costs a reader
the pointer and not the mathematics. The paper draws a box as four
rules with a font character at each corner. Only the corners survive,
so a box reaches the extraction as the stray `✄`, `✂` and `✁` a reader
meets at `l.297`, `l.300`, `l.421` and elsewhere. The cover-page rule is
HAL deposit decoration, ahead of the article's own title page, and it
carries no content of any kind.

## Source provenance

Lane placed the PDF in the repository root on 2026-07-27, and it was
moved into this entry unmodified. The ingesting agent performed no
fetch, so `fetch-url` is `none` rather than a URL that was not
exercised. The recorded `sha256` is the identity of the file as
supplied, and it has not been checked against any public copy.

The HAL record is open access, and the article's HAL landing page is
recorded as `metadata-url`. The Springer version behind the DOI is
paywalled. A re-fetcher should expect the HAL deposit to carry the
cover page reproduced in the vendored copy, and should treat a
byte-difference against the recorded hash as a re-ingestion.

## Section map

Anchors index `duploids.pdftext`. Jump with
`sed -n 'A,Bp' duploids.pdftext`.

- HAL cover page — `l.1`
- Title, author, abstract — `l.24` (title), `l.29` (abstract)
- Introduction — `l.39`
- Footnote: the article shortens Chapter II of the author's PhD thesis
  — `l.67`
- Table 1 (comparison of direct models of computation) — `l.69`
- Outline, structure theorem, characterization of duploids — `l.151`
- §2 Pre-duploids — `l.176`
- **Definition 1** (pre-duploid) — `l.180`
- The categories `P` and `N` cut out by the polarity partition —
  `l.224`
- §2.1 Linear and Thunkable Morphisms — `l.231`
- **Definition 2** (linear, thunkable) — `l.233`
- **Definition 3** (the sub-categories of a pre-duploid) — `l.246`
- **Proposition 4** (hom-sets extend to a profunctor) — `l.257`
- §2.2 Examples of Pre-duploids — `l.268`
- **Definition 5** (thunk, after Führmann) — `l.286`
- **Proposition 6** (thunkable for thunk-force = thunkable for
  pre-duploids) — `l.315`
- The runnable monad, the concept dual to the thunk — `l.318`
- §2.3 Syntactic Pre-Duploid — `l.333`
- §3 Duploids — `l.415`
- **Definition 7** (duploid, first form) — `l.418`
- **Proposition 8** (`wrap N` thunkable, dually `force P` linear) —
  `l.434`
- **Definition 9** (duploid) — `l.440`
- §3.1 Syntactic Duploid — `l.445`
- §3.2 The Duploid Construction — `l.512`
- **Proposition 10** (the construction is a pre-duploid) — `l.576`
- **Remark 11** (P is the Kleisli category of the monad GF, N dually)
  — `l.581`
- The shifts of the constructed pre-duploid, and the six definitions
  `⇑P`, `⇓N`, `delay_P`, `force_P`, `wrap_N`, `unwrap_N` —
  `l.583`-`l.603`
- **Proposition 12** (every adjunction determines a duploid) — `l.607`
- §3.3 Linear and Thunkable Morphisms in Duploids — `l.610`
- **Proposition 13** (thunkability criterion) — `l.614`
- **Proposition 14** (linearity criterion) — `l.647`
- Idempotent adjunction, the four equivalent statements — `l.650`
- **Corollary 15** (the duploid is a category iff the adjunction is
  idempotent) — `l.653`
- §3.4 Structure of Shifts — `l.657`
- The boxed reversed adjunction `⇓ ⊣ ⇑ : P → N` — `l.663`
- The shifts and `delay`/`force`/`wrap`/`unwrap` extended to all
  objects, with the four equations that fix the extension, and the
  extension of Proposition 8 — `l.664`-`l.704`
- **Proposition 16** (`⇑`, `⇓` as adjoint equivalences) — `l.707`
- **Proposition 17** (the shift profunctor isomorphisms) — `l.731`
- §3.5 The Category of Duploids — `l.766`
- **Definition 18** (functor of pre-duploids) — `l.768`
- **Proposition 19** — `l.772`
- **Definition 20** (the category `Dupl`) — `l.786`
- §3.6 Examples of Duploids — `l.790`
- Thunk-force categories and categories with a runnable monad,
  characterized among duploids — `l.810`-`l.817`
- §4 Structure Theorem — `l.821`
- §4.1 Every Duploid Comes From an Adjunction — `l.825`
- **Proposition 21** (↑ ⊣ ↓ on the sub-categories) — `l.827`
- **Proposition 22** (D isomorphic to the duploid of its adjunction) —
  `l.840`
- §4.2 The Equalising Requirement — `l.849`
- **Definition 23** (equalising requirement) — `l.851`
- **Proposition 24** — `l.854`
- **Proposition 25** — `l.867`
- §4.3 Main Result — `l.877`
- **Definition 26** (pseudo map of adjunctions) — `l.880`
- **Definition 27** (the category `Adj`) — `l.897`
- **Theorem 28** (the reflection and the equivalence) — `l.899`
- §5 Ongoing Work — `l.909`
- References — `l.928`

The map covers all 28 numbered statements and all 18 section
headings. It also covers each unnumbered passage that a digest below
treats as an item of its own. It does not anchor every line a digest
cites. A digest may cite a line inside an anchored statement's own
body, such as `l.892-896` inside Definition 26. It may also cite a
one-line connecting sentence, such as `l.439`. The map is not a
paragraph-level content map, and it does not stand in for the
statement audit.

## Content digests

Statement-level, in the source's own notation, transcribed by the rule
below.

The alphabet. The source sets its duploid and its two categories in a
script alphabet: `𝒟`, `𝒞₁`, `𝒞₂`, `𝒫` and `𝒩`. This entry writes those
as `D`, `C1`, `C2`, `P` and `N`, so a digest and the extraction a reader
greps carry the same letters. A passage that quotes a page render shows
the source's own glyphs instead, and the over/underline table in Files
sets the two alphabets against each other in separate columns. A
subscript reaches a digest as `_` and a superscript as `^`. So the
source's `A⁺ →_𝒟 B⊖` on PDF page 9 is `A⁺ →_D B⊖` here, and its
`g ◦^𝒟 f` is `g ◦^D f`.

Notation key. Definition 1 (l.183-186) gives a composite of
`f ∈ D(A,B)` and `g ∈ D(B,C)` one general name and two further
notations. The choice among the two follows the polarity of the
**middle** object `B`, whatever the polarities of `A` and `C`: `g • f`
when `B` is positive, `g ◦ f` when `B` is negative. So `•` and `◦`
record the polarity of the object between the two morphisms. They do
not record which subcategory the composite lives in. Restricting `•`
to `P` and `◦` to `N` gives the two categories the source reads off
the polarity partition at l.224-228, which is a consequence of
Definition 1 rather than its statement. The paper writes the general
composite `g ⊙ f` with a ring that carries a filled dot at its center
(U+2299). The native extraction dropped that glyph everywhere. The
correction patch restores it (see Files). So the digests below write
`⊙` as the paper does. Order is applicative throughout: `f ⊙ g` means
"apply `g`, then `f`". Juxtaposition in a digest never means duploid
composition, which is always `⊙`, `•` or `◦`. Juxtaposition keeps its
standard category-theoretic readings. It means functor application, as
in `GFε` and in Theorem 28's `jiD`, or whiskering, as in `ψF`, or
functor composition, as in Definition 26's `F'H2` and `H1F`.

A second warning. The extraction flattens several two-column displays,
so line order in `duploids.pdftext` is not reading order at those
ranges. Files lists the ranges and says which of them a digest reads.
Every digest that reads one names the interleaving in its own text.

- **Pre-duploid** (Definition 1, l.180): a set of objects `|D|` with a
  polarity map `ϖ : |D| → {+, ⊖}`, hom-sets `D(A,B)`, a composition
  `g ⊙ f ∈ D(A,C)` for `f ∈ D(A,B)`, `g ∈ D(B,C)`, written `g • f` when
  `B` is positive and `g ◦ f` when `B` is negative, and identities.
  Three associativity laws hold, one per fixed polarity pattern on the
  middle two objects: `(••)` `(h•g)•f = h•(g•f)` over `A→P→Q→B`,
  `(◦◦)` `(h◦g)◦f = h◦(g◦f)` over `A→N→M→B`, `(•◦)` `(h•g)◦f =
  h•(g◦f)` over `A→N→P→B`. Left open: paths `A→P→N→B` need not
  associate.
- **Linear, thunkable** (Definition 2, l.233): `f` is linear when
  `f ⊙ (g ⊙ h) = (f ⊙ g) ⊙ h` for all `g,h`. `f` is thunkable when
  `h ⊙ (g ⊙ f) = (h ⊙ g) ⊙ f` for all `g,h`. Any `f : P → A`
  (positive source) is automatically
  linear, and any `f : A → N` (negative target) is automatically
  thunkable. Both classes are closed under composition and identity.
  The source borrows the term *thunkable* from `[16,8]` (l.244), which
  its reference list gives as Thielecke (l.957) and Führmann (l.943).
  It attributes only that one term.
- **Sub-categories** (Definition 3, l.246): `D_l`, `D_t` — linear,
  thunkable morphisms of `D`. `N_l` — linear morphisms of `N`. `P_t` —
  thunkable morphisms of `P`. `N`/`N_l` are the full subcategories of
  `D_t`/`D_l` restricted to negative objects. `P`/`P_t` are
  symmetrically the full subcategories of `D_l`/`D_t` restricted to
  positive objects.
- **Proposition 4** (l.257): the hom-sets of a pre-duploid extend to a
  (pro-)functor `D(−,=) : D_t^op × D_l → Set`, with
  `D(f,g)(h) = g ⊙ h ⊙ f` for `f ∈ D_t(A,B)`, `g ∈ D_l(C,D)`. The proof
  notes that restricting `f` to thunkable and `g` to linear is what
  makes the definition unambiguous. **Entry's reading, not the
  source's**: this is the profunctor that Proposition 19 works with.
  Proposition 19 states that the transformation
  `F : D(−,=) → D'(F_t−,F_l=)` is natural (l.774-775), which is a
  property of the transformation, not of the profunctor.
- **Thunk** (Definition 5, l.286, after Führmann): a functor `L : P →
  P` with a *natural* transformation `ε : L → 1` and a transformation
  `ϑ : 1 → L`, such that `ϑ_L : L → L²` is natural, satisfying
  `ε•ϑ = id`, `Lε•ϑ_L = id_L`, `ϑ_L•ϑ = Lϑ•ϑ`. A thunk induces a
  comonad `(L,ε,ϑ_L)`. A thunk-force category `(P,•,id,L,ϑ,ε)` builds a
  pre-duploid: positive objects are `P`'s objects, negative objects a
  disjoint copy `⇑|P|`, with Führmann's own "thunkable" (`Lf•ϑ_P =
  ϑ_Q•f`) recalled for comparison against Definition 2. `ϑ` is not
  natural in general (l.313), which is what leaves morphisms
  non-thunkable.
- **Proposition 6** (l.315): for the pre-duploid built from a
  thunk-force category, `f : P → Q` is thunkable in Führmann's sense
  iff thunkable per Definition 2. Corollary: `ϑ` is natural iff the
  pre-duploid is a category (`◦•`-associativity holds).
- **Duploid, first form** (Definition 7, l.418): a pre-duploid `D` with
  mappings `⇓ : |N|→|P|`, `⇑ : |P|→|N|` and, for all `P,N`, morphisms
  `delay_P : P→⇑P`, `force_P : ⇑P→P`, `wrap_N : N→⇓N`, `unwrap_N :
  ⇓N→N` satisfying `force_P◦(delay_P•f) = f` for all `f ∈ D(A,P)`,
  `(f◦unwrap_N)•wrap_N = f` for all `f ∈ D(N,A)`,
  `delay_P•force_P = id_⇑P`, `wrap_N◦unwrap_N = id_⇓N`. The source
  calls Definition 9 "the following equivalent definition" (l.439) and
  keeps using `delay` and `unwrap` afterward. (The source sets this
  definition as two side-by-side boxes, the left one holding the four
  typings and the right one the four equations. The extraction flattens
  that display at l.421-433, so read the digest, not the line order.
  A render of PDF page 8 confirms all eight items.)
- **Proposition 8** (l.434): for any `N`, `wrap_N` is thunkable, and
  dually for any `P`, `force_P` is linear. Proof (for `wrap_N`):
  `h◦(g•wrap_N) = (h◦(g•wrap_N)◦unwrap_N)•wrap_N =
  (h◦(g•wrap_N◦unwrap_N))•wrap_N = (h◦g)•wrap_N`, using
  `wrap_N◦unwrap_N = id_⇓N`. The derived equation is exactly
  Definition 2's thunkable shape (`h ⊙ (g ⊙ f) = (h ⊙ g) ⊙ f` with
  `f = wrap_N`). See
  Source errata for the proof's closing sentence. This proposition
  licenses Definition 9's simplification. The paper later extends the
  proposition to all objects `A` (l.703-704): `unwrap_A` and `wrap_A`
  are thunkable, and `delay_A` and `force_A` are linear.
- **Duploid** (Definition 9, l.440): "A duploid is a pre-duploid `D`
  given with mappings `⇓ : |N|→|P|` and `⇑ : |P|→|N|`, together with a
  family of invertible linear maps `force_P : ⇑P→P` and a family of
  invertible thunkable maps `wrap_N : N→⇓N`," introduced as "the
  following equivalent definition of a duploid" (l.439). The source
  states the equivalence and nothing more. **Entry's reading, not the
  source's**: the equivalence runs through Proposition 8, and
  `delay_P`, `unwrap_N` come back as `force_P⁻¹`, `wrap_N⁻¹`.
  `mmmm-classical-notions` credits "a slight variant of" this paper's
  duploid definition (`article.tex:1817`). That sentence names the
  paper, not Definition 7 or Definition 9, so which one it varies is
  open.
- **The duploid construction** (Proposition 10, l.576, from §3.2):
  given an adjunction `F ⊣ G : C1 → C2` with `♯ : C1(F−,=) → C2(−,G=)`
  natural, `♭ = ♯⁻¹`, negative objects `|C1|`, positive objects `|C2|`,
  `|D| ≝ |C1| ⊎ |C2|`, `D(A,B) ≝ C1(FA⁺, B⊖)` with `g ◦^D f ≝
  (g♯ ◦^{C2} f♯)♭`: this data is a pre-duploid. `••`-associativity is
  inherited from `C1`, `◦◦` from `♯`/`♭` mutually inverse, and `•◦`
  from naturality of `♯`/`♭`. The source defines the two superscripts in
  the same display (l.536-557), by four equations: `P⁺ ≝ P`, `P⊖ ≝ FP`,
  `N⁺ ≝ GN`, `N⊖ ≝ N`. **Entry's reading, not the source's**: `A⁺` names
  an object of `C2` and `A⊖` an object of `C1`, whatever the polarity of
  `A`, which is what makes `C1(FA⁺, B⊖)` a hom-set of `C1`. (The
  extraction flattens that display. It tears the boxed `A⁺ →_D B⊖`, the
  word `where` and the four equations into separate lines, and it drops
  a page number into the middle of them. A render of PDF page 9 confirms
  the four equations.)
- **Remark 11** (l.581-582): in that construction, `P` is the Kleisli
  category `(C2)_GF` of the monad `GF`, and `N` is the Kleisli
  category `(C1)_FG` of the comonad `FG`. The remark states those two
  identifications and nothing else.
- **The shifts of the constructed pre-duploid** (unnumbered,
  l.583-603): the passage that follows Remark 11 opens "The
  pre-duploid has shifts, defined as follows" (l.583) and then gives
  `⇑P ≝ FP`, `⇓N ≝ GN`, `delay_P ≝ id^{C1}_{FP}`,
  `force_P ≝ (id_{GFP})♭`, `wrap_N ≝ id^{C1}_{FGN}` and
  `unwrap_N ≝ (id_{GN})♭`. This is unnumbered prose, not part of
  Remark 11. (The source sets the first two definitions side by side on
  one row. The extraction flattens them at l.584-589, with the two `def`
  markers ahead of the equations they decorate. A render of PDF page 10
  confirms the pairing.)
- **Proposition 12** (l.607): every adjunction determines a duploid
  (Proposition 10 plus the shift data at l.583-603). The source states
  it as an immediate corollary with no separate proof.
- **Proposition 13, thunkability criterion** (l.614): in a duploid `D`,
  let `f ∈ D(A,P)`. Then `f` is thunkable iff
  `(wrap_⇑P◦delay_P)•f = wrap_⇑P◦(delay_P•f)`. Dually, let
  `f ∈ D(N,B)`. Then `f` is linear iff
  `f◦(unwrap_N•force_⇓N) = (f◦unwrap_N)•force_⇓N`.
- **Proposition 14, linearity criterion** (l.647): let
  `F ⊣_{(η,ε)} G : C1 → C2` be an adjunction, and consider the
  associated duploid `D`. Then `f ∈ D(N,A)` is linear iff
  `f◦ε_{FGN} = f◦FGε_N` **(in C1)**, and `f ∈ D(A,P)` is thunkable iff
  its transpose `f♯ ∈ C2(A⁺,GFP)` satisfies
  `η_{GFP}◦f♯ = GFη_P◦f♯` **(in C2)**. The two qualifiers are the
  source's own. They fix the `◦` in both equations as composition in a
  plain category, not as a duploid composite.
- **Corollary 15** (l.653): let `F ⊣_{(η,ε)} G : C1 → C2`. The
  associated duploid `D` is a category if and only if the adjunction
  is idempotent. The source defines *idempotent* in the sentence just
  above (l.650-652), by four equivalent statements: the multiplication
  of the associated monad is an isomorphism, or the co-multiplication
  of the associated comonad is an isomorphism, or `ε_GF = GFε`, or
  `η_FG = FGη`.
- **Proposition 16** (l.707): let `D` be a duploid. The assignments
  `⇑f ≝ delay_B ⊙ f ⊙ force_A` and `⇓f ≝ wrap_B ⊙ f ⊙ unwrap_A` define
  functors
  `⇑ : D_l → N_l` and `⇓ : D_t → P_t` taking part in adjoint
  equivalences `I ⊣_{(delay,force)} ⇑` and `I ⊣_{(wrap,unwrap)} ⇓`,
  with `I` the inclusions. Consumed by the proofs of Propositions 21
  and 22. (The extraction flattens this two-column display, so the
  `force_A` at l.718 belongs to `⇑f`, not to `⇓f`. The source forms
  are the ones that typecheck, since `force_A : ⇑A → A` and
  `unwrap_A : ⇓A → A` for every object `A` by the extension at
  l.664-704. That extension is two flattened displays as well. The
  shift table at l.666-689 sets the `⇓A`/`⇑A` cases in a left column
  against the `delay`/`force`/`wrap`/`unwrap` typings in a right one,
  and the four equations that fix the extension run in two columns at
  l.691-701. Renders of PDF page 11 confirm both.)
- **Proposition 17** (l.731): let `D` be a duploid. There are natural
  isomorphisms of profunctors
  `D_t(−, I⇑=) ≃ D(−,=) ≃ D_l(I⇓−, =) : D_t^op × D_l → Set`, with `I`
  the inferrable inclusions. Leaving the inclusions implicit gives the
  shift adjunctions. Consumed by the proof of Proposition 22.
- **Functor of pre-duploids** (Definition 18, l.768): a
  polarity-preserving `|F| : |D1|→|D2|` with `F_{A,B} : D1(A,B) →
  D2(FA,FB)` satisfying `F(id_A) = id_{FA}` and
  `F(g ⊙ f) = Fg ⊙ Ff` (l.769). A **functor of
  duploids** also sends `force_P` to a linear morphism and `wrap_N` to
  a thunkable morphism.
- **Proposition 19** (l.772): given duploids `D`, `D'` and a mapping
  `F` whose object part preserves polarities, together with mappings
  `F_{A,B} : D(A,B) → D'(FA,FB)` on morphisms, `F` is a functor of
  duploids iff it restricts to functors `F_t : D_t→D'_t`,
  `F_l : D_l→D'_l` such that the transformation
  `F : D(−,=) → D'(F_t−,F_l=)` is natural.
- **The category `Dupl`** (Definition 20, l.786): objects duploids,
  morphisms duploid functors (Definition 18).
- **Proposition 21** (l.827): let `D` be a duploid. Then `↑ : P_t→N_l`
  (the restriction of `⇑`) is left adjoint to `↓ : N_l→P_t` (the
  restriction of `⇓`), with unit `wrap_⇑◦delay` and co-unit
  `unwrap•force_⇓`.
- **Proposition 22** (l.840): `D` is isomorphic to the duploid
  constructed (Proposition 10 with the shift data at l.583-603) from
  the adjunction `↑ ⊣ ↓` of
  Proposition 21.
- **Equalising requirement** (Definition 23, l.851): an adjunction `F
  ⊣_{(η,ε)} G : C1 → C2` satisfies it when, for all `P ∈ |C2|`, `η_P`
  **is an equaliser of** `η_{GFP}` and `GFη_P`, and for all
  `N ∈ |C1|`, `ε_N` **is a co-equaliser of** `ε_{FGN}` and `FGε_N`.
  Here `P` and `N` range over the two categories of the adjunction.
  Definition 23 has no duploid, so they do not name polarities. The
  source states the
  universal property, not merely the equation. **Entry's reading, not
  the source's**: the universal property is what Proposition 24's
  factorizations use.
- **Proposition 24** (l.854): let `F ⊣_{(η,ε)} G : C1 → C2` be an
  adjunction, and consider the associated duploid `D`. The adjunction
  satisfies the equalising requirement iff, for all `A,P,N`, three
  conditions hold. (1) `ε_N` is epi and `η_P` is mono, equivalently `G`
  and `F` are faithful. (2) Every linear `f ∈ D(N,A)` is `g◦ε_N` for
  some `g ∈ C1(N,A⁻)`, equivalently the linear morphisms are in the
  image of `G` modulo the adjunction. (3) Every thunkable `f ∈ D(A,P)`
  is, modulo the adjunction, `η_P◦g` for some `g ∈ C2(A⁺,P)`,
  equivalently the thunkable morphisms are in the image of `F`.
- **Proposition 25** (l.867): let `D` be a duploid. The adjunction
  `↑ ⊣ ↓ : N_l → P_t` of Proposition 21 satisfies the equalising
  requirement.
- **Pseudo map of adjunctions** (Definition 26, l.880, after Jacobs):
  for adjunctions `F ⊣_{(η,ε)} G : C1 → C2` and
  `F' ⊣_{(η',ε')} G' : C1' → C2'`, a quadruple `(H1,H2,φ,ψ)` of
  functors `H1 : C1→C1'`, `H2 : C2→C2'` together with natural
  isomorphisms `φ : F'H2 → H1F` and `ψ : G'H1 → H2G`, such that `H1`
  and `H2` preserve `η` and `ε` up to isomorphism. The source writes
  both as arrows decorated with `≃` (l.888-892), so the direction is
  part of the statement. `φ_G⁻¹` in the next equation depends on it.
  The source states
  that condition as two equations (l.892-894):
  `H2η = ψF ◦ G'φ ◦ η'_{H2}` and `H1ε = ε'_{H1} ◦ F'ψ⁻¹ ◦ φ_G⁻¹`. Two
  pseudo maps compose as (l.895-896):
  `(H1',H2',φ',ψ') ◦ (H1,H2,φ,ψ) =
  (H1'H1, H2'H2, H1'φ ◦ φ'_{H2}, H2'ψ ◦ ψ'_{H1})`, which is what makes
  Definition 27 a category.
- **The category `Adj`** (Definition 27, l.897): adjunctions between
  locally small categories as objects, pseudo maps as morphisms.
  `Adj_eq` is the full subcategory satisfying the equalising
  requirement.
- **The reflection theorem** (Theorem 28, l.899): a reflection and
  equivalence `Dupl ≃ Adj_eq ◁ Adj`. `j : Adj → Dupl` is the duploid
  construction (Proposition 10 with the shift data at l.583-603).
  `i : Dupl → Adj_eq` sends
  a duploid to the adjunction `↑ ⊣ ↓` of Proposition 21 (in `Adj_eq`
  by Proposition 25). Proposition 22 gives `jiD ≃ D`. The paper states
  that the complete proof appears in the author's PhD thesis, Chapter
  II (l.902). It glosses `j` as completing values with all pure
  (thunkable) expressions and stacks with all linear evaluation
  contexts.

## What the source establishes

The paper introduces the **pre-duploid**: a category-like structure
whose objects carry a polarity, and whose composition associates in
every polarity pattern on the middle two objects except `+ → ⊖`. It
then introduces the **duploid**, a pre-duploid with shift operators
`⇑`, `⇓` and the four maps `delay`, `force`, `wrap`, `unwrap`. It
gives two equivalent presentations of that structure (Definition 7 and
Definition 9), a construction of a duploid from any adjunction
(Propositions 10 and 12), and criteria that read linearity and
thunkability back off the adjunction (Propositions 13 and 14).

The main result is the **structure theorem**: a reflection
`Dupl ◁ Adj`, where `Adj` is the category of adjunctions and pseudo
maps of adjunctions, and an equivalence `Dupl ≃ Adj_eq` cutting `Adj`
down to the adjunctions that satisfy the equalising requirement
(Theorem 28, with Propositions 21, 22, 24 and 25 supplying the parts).
The paper reads this as saying that every duploid comes from an
adjunction, and that the adjunctions so obtained are exactly those
whose unit and co-unit are equalisers and co-equalisers. Corollary 15
locates the classical case: the duploid of an adjunction is a category
exactly when the adjunction is idempotent, so associativity is what
idempotency buys.

The intended reading is semantic. The paper presents duploids as a
direct account of polarised evaluation order, and offers Girard's
correlation spaces, Blass games, and Melliès's Conway games as
pre-duploids or near-duploids that fail associativity (§2.2, §3.6). It
also characterizes Führmann's thunk-force categories as the duploids
whose `⇑` is bijective on objects, and categories with a runnable
monad as those whose `⇓` is bijective on objects (l.810-817).

The paper is a shortened version of Chapter II of the author's PhD
thesis, and it points at the thesis for the complete proof of the main
result (l.67, l.902). Everything recorded here is the source's own
content, stated in its own terms. Every mathematical claim is
CONJECTURED until machine-checked.
