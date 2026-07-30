# Statement audit: `resources/munch-maccagnoni-duploids`

An independent statement audit of the 29 Content digests in the entry
for Guillaume Munch-Maccagnoni, *Models of a Non-Associative
Composition*, FoSSaCS 2014 [1]. The audit re-derives every digest from
the primary source. It accepts no prior review's fidelity verdict.

## 1. Summary verdict

**29/29 CONFIRMED (digest-level), 2026-07-29, by Claude (Opus 5).**

The audit ran in two passes. The first pass found one drift. The
Theorem 28 digest transcribed the reflection symbol as `⊳`, where a 600
dpi render of PDF page 15 shows `◁` [1]. Section 5 gives the detail and
the one-character fix. That fix has landed. The second pass re-read
both corrected passages and re-derived the source character from the
PDF. Section 8 records that pass, and the tally above is its verdict.

Of the 29 confirmed digests, 22 are near-verbatim renderings and 7 are
faithful paraphrases. Section 3 marks each one. It also names what each
paraphrase compresses. The paraphrase count follows the sibling entry
`mmmm-classical-notions`, which counts an accurate paraphrase as
CONFIRMED [4].

All 28 Section-map anchors to numbered statements resolve to the line
that opens the statement. So do all 34 anchors to unnumbered passages
and section headings. Section 4 records one grep caveat and no anchor
faults.

Depth is **digest-level**, matching `mmmm-classical-notions` [4]. The
audit read every digest against the passage it cites in
`duploids.pdftext`. Where a digest's fidelity turns on a repaired or
drawn mark, the audit also read a direct render of the PDF page. Ten of
the sixteen pages were rendered in full at 200 dpi, and four regions at
600 dpi.

### Hash binding

The field binds two hashes:

```
@ a39faa7c / eb36ae85
```

The first prefix pins `duploids.pdf` (the frontmatter `sha256`). The
second pins `duploids.pdftext` (the frontmatter `secondary-sha256`).

The reasoning. `resources/README.md` names two events that void the
field. One is a re-fetch that changes `sha256`. The other is a
re-extraction, which covers applying or changing the correction patch
[2, l.55-57, l.107-112, l.130-133]. The contract then says the
`@ <hash>` binding is what makes the voiding mechanical [2,
l.132-133]. A binding to `sha256` alone cannot do that here. The patch
is editable text inside the entry, and the PDF stays byte-identical
under any patch change. So a PDF-only binding would survive an event
the contract voids. A binding to the extraction hash alone has the
opposite gap. It would miss a re-ingestion, and it would not name the
entry's canonical artifact, which the field's own wording calls for.
Naming both closes each gap. `just resources-verify` already reads both
frontmatter pairs against disk, so this needs no new machinery.

Prefix length is 8 hex, matching `kelly-maclane-conditions` and
`bentzen-naive-cubical` [5, 6]. Order follows the frontmatter:
canonical first, secondary second.

This entry is the first in the tree to pin its corrected extraction as
`secondary-sha256`. `kelly-maclane-conditions` also carries a tracked
correction patch. Its patch is a tracked file whose identity git holds,
so its field binds one hash [5]. Here the patch lives in the entry
prose. The extraction hash is therefore the only mechanical witness of
what the patch produced.

## 2. What the audit read

| Artifact | Identity | How the audit used it |
| --- | --- | --- |
| `duploids.pdf` | `a39faa7c…`, matches frontmatter | page renders, font object dumps |
| `duploids.pdftext` | `eb36ae85…`, matches frontmatter | line anchors, digest comparison |
| entry `README.md` | snapshot `10690063…` | the digest text under audit |

The entry file changed twice while this audit ran, from a concurrent
editor. The audit therefore reads a snapshot taken at 16:40 on
2026-07-29, kept at `outputs/.notes/duploids-entry-audit-snapshot.md`.
The snapshot's frontmatter, Section map and Content digests match the
file as first read. The concurrent edits added an "alphabet" paragraph
at the head of the digest section and rewrote parts of Files. No digest
bullet changed in substance.

A byte comparison at 16:46 confirms the binding. The Section map and
the Content digests sections of the live file are byte-identical to the
snapshot. The concurrent editor touched only Vetting and Files. So the
verdicts below apply to the live file as it stands.

The audit built a line-to-page map from 16 single-page `pdftotext`
runs. It grounds every page reference below:

| PDF page | Extraction lines | PDF page | Extraction lines |
| --- | --- | --- | --- |
| 1 | 1-23 | 9 | 457-556 |
| 2 | 24-68 | 10 | 557-630 |
| 3 | 69-150 | 11 | 631-706 |
| 4 | 151-200 | 12 | 707-781 |
| 5 | 201-273 | 13 | 782-831 |
| 6 | 274-330 | 14 | 832-874 |
| 7 | 331-405 | 15 | 875-927 |
| 8 | 406-456 | 16 | 928-975 |

Printed page *n* is PDF page *n+1*. Every page attribution in the
entry's patch tables agrees with this map.

## 3. Per-digest findings

### 1. Pre-duploid (Definition 1, `l.180`): CONFIRMED

`duploids.pdftext:180-221`, renders of PDF pages 4 and 5. Five items
match: the object set, the polarity map `ϖ : |D| → {+, ⊖}` (`l.181`),
the hom-sets (`l.182`), the composite `g ⊙ f` with its two polarity
notations (`l.183-186`), and the identities (`l.221`). The three
associativity laws match their labels, equations and diagram shapes:
`(••)` at `l.195-198`, `(◦◦)` at `l.213-216`, `(•◦)` at `l.217-220`.
The digest reads "Left open: paths `A→P→N→B` need not associate". That
matches `l.178-179`, "when the middle map has polarity + → ⊖". It also
matches `l.409-411`, "in general h ◦ (g • f) ≠ (h ◦ g) • f".

### 2. Linear, thunkable (Definition 2, `l.233`): CONFIRMED

`duploids.pdftext:233-245`, render of PDF page 5. Both equations match
verbatim after the patch. The two automatic cases match `l.243`.
Closure under composition and identity matches `l.244-245`. The digest
credits *thunkable* to `[16,8]`, matching `l.244`. The two reference
entries match `l.957` (Thielecke) and `l.943` (Führmann).

### 3. Sub-categories (Definition 3, `l.246`): CONFIRMED

`duploids.pdftext:246-256`, render of PDF page 5. The render shows the
four-row table. Row 1 reads out in full, and rows 2 to 4 use a ditto
rule. That is what the patch reconstructs at `l.249`, `l.250` and
`l.252`. Both closing observations match `l.254-256`, including which
of `D_t` and `D_l` each pair restricts.

### 4. Proposition 4 (`l.257`): CONFIRMED

`duploids.pdftext:257-264`, render of PDF page 5. The profunctor
signature, the two membership hypotheses and the action
`D(f,g)(h) = g ⊙ h ⊙ f` all match. The proof note matches `l.263`. The
digest marks its own commentary "Entry's reading, not the source's".
The Proposition 19 fact it cites matches `l.774-775`. The digest omits
the action's typing `D(f,g) : D(B,C) → D(A,D)` (`l.262`), which drops
nothing the statement needs.

### 5. Thunk (Definition 5, `l.286`): CONFIRMED (paraphrase)

`duploids.pdftext:286-313`, render of PDF page 6. Definition 5 proper
is near-verbatim. The functor, the natural `ε`, the plain `ϑ`, the
naturality of `ϑ_L` and all three equations match `l.286-290`. The
comonad remark matches `l.291`.

The paraphrase is the surrounding construction. The digest says that a
thunk-force category `(P,•,id,L,ϑ,ε)` builds a pre-duploid, matching
`l.292-296`, and it gives the object part. It carries neither the
composite `g ◦ f = g • Lf • ϑ_P` (`l.293`) nor the hom-set definition
`D(A,B) ≝ P(A̅, B̲)` (`l.300`, `l.307`). Führmann's own thunkable
condition matches `l.312-313`, and so does the reason `ϑ` fails
naturality.

### 6. Proposition 6 (`l.315`): CONFIRMED

`duploids.pdftext:315-317`, render of PDF page 6. The biconditional
matches verbatim. The consequence the digest labels "Corollary" matches
`l.316-317`. That includes the `◦•`-associativity name for the law
that fails.

### 7. Duploid, first form (Definition 7, `l.418`): CONFIRMED

`duploids.pdftext:418-433`, render of PDF page 8. The render shows two
side-by-side boxes. The left box carries four typings and the right box
four equations. All eight items match the digest, including both
universal quantifiers `(∀f ∈ D(A,P))` and `(∀f ∈ D(N,A))`. The
"following equivalent definition" quotation matches `l.439`. The
digest's interleaving note is correct. The extraction flattens the
display across `l.421-433`.

### 8. Proposition 8 (`l.434`): CONFIRMED

`duploids.pdftext:434-437`, render of PDF page 8. The statement and
the four-term proof chain match verbatim. The render confirms the
errata item the digest points at. The closing sentence reads "Hence
`wrap_N` is linear" where the proposition says thunkable. The
extension to all objects matches `l.703-704` and the render of PDF page
11.

### 9. Duploid (Definition 9, `l.440`): CONFIRMED

`duploids.pdftext:440-442`, render of PDF page 8. The digest quotes the
definition, and the quotation is exact. The "Entry's reading" marker
separates the commentary. The cross-entry claim checks out.
`mmmm-classical-notions/article.tex:1817` reads [3]:

```
At this stage, we are ready to recall (a slight variant of) the
definition of duploid from~\citet{munchduploids}.
```

That sentence names the paper and neither definition.

### 10. The duploid construction (Proposition 10, `l.576`): CONFIRMED (paraphrase)

`duploids.pdftext:514-579`, renders of PDF pages 9 and 10. Every stated
item matches. The adjunction and `♯`/`♭` match `l.514-515`. The
polarity convention matches `l.517-519`. `|D| ≝ |C1| ⊎ |C2|` matches
`l.559`, and `D(A,B) ≝ C1(FA⁺, B⊖)` matches `l.561`. The composite
`g ◦^D f ≝ (g♯ ◦^{C2} f♯)♭` matches `l.563`. The conclusion matches
`l.576`, and the three-part proof sketch matches `l.577-579`. The four
superscript equations match the render of PDF page 9, each with `≝`.

The paraphrase is twofold. First, the source's "••-associativity is
given" becomes "inherited from `C1`", which is a correct gloss rather
than a quotation. Second, the digest omits two items of the §3.2 setup
it otherwise reproduces. Those are "Positive composition is given by
the composition in `C1`" (`l.561-562`) and the identities
`id^D_P ≝ id^{C1}_{FP}`, `id^D_N ≝ (id^{C2}_{GN})♭` (`l.573-574`). The
interleaving note is correct, including the dropped page number at
`l.548`.

### 11. Remark 11 (`l.581-582`): CONFIRMED

`duploids.pdftext:581-582`, render of PDF page 10. Both Kleisli
identifications match, with the right monad and comonad on the right
category. The digest's claim that the remark says nothing else is
correct.

### 12. The shifts of the constructed pre-duploid (unnumbered, `l.583-603`): CONFIRMED

`duploids.pdftext:583-603`, render of PDF page 10. The opening sentence
quotation matches `l.583`. All six definitions match the render, each
with `≝`: `⇑P ≝ FP`, `⇓N ≝ GN`, `delay_P ≝ id^{C1}_{FP}`,
`force_P ≝ (id_{GFP})♭`, `wrap_N ≝ id^{C1}_{FGN}` and
`unwrap_N ≝ (id_{GN})♭`. The render also confirms two claims. The
passage sits as unnumbered prose after Remark 11, and the first two
definitions sit side by side on one row. The digest omits the hom-set
memberships and the `∈ C1(…)` annotations the source attaches to each
of the four morphisms. That changes no definition.

### 13. Proposition 12 (`l.607`): CONFIRMED (paraphrase)

`duploids.pdftext:606-607`, render of PDF page 10. The statement
matches. The digest expands the source's "as above" into "Proposition
10 plus the shift data at `l.583-603`". That is the correct referent.
The render confirms the lead-in "It is easy to see that:" and the
absence of a proof.

### 14. Proposition 13, thunkability criterion (`l.614`): CONFIRMED

`duploids.pdftext:614-620`, render of PDF page 10. Both directions,
both hypotheses and both equations match verbatim. So do the
subscripts `⇑P` and `⇓N`.

### 15. Proposition 14, linearity criterion (`l.647`): CONFIRMED

`duploids.pdftext:647-649`, render of PDF page 11. The hypothesis, both
biconditionals, the transpose's type `C2(A⁺,GFP)` and both equations
match verbatim. The render shows the two qualifiers "(in C1)" and
"(in C2)" as the source's own, which is what the digest claims.

### 16. Corollary 15 (`l.653`): CONFIRMED

`duploids.pdftext:650-654`, render of PDF page 11. The statement
matches verbatim. All four equivalent forms of *idempotent* match
`l.650-652`, in the source's order.

### 17. Proposition 16 (`l.707`): CONFIRMED

`duploids.pdftext:707-726`, render of PDF page 12. The render settles
the interleaving question the entry left open. The display sets
`⇑f ≝ delay_B ⊙ f ⊙ force_A` and `⇓f ≝ wrap_B ⊙ f ⊙ unwrap_A` side by
side on one row. So `force_A` at `l.718` does belong to `⇑f`, exactly
as the digest says.

Both functor typings, both adjoint equivalences and their
`(delay,force)` and `(wrap,unwrap)` labels match `l.724-726`. The
typing justification checks out. The render of PDF page 11 gives
`force_N ≝ id_N : ⇑N → N` and `unwrap_P ≝ id_P : ⇓P → P`, which extend
Definition 7's `force_P` and `unwrap_N` to every object. The two
consumers match `l.832` and `l.843`. One notation point sits below the
drift threshold. The digest writes `=` where the source writes `≝`, in
both assignments.

### 18. Proposition 17 (`l.731`): CONFIRMED (paraphrase)

`duploids.pdftext:731-735`, render of PDF page 12. The chain of natural
isomorphisms, its signature and the "inferrable" inclusions match
verbatim. The paraphrase is the last clause. The source draws two
adjunction diagrams, `D_t ⊣ D_l` and `N ⊣ P` (`l.736-758`). The digest
compresses both into "the shift adjunctions". The consumer matches
`l.843`.

### 19. Functor of pre-duploids (Definition 18, `l.768`): CONFIRMED

`duploids.pdftext:768-771`, render of PDF page 12. The object mapping,
the morphism mappings and both functor laws match. The source's second
sentence reads "F force_P is linear for all P ∈ |P1|, and F wrap_N is
thunkable for all N ∈ |N1|". The digest paraphrases it as sending each
map to a morphism of that class. The quantifiers stay readable from the
subscripts.

### 20. Proposition 19 (`l.772`): CONFIRMED

`duploids.pdftext:772-775`, render of PDF page 12. Every hypothesis and
the biconditional match. So do both restricted functors and the
naturality clause.

### 21. The category `Dupl` (Definition 20, `l.786`): CONFIRMED (paraphrase)

`duploids.pdftext:786-787`, render of PDF page 13. Objects and
morphisms match. The digest omits the source's identity notation `1_D`
(`l.787`). The pointer to Definition 18 is correct. That is where the
source defines a functor of duploids.

### 22. Proposition 21 (`l.827`): CONFIRMED

`duploids.pdftext:827-829`, render of PDF page 13. Both restrictions,
their directions, the adjunction, the unit `wrap_⇑◦delay` and the
co-unit `unwrap•force_⇓` all match verbatim.

### 23. Proposition 22 (`l.840`): CONFIRMED (paraphrase)

`duploids.pdftext:840-841`, render of PDF page 14. The isomorphism
matches. The digest makes two expansions. It reads the source's "the
above adjunction ↑ ⊣ ↓" as "of Proposition 21". It reads "the duploid
obtained from" as "constructed (Proposition 10 with the shift data)".
Both expansions name the right referent.

### 24. Equalising requirement (Definition 23, `l.851`): CONFIRMED

`duploids.pdftext:851-852`, render of PDF page 14. Both quantifier
ranges, `P ∈ |C2|` and `N ∈ |C1|`, match exactly. So do the equaliser
and co-equaliser pairs. The digest notes that the definition mentions
no duploid and so names no polarity. The render bears that out. The
digest marks its own reading.

### 25. Proposition 24 (`l.854`): CONFIRMED (paraphrase)

`duploids.pdftext:854-862`, render of PDF page 14. The hypothesis, the
biconditional and the quantifier "for all objects A, P, N" match. All
three conditions match in their operative clause. So do `g ∈ C1(N,A⁻)`
and `g ∈ C2(A⁺,P)`.

The paraphrase sits in the two "equivalently" glosses. The source reads
"all linear morphisms are **in** the image of G". It also reads "all
thunkable morphisms are **in** the image of F". The digest reads "are
the image of", which states equality where the source states
containment. The operative clause in front of each gloss carries the
condition, so the mathematics is right. Section 6 records a separate
observation about the source's `A⁻`.

### 26. Proposition 25 (`l.867`): CONFIRMED

`duploids.pdftext:867-868`, render of PDF page 14. The statement and
the annotation `↑ ⊣ ↓ : N_l → P_t` match verbatim. The digest's added
pointer to Proposition 21 names the adjunction the source means.

### 27. Pseudo map of adjunctions (Definition 26, `l.880`): CONFIRMED

`duploids.pdftext:880-896`, render of PDF page 15. Both adjunctions,
the quadruple, both functor typings and both natural isomorphisms
match. The directions `φ : F'H2 → H1F` and `ψ : G'H1 → H2G` are the
ones the render gives. The render confirms the `≃` decorations at
`l.888-892`.

Both preservation equations match `l.892-894` verbatim. That includes
the `φ_G⁻¹` whose exponent the extraction tears onto `l.893`. The
composition law matches `l.895-896` verbatim. The credit to Jacobs
matches `l.879`. The digest writes `ψF` for the source's `ψ_F`, which
its own notation key declares as whiskering.

### 28. The category `Adj` (Definition 27, `l.897`): CONFIRMED

`duploids.pdftext:897-898`, render of PDF page 15. Objects, morphisms
and the full subcategory `Adj_eq` match.

### 29. The reflection theorem (Theorem 28, `l.899`): CONFIRMED

`duploids.pdftext:899-905`, renders of PDF page 15 at 200 dpi, 600 dpi
and 2400 dpi.

Everything matches. `j : Adj → Dupl` as the
duploid construction matches `l.901`. So do `i : Dupl → Adj_eq` and
`jiD ≃ D` from Proposition 22. The thesis pointer matches `l.902`. The
gloss on `j` matches `l.903-905`. Its parenthetical "(thunkable)" for
the source's "pure" rests on `l.171-172`, where the paper describes the
same completion with the word "thunkable".

**The mark.** The displayed formula reads

```
Dupl ≃ Adj_eq ◁ Adj
```

Crops of PDF page 15 at 600 dpi and 2400 dpi both show the triangle
pointing **left**. The digest matches that at the second pass and not
at the first. Its earlier text read `⊳` (U+22B3), the mirror image of
the source's `◁`. The orientation of that mark is its content, because
it names which of the two categories reflects into the other. So the
earlier text substituted a notation that reverses a direction, which is
drift under the audit's rubric. The rest of the same digest fixed the
direction correctly all along, through `j` and `i`. Section 8.1 records
the corrected text and Section 8.2 the render.

The earlier text reproduced the extraction, which still reads `⊳` at
`l.900`. The extraction is not at fault. Section 5 traces the cause
into the PDF's own font maps.

## 4. Anchor resolution

No anchor faults. All 28 numbered-statement anchors resolve to the line
that opens the statement:

- Definition 1 `l.180`, Definition 2 `l.233`, Definition 3 `l.246`,
  Proposition 4 `l.257`, Definition 5 `l.286`, Proposition 6 `l.315`,
  Definition 7 `l.418`.
- Proposition 8 `l.434`, Definition 9 `l.440`, Proposition 10 `l.576`,
  Remark 11 `l.581`, Proposition 12 `l.607`, Proposition 13 `l.614`,
  Proposition 14 `l.647`.
- Corollary 15 `l.653`, Proposition 16 `l.707`, Proposition 17
  `l.731`, Definition 18 `l.768`, Proposition 19 `l.772`, Definition
  20 `l.786`, Proposition 21 `l.827`.
- Proposition 22 `l.840`, Definition 23 `l.851`, Proposition 24
  `l.854`, Proposition 25 `l.867`, Definition 26 `l.880`, Definition
  27 `l.897`, Theorem 28 `l.899`.

Two anchors point at a line the extraction split. `l.257` reads
"Proposition" with "4." on `l.258`. `l.731` reads "Proposition" with
"17." on `l.732`. Each is still the line that opens the statement, so
each resolves.

The 34 remaining Section-map anchors also resolve, checked line by
line. They cover the HAL cover page, the title, the abstract, all 18
section headings (the References heading among them), and ten
unnumbered passages. One of those passages carries a digest of its own,
the shift data at `l.583-603`. Three of them are ranges, so ten
passages give 13 anchors.

**One grep caveat.** `l.707` starts with a form feed, because PDF page
12 starts there. So `rg '^Proposition 16'` finds nothing, while
`rg 'Proposition 16'` finds the line. Any future mechanical anchor
check has to allow a leading `\f`. The anchor itself is correct.

## 5. The blockers the first pass found, and their resolution

Both blockers are closed. Section 8 records the checks that closed
them.

### 5.1 The Theorem 28 digest, and the entry's own summary

Two places in the entry write `⊳` where the render gives `◁`:

- The Theorem 28 digest, `Dupl ≃ Adj_eq ⊳ Adj`.
- The "What the source establishes" section, "a reflection
  `Dupl ⊳ Adj`". The render of PDF page 4 gives `Dupl ◁ Adj`.

The fix in both places is one character. `⊳` becomes `◁`. That edit has
landed in both places, and the second pass re-read both bullets against
a fresh render. So the tally is 29/29. Section 8.1 gives the corrected
text and Section 8.2 the render.

### 5.2 An undisclosed extraction defect, with its cause

The mirror flip is not a Poppler bug. The PDF's own `ToUnicode` maps
are wrong, in two fonts, in opposite directions:

| PDF objects | Font, code | Glyph name | `ToUnicode` says | The page shows |
| --- | --- | --- | --- | --- |
| 241, 240 | `rtxmi`, `0x2F` | `/triangleleft` | U+22B3 `⊳` | `◁` |
| 245, 244 | `txsya`, `0x42` | `/triangleright` | U+22B2 `⊲` | `▷` |

`pdftotext` follows each map faithfully, so the extraction inherits
both flips. These extraction lines carry a flipped mark:

- The reflection mark, render `◁`, extraction `⊳`: `l.154`, `l.900`.
- The rewrite relation, render `▷`, extraction `⊲`: `l.372`, `l.373`,
  `l.375`, `l.376`, `l.380`, `l.472`, `l.474`, `l.475`, `l.477`,
  `l.478`.

The entry's "What the patch does not repair" section lists eight
garbled symbol classes. It does not list this one. That section also
says "Every one of these sits in §2.3, in §3.1, or at the end of a
proof. No digest below reads any of them." Count this class, and both
halves of that sentence fail. `l.900` sits in §4.3, and the Theorem 28
digest reads it. The section needs a ninth row and a narrowed coverage
sentence.

The entry now carries a ninth-class paragraph and a narrowed coverage
sentence. Section 8.3 checks every factual claim in that paragraph
against the PDF's own objects.

A reader who greps the extraction for either triangle gets the wrong
one. That is a hazard for any future citation into §2.3 or §3.1, where
the rewrite relation carries the calculus.

## 6. Further observations, outside the tally

These change no digest verdict. Each one is an accuracy note a future
reader should have. The entry has since acted on items 1, 3 and 4.
Section 8.4 records the check on each of those three edits.

1. **The source's own notation slip at `l.858`.** Proposition 24
   condition 2 writes `g ∈ C1(N, A⁻)` with U+2212 MINUS. A 600 dpi crop
   of PDF page 14 confirms it. §3.2 defines the negative superscript as
   `A⊖` (`l.552-555`). The digest transcribes `A⁻` faithfully, so the
   digest is correct. The entry's Source errata section records two
   source inconsistencies and not this third one.

2. **The patch repairs marks no digest reads.** The six over/underline
   rules at `l.300` and `l.307` carry the hom-set definition
   `D(A,B) ≝ P(A̅, B̲)` with `P̅ = P̲ ≝ P`, `⇑̅P̅ ≝ LP` and `⇑̲P̲ ≝ P`.
   The Definition 5 digest is the only one that could read them, and it
   does not. A reader who wants the thunk-force pre-duploid has to open
   the render.

3. **Two `≝` marks in the Proposition 16 digest read `=`.** The ninth
   read fixed this class in the Proposition 10 digest and did not sweep
   Proposition 16.

4. **Two glosses in the Proposition 24 digest read "the image of"
   where the source reads "in the image of".** See Section 3, entry 25.

5. **The Proposition 10 digest omits the positive composition and the
   identities** (`l.561-562`, `l.573-574`). See Section 3, entry 10. A
   note for a formalizer: the identities and the shift data agree, since
   `id^D_P ≝ id^{C1}_{FP}` and `delay_P ≝ id^{C1}_{FP}`.

6. **The entry's page attributions are all correct.** Four tables carry
   page numbers: the `⊙` table, the ditto table, the over/underline
   table and the trailing-`⊙` pairing table. Every number agrees with
   the line-to-page map in Section 2. The `⊙` counts sum to 40 both by
   row and by page.

## 7. The field text

Paste this into the Vetting section:

```
Statements verified: 29/29 CONFIRMED (digest-level), 2026-07-29, by
Claude (Opus 5), @ a39faa7c / eb36ae85.
```

Two prefixes, because two files carry the audit. `a39faa7c` pins
`duploids.pdf` and `eb36ae85` pins `duploids.pdftext`. So a re-fetch
and a patch change each void the field mechanically. Section 8.5 gives
the recomputed hashes behind both prefixes.

The 29/29 form rests on the second pass of Section 8. That pass read
the corrected Theorem 28 bullet and the corrected summary sentence, and
it re-derived the source character from a fresh render. The entry
carries no `Statements verified:` field today, so this text adds one
rather than replacing one.

The one drift the first pass found was a transcription defect and not a
mathematical error. The entry now supports citing the paper's
statements at all 29 digests. That includes the Theorem 28 displayed
formula, alongside `j`, `i` and `jiD ≃ D`.

## 8. Follow-up: second pass, 2026-07-29

A second pass read the entry after the Section 5 and Section 6 fixes
landed. It re-derived every source character from the PDF rather
than reading the first pass's claim about them [1]. Verdict: **29/29
CONFIRMED (digest-level)**.

### 8.1 The corrected passages

Two passages carried the drift. Both now read `◁` (U+25C1):

- The Theorem 28 digest, `README.md:1049`, `Dupl ≃ Adj_eq ◁ Adj`.
- "What the source establishes", `README.md:1072`, `Dupl ◁ Adj`.

A line diff against the audited snapshot at
`outputs/.notes/duploids-entry-audit-snapshot.md` gives one changed
character in each passage. Nothing else in either passage moved. The
same diff covers the three smaller fixes of Section 8.4, and it shows
each of those confined to its own bullet.

A codepoint scan of the whole entry finds ten triangle characters. Eight
of them sit inside the extraction-defect paragraph of Section 8.3,
where the entry names both the source mark and the extraction's mirror
of it. The other two are the two above, and both are U+25C1. No U+22B3
survives outside that paragraph.

### 8.2 The source glyph, re-derived

Two renders made in this pass, both from `duploids.pdf` [1]:

- PDF page 15 at 600 dpi, the Theorem 28 display region. It reads
  `Dupl ≃ Adj_eq ◁ Adj`. A 2400 dpi crop of the mark alone puts the
  apex on the left.
- PDF page 4 at 1200 dpi, the `l.154` mark. It reads `◁`.

`pdftotext -bbox` places the page-15 mark at x 326.87 to 331.04 and y
338.98 to 348.63, in points. That box fixed the crop. So the source
shows `◁` in both places, and the entry now agrees with the page in
both places.

### 8.3 The ninth defect class

The entry's new paragraph at `README.md:580-599` states the mechanism,
the four PDF objects and the affected lines. Every claim in it holds
against the PDF's own objects [1]:

| The paragraph's claim | What the object shows |
| --- | --- |
| obj 241, font `rtxmi`, code `0x2F`, glyph `/triangleleft` | obj 241 is `/Type /Encoding` with `/Differences [... 47 /triangleleft ...]`. Font obj 196 is `/BaseFont /KKIRPW+rtxmi` and names `/Encoding 241 0 R` |
| obj 240 maps that code to U+22B3 | obj 240 is the `ToUnicode` CMap of font obj 196. Its `bfrange` reads `<2f><2f><22b3>` |
| obj 245, font `txsya`, code `0x42`, glyph `/triangleright` | obj 245 is `/Type /Encoding` with `/Differences [... 66 /triangleright ...]`. Font obj 198 is `/BaseFont /VBRUYU+txsya` and names `/Encoding 245 0 R` |
| obj 244 maps that code to U+22B2 | obj 244 is the `ToUnicode` CMap of font obj 198. Its `bfrange` reads `<42><42><22b2>` |

Each map inverts its own glyph name, and the two invert in opposite
directions. That is what the paragraph says.

The affected-line list is exact. A codepoint scan of `duploids.pdftext`
finds 12 triangle characters and no more. They sit at the 12 lines the
paragraph names, with U+22B3 at `l.154` and `l.900` and U+22B2 at the
ten rewrite-relation lines. A 1200 dpi crop of PDF page 7 shows the
`l.372` mark as `▷`, so the rewrite half of the claim holds as well as
the reflection half.

The narrowed coverage sentence holds too. `l.875` opens §4.3 and `l.900`
follows it. No digest and no Section-map anchor cites any of the ten
rewrite-relation lines. So the Theorem 28 digest is the only digest that
reads a flipped mark, which is what the paragraph claims.

### 8.4 The three smaller fixes

1. **Source errata, third item** (`README.md:228-233`).
   `duploids.pdftext:858` reads `g ∈ C1 (N, A− )` with U+2212, and a 600
   dpi crop of PDF page 14 shows that superscript minus. §3.2 sets the
   negative superscript at `duploids.pdftext:552` and `l.555`, as
   `P⊖ = F P` and `N⊖ = N`. `l.858` is the only line in the extraction
   that writes a polarity superscript with a minus. The section's
   lead-in moved from two inconsistencies to three, which the added
   bullet needs.
2. **Proposition 16, two `≝` marks** (`README.md:966`). A 600 dpi render
   of PDF page 12 sets `def` above `=` in both assignments. The same
   render puts the two displays side by side on one row, which the
   digest's own interleaving note already claimed.
3. **Proposition 24, "in the image of"** (`README.md:1022`, `l.1025`).
   `duploids.pdftext:859` reads "equivalently all linear morphisms are
   in the image of G modulo the adjunction". `l.861-862` reads "all
   thunkable morphisms are in the image of F". A 600 dpi crop of PDF
   page 14 confirms both. The digest now matches the source at both
   glosses. Section 3 entry 25 named those two glosses as the digest's
   paraphrase, so that part of the note no longer describes the entry.
   The second pass did not re-derive the near-verbatim and paraphrase
   split for this digest, so Section 1 keeps the first pass's label
   for it.

### 8.5 The hash binding, recomputed

`shasum -a 256` on the two artifacts, run in this pass:

- `duploids.pdf`: `a39faa7cfe1f882f…`, matching the frontmatter
  `sha256` at `README.md:3`.
- `duploids.pdftext`: `eb36ae85af65e85c…`, matching the frontmatter
  `secondary-sha256` at `README.md:11`.

So the prefix pair the Section 7 field names is still the pair on disk.
Neither artifact changed between the two passes.

## Sources

1. Guillaume Munch-Maccagnoni, *Models of a Non-Associative
   Composition*, FoSSaCS 2014, pp. 396-410,
   DOI 10.1007/978-3-642-54830-7_26, HAL Id hal-00996729 v1.
   Vendored at `resources/munch-maccagnoni-duploids/duploids.pdf`,
   sha256 `a39faa7c…`, and
   `resources/munch-maccagnoni-duploids/duploids.pdftext`, sha256
   `eb36ae85…`. Metadata page
   <https://inria.hal.science/hal-00996729v1>.
2. `resources/README.md`, the entry-format authority. Canonical source
   format at `l.29-64`. The Vetting contract at `l.114-141`.
3. `resources/mmmm-classical-notions/article.tex:1817`, the sibling
   entry's duploid credit.
4. `resources/mmmm-classical-notions/README.md:58-59`, the
   digest-level field this audit's depth follows.
5. `resources/kelly-maclane-conditions/README.md:57-64`, an earlier
   entry with a tracked correction patch and a one-hash binding.
6. `resources/bentzen-naive-cubical/README.md:61-62`, an 8-hex prefix
   precedent.

## Verification Record

Every command ran on 2026-07-29 from
`/Users/lane/kitcat/resources/munch-maccagnoni-duploids`, unless the
command names another path.

### Identity checks

| Command | Outcome |
| --- | --- |
| `shasum -a 256 duploids.pdf duploids.pdftext` | PASS. Both match the frontmatter `sha256` and `secondary-sha256`. |
| `wc -l duploids.pdftext` | 975 lines, matching the Files section. |
| `pdftotext -v` | `pdftotext version 26.06.0`, matching the pinned Poppler. |
| `pdfinfo duploids.pdf` | 16 pages, A4, Producer PDFLaTeX. |
| `shasum -a 256 outputs/.notes/duploids-entry-audit-snapshot.md` | `10690063…`, the audited entry text. |

### Source reads

| Command | What it established |
| --- | --- |
| `for n in $(seq 1 16); do pdftotext -f $n -l $n duploids.pdf p$n.txt; done` | The line-to-page map in Section 2. |
| `rg -n '^(Definition\|Proposition\|Corollary\|Theorem\|Remark\|Lemma)' duploids.pdftext` | 27 of 28 statement openers. `l.707` missed on the form feed. |
| `sed -n '707p' duploids.pdftext \| od -c` | `\f` at byte 0 of `l.707`. The anchor resolves. |
| `pdftoppm -png -r 200 -f N -l N` for N in 5, 6, 8 to 15 | Ten full-page renders, read for digests 1 to 29. |
| `pdftoppm -png -r 600` with `-x -y -W -H` on pages 4, 7, 14, 15 | Four crops: both reflection marks, the rewrite relation, `A⁻`. |
| `rg -n '⊳\|⊲\|◁\|▷' duploids.pdftext` | 12 occurrences, all listed in Section 5.2. |
| Python and `zlib` dumps of PDF objects 240, 241, 244, 245 | The two wrong `ToUnicode` entries in Section 5.2. |
| `sed -n '1815,1820p' ../mmmm-classical-notions/article.tex` | The `article.tex:1817` credit. |

### Anchor audit

- 28 numbered-statement anchors: 28 confirmed, 0 dead, 0 stale.
- 34 further Section-map anchors: 34 confirmed, 0 dead, 0 stale.
- 1 grep caveat, at `l.707`. Not an anchor fault.

### Digest audit

- 29 digests read. First pass: 21 CONFIRMED, 7 CONFIRMED (paraphrase),
  1 NOT CONFIRMED. The one NOT CONFIRMED was Theorem 28's displayed
  formula.
- Second pass: Theorem 28 re-read and CONFIRMED. Final tally 22
  CONFIRMED, 7 CONFIRMED (paraphrase), 0 NOT CONFIRMED.

### Second pass, 2026-07-29

Commands run from `/Users/lane/kitcat`, or from the entry directory
where the command names a bare artifact.

| Command | Outcome |
| --- | --- |
| `shasum -a 256 duploids.pdf duploids.pdftext README.md` | `a39faa7c…` and `eb36ae85…` unchanged. Entry `6cdfde5f…`. |
| `rg -n 'sha256\|secondary-sha256' README.md` | Both prefixes match the frontmatter at `l.3` and `l.11`. |
| `diff -u outputs/.notes/duploids-entry-audit-snapshot.md resources/munch-maccagnoni-duploids/README.md` | One character changed in each of the two triangle passages. The three smaller fixes each confined to their own bullet. |
| Python codepoint scan of `README.md` | Ten triangle characters. Two outside the defect paragraph, both U+25C1. |
| `pdftoppm -png -r 600 -f 15 -l 15 -x 2100 -y 2750 -W 900 -H 210` | `Dupl ≃ Adj_eq ◁ Adj`. |
| `pdftoppm -png -r 2400 -f 15 -l 15 -x 10870 -y 11290 -W 200 -H 200` | The page-15 mark, apex on the left. |
| `pdftoppm -png -r 1200 -f 4 -l 4 -x 6220 -y 2900 -W 160 -H 190` | The `l.154` mark, `◁`. |
| `pdftoppm -png -r 1200 -f 7 -l 7 -x 4110 -y 7590 -W 170 -H 140` | The `l.372` mark, `▷`. |
| `pdftoppm -png -r 600 -f 12 -l 12 -x 1400 -y 1100 -W 2400 -H 200` | Both Proposition 16 assignments, `def` above `=`, side by side. |
| `pdftoppm -png -r 600 -f 14 -l 14 -x 1100 -y 4270 -W 2900 -H 290` | Proposition 24 condition 2, "in the image of G", with `A⁻`. |
| `pdftotext -bbox -f N -l N` for N in 4, 7, 12, 14, 15 | The word boxes that fixed every crop above. |
| Python regex and `zlib` dump of PDF objects 240, 241, 244, 245 | The four object bodies in the Section 8.3 table. |
| Python scan of font dictionaries referencing those objects | Font obj 196 is `rtxmi`, font obj 198 is `txsya`. |
| `pdffonts duploids.pdf` | `KKIRPW+rtxmi` at obj 196, `VBRUYU+txsya` at obj 198. |
| Python codepoint scan of `duploids.pdftext` | 12 triangle characters, at exactly the 12 lines the entry names. |
| `rg -n 'l\.37[0-9]\|l\.47[0-9]\|l\.380\|l\.154' README.md` | Only the defect paragraph cites those lines. No digest does. |
| `rg -n 'Statements verified' README.md` | The entry carries no field yet. |

### Kernel layer

Not applicable. This audit makes no claim about any formal artifact. It
runs no proof checker and names no declaration. The audit read and
wrote no module, so `just check` had nothing to run against.

### Prose gate

`python3 .claude/skills/writing/prose-lint.py
outputs/duploids-entry-audit.md --max-per100 2.0`. Before the second
pass edits, 3893 words at 0.74 per 100 words. After them, 5071 words at
0.89 per 100 words, 0 em dashes, exit 0.

### Scope

The audit covers the 29 Content digests and the 62 Section-map anchors.
Four things sit outside it: the Files section's drawn-mark counts, the
correction patch hunk by hunk, the Source errata section, and the "What
the source establishes" section. Sections 5, 6 and 8 name the specific
claims in those parts that the audit did check.
