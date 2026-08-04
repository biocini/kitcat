---
artifact: kraus-infty-cwf.tar.gz
sha256: caddd47bf988eba1898f2368d0858a9adc19bba2cc035d24a5680d647493b71e
format: latex-source
fetch-url: https://arxiv.org/e-print/2009.01883
metadata-url: https://arxiv.org/abs/2009.01883
doi: 10.48550/arXiv.2009.01883
version: v2
fetched: 2026-08-03
sha256-inner: 35b5788a43c2eddd8ae05c80f3b7ea3da057677ec99d3b8f8272646f524315e7
secondary-artifact: Identities.agda
secondary-sha256: 31db662a4dd8a986fe7f49db95f0a4e6d5f2cd9de8e5f4bcaef79f494910ccfa
---

# Kraus — Internal ∞-Categorical Models of Dependent Type Theory

A definition of $\infty$-categories with families ($\infty$-CwF's) in
homotopy type theory, built to serve as models of dependent type
theory without assuming unique identity proofs. The paper's §5.2
introduces **identities via idempotent equivalences**: a morphism
counts as an identity when it is both an equivalence and idempotent,
replacing the usual posited-neutral-element definition; "having such
an identity at every object" is then proved a *proposition*, not
data, with no set-truncation hypothesis on the hom-family. The
development is supplemented by an Agda formalisation, a separate
GitHub repository the paper cites by footnote — vendored here
alongside the paper as a secondary artifact (see Files).

Load declaration: full statement depth over §5.2 ("Contexts and
substitutions, second part: identities", the identities-via-
idempotent-equivalences development) and its companion Agda file.
The rest of the paper ($\infty$-CwF's proper, semi-Segal contexts,
2LTT, the example models) is mapped at outline depth only.

## Citation

Nicolai Kraus. *Internal ∞-Categorical Models of Dependent Type
Theory: Towards 2LTT Eating HoTT*. arXiv:2009.01883 [cs.LO]
(cross-listed math.CT, math.LO), v2, 30 January 2021 (v1: 3 September
2020, 33 pages). <https://arxiv.org/abs/2009.01883>. Published as:
*Internal ∞-categorical models of dependent type theory*, Proceedings
of the 36th Annual ACM/IEEE Symposium on Logic in Computer Science
(LICS 2021), DOI
[10.1109/LICS52264.2021.9470667](https://doi.org/10.1109/LICS52264.2021.9470667)
(the vendored artifact is the arXiv e-print; it has not been diffed
against the LICS proceedings version).

Companion Agda formalisation, cited by the paper itself (`notes.tex`
l.203–204, footnote to §1's "Agda formalisation" paragraph): Nicolai
Kraus. *idempotentEquivalences* [Agda source, `--without-K`, built
against Andrew Swan's Agda-2.6.1-compatible fork of HoTT-Agda].
GitHub repository `nicolaikraus/idempotentEquivalences`, commit
`b702156` (2021-01-28, the repository's HEAD as of this ingestion — no
commits since). <https://github.com/nicolaikraus/idempotentEquivalences>.
A rendered HTML version is also linked from the same footnote:
<https://nicolaikraus.github.io/docs/html-idempotentequivalences/Identities.html>
(not vendored — a browsable view of the same source, not a distinct
artifact).

## Vetting

PROVISIONAL. Ingested 2026-08-03 by Claude (Sonnet 5) at Lane's
direction. The arXiv e-print was fetched by stable identifier
(`https://arxiv.org/e-print/2009.01883`, the unversioned URL, which
the submission history confirms currently serves v2 — the abs page
lists exactly two versions, `[v1] Thu, 3 Sep 2020` and `[v2] Sat, 30
Jan 2021`, and the tarball's internal file mtimes, 30 Jan 2021, agree)
and re-fetched independently a second time in the same session; both
fetches hashed identically (frontmatter `sha256`). The companion
repository's HEAD commit was checked against the GitHub API
(`GET /repos/nicolaikraus/idempotentEquivalences/commits/master`)
twice in the same session, both times returning `b702156…`, and the
repository's `pushed_at` (2021-01-28) predates the ingestion by years
with no intervening activity, so the commit pin is not a moving
target. The commit-pinned `Identities.agda` fetch was byte-compared
against the copy already sitting untracked at this ingestion, and the
two are identical. §5.2 (`notes.tex` l.772–928, load-bearing) was read
in full from the extracted `.tex`; the surrounding sections were
skimmed for the outline map only.

Statements verified: 23/30 CONFIRMED (statement-level), 7 CORRECTED,
2026-08-03, by verifier (Claude, Opus), @ caddd47b.

The audit read the §5.2 full map and the Content digests against
`notes.tex` and `Identities.agda`, one statement per anchored claim.
Four corrections fix line anchors. The four-levels and
Agda-formalisation passage sits at `l.813–816`, and so does the
wild-semicategory translation. The *neutral morphism* cross-reference
sits at `l.821`. The Agda module `I` spans `l.298–339`.

Three corrections fix paraphrases. The `l.911–914` sentence names two
horns, each with a contractible type of fillers. Both sources deny
that `is-idpt+eqv` is a proposition, and the Agda file gives the `S¹`
counterexample. `hasGoodIdStruc` matches `is-good-category` only up to
the order of the two conjuncts. A spot check of the outline map found
one more error: §5 carries `\label{sec:highercwf}` at `l.695`.

Two items stayed flagged rather than fixed, both outside the audit's
scope (header, Load declaration, Files). Fixed by the lead the same
day: every "§4.2" naming the identities subsection is now "§5.2"
(header, Load declaration, the paragraph above, and the Section map's
outline intro and depth note), the Vetting paragraph's own range for
that subsection corrected `l.694–928` → `l.772–928` to match, and the
Files line count corrected `445 lines` → `444 lines`.

## Files

Canonical format: **LaTeX source** (the arXiv e-print, v2). All
vendored and derived forms are gitignored (including the companion
`.agda` files, a newly-added `.gitignore` pattern — the first
GitHub-sourced vendoring in this tree); only this README is tracked.

- `kraus-infty-cwf.tar.gz` — the canonical artifact:
  the arXiv e-print tarball. This is the file the frontmatter's
  canonical `sha256` is of. Contains `arxiv.tex` (the compiled
  document, `\input`s the rest), `abstract.tex`, `header.tex`
  (macros), `notes.tex` (the paper body, 1498 lines — **the file the
  reader greps**; all line anchors below index into it),
  `figure-GAT-order-single.tex` (one TikZ figure), and `arxiv.bbl`
  (the bibliography).
- `Identities.agda` — the companion Agda formalisation, the
  **secondary artifact** (frontmatter `secondary-artifact` /
  `secondary-sha256`), fetched commit-pinned:
  `https://raw.githubusercontent.com/nicolaikraus/idempotentEquivalences/b702156f180a6a853458c8985f558d4b91e83a3a/Identities.agda`.
  444 lines. Defines `SemiCategory` (a wild semicategory — no
  set-truncation on `Hom`) and, for a fixed such category: `is-idpt`,
  `is-eqv`, `is-idpt+eqv`, `is-standard-id`, `is-standard-category`,
  `is-good-category`, the biimplection `idpt+eqv⇔std`, the
  uniqueness lemma `idpt+eqv-unique`, `eqv-2-out-of-3`, the `I(e)`
  construction (module `I`), `e-vs-I.e-I-idpt`, module `unique`
  (`unique-idpt+eqv`, contractibility), and the top-level theorems
  `good-iff-standard` and `goodness-is-prop`. Opens `HoTT` (Andrew
  Swan's Agda-2.6.1-compatible fork of the HoTT-Agda library,
  `awswan/HoTT-Agda@agda-2.6.1-compatible` — a build dependency, not
  itself vendored here) and `Iff`, both `public`.
- `Iff.agda` — a companion file `Identities.agda` imports, fetched
  commit-pinned at the same commit
  (`https://raw.githubusercontent.com/nicolaikraus/idempotentEquivalences/b702156f180a6a853458c8985f558d4b91e83a3a/Iff.agda`).
  6 lines of content: opens `lib.Base` and `lib.types.Sigma` (from
  HoTT-Agda) and defines `_⇔_ : Set j₁ → Set j₂ → Set (lmax j₁ j₂)`
  as `(A → B) × (B → A)`. Not tracked by a frontmatter hash pair (the
  schema carries one secondary-artifact pair; this file has no
  independent mathematical content beyond the one notation it
  defines, quoted here in full) — sha256
  `11290d427dffa7767ffaa5c08911ad294190c6be9019d7cae634b36c76444a28`,
  recorded for manual re-verification.

## Source provenance

The paper: fetched directly from arXiv by stable identifier
(`curl -L https://arxiv.org/e-print/2009.01883`); the hash was
checked stable across two independent fetches in the same session
(see Vetting). Version pin v2, the version the unversioned e-print
URL currently serves and the only version whose submission-history
timestamp matches the tarball's internal file dates.

The companion Agda source: GitHub has no e-print-style "version" —
the vendoring analogy adopted here (the first GitHub-sourced entry in
this tree) is to pin by **commit SHA**, the repository's immutable
content identifier, exactly as an arXiv version pin fixes a
snapshot. `Identities.agda` and `Iff.agda` were fetched from
`raw.githubusercontent.com` at commit `b702156f180a6a853458c8985f558d4b91e83a3a`
(the `master` branch's HEAD, confirmed via the GitHub REST API — see
Vetting), rather than from an unpinned branch URL, so a re-fetch of
this entry's `fetch-url` analogue for the secondary artifact is
mechanical from the commit SHA recorded here and in Files. The
repository carries no LICENSE file (`GET .../license` → 404); this
does not bear on citation, only on any future redistribution
decision, which this entry does not make. The repository's own
`README.md` (not separately vendored — its four lines are quoted here
in full since that is all of its content): "This repository contains
a small Agda implementation of idempotent equivalences, as suggested
in my paper Internal ∞-Categorical Models of Dependent Type Theory:
Towards 2LTT Eating HoTT. The file Identities.agda contains
information on the Agda version and dependencies." — confirming the
paper/repository linkage independently of the paper's own footnote.

## Section map

Line anchors are into `notes.tex` (the extracted paper body); jump
with `sed -n 'A,Bp' notes.tex`. Outline depth for background
sections; full depth for §5.2 (marked below).

**Outline** (§ numbers are the paper's own):
- §1 Introduction: Formalising Type Theory — `l.1–205`. The
  Agda-formalisation footnote (companion-repo citation) is
  `l.202–204`.
- §2 CwF's: 1-Categorical Models of DTT — `l.206–357`
  (`sec:tt-in-tt`; §2.1 Motivation `l.208`, §2.2 CwF's as GATs
  `l.244`, §2.3 Examples `l.287`).
- §3 Challenges in Type Theory without UIP — `l.358–492`
  (`sec:challenges`; §3.1 Deficiency of Truncated Structure `l.372`,
  §3.2 Deficiency of Wild/Incoherent Structure `l.409`).
- §4 Infinite Structures in Type Theory — `l.493–693`
  (`sec:infstrucs`; §4.1 Semisimplicial Types `l.510`, §4.2
  Two-Level Type Theory `l.622` — the paper's own §4.2, not to be
  confused with the load-bearing identities subsection, which is
  §5.2; see the next item).
- §5 Higher Dimensional Categories and Internal ∞-CwF's —
  `l.694–1153` (`\label{sec:highercwf}` at `l.695`; §5.1 Contexts
  and substitutions,
  first part: semi-Segal types, `l.699`; **§5.2 Contexts and
  substitutions, second part: identities, `l.772–928` — LOAD-BEARING,
  full depth below**; §5.3 The empty context: a terminal object
  `l.929`; §5.4 Types: a presheaf `l.938`; §5.5 Terms: diagrams over
  a category of elements `l.1004`; §5.6 Context extension `l.1096`).
- §6 Examples of ∞-Categories with Families — `l.1154–1321`
  (`sec:examples-of-iCwF`; §6.1 The Syntax as a QIIT `l.1156`; §6.2
  The Initial Model as a HIIT `l.1168`; §6.3 Higher Models from
  Strict Models and the Standard Interpretation `l.1238`; §6.4
  Slicing in ∞-CwF's `l.1298`).
- §7 Variations: Set-Based, Univalent, and Finite-Dimensional Models
  — `l.1322–1476` (`sec:variations`; §7.1 Set-Based ∞-CwF's `l.1327`;
  §7.2 Univalent ∞-CwF's `l.1369`; §7.3 Finite-Dimensional Models
  `l.1407`).
- §8 Open Problems and Future Directions — `l.1477–1498` (end of
  file; acknowledgements are in `arxiv.tex`, not `notes.tex`).

**§5.2 full map** (`l.772–928`, "Contexts and substitutions, second
part: identities", `\label{subsec:identities}` at `l.773`):
- `l.775–791` — the three design conditions an identity-property must
  satisfy: (1) recover naive two-sided-neutral identities per object;
  (2) be a *proposition* (an $\infty$-semicategory is an
  $\infty$-category in at most one way); (3) not force univalence
  (contexts of the syntactic model must not be forced to a set).
- `l.793–812` — situating the definition against prior approaches
  (Rourke's non-constructive extension result; Lurie/Harpaz's
  semisimplicial-space horn-filling condition, translated to
  "complete semi-Segal types"; Sattler–Kraus and Kock's infinite-tower
  alternatives) and the "dunce's hat" motivating analogy (contractible
  but not collapsible — not of the form $\Sigma(a{:}A).\,a=a_0$).
  `l.813–816`: the whole §5.2 development needs only the first four
  semisimplicial levels $(A_0,A_1,A_2,A_3)$, phrased in wild-semicategory
  language `(\ob,\hom,\mc,\ass)` with **no set-truncation**, and is
  "completely formalised in Agda" (cross-ref to the footnote at
  `l.202–204`).
- `l.819–836` **Definition** (identities via idempotent equivalences,
  unlabelled): in a wild semicategory, `iseqv(e)` for
  `e : hom(x,y)` means both `(- ⋄ e) : hom(y,z) → hom(x,z)` and
  `(e ⋄ -) : hom(w,x) → hom(w,y)` are equivalences of types (`l.821–827`,
  the two composition maps as an `align` block); `f : hom(x,x)` is
  *idempotent* if `f ⋄ f = f` (`l.828`); `i : hom(x,x)` is a *good
  identity* if it is an equivalence and idempotent (`l.829`); the
  semicategory has a **good identity structure** if
  `hasGoodIdStruc(C) :≡ Π(x:ob). Σ(i:hom(x,x)). iseqv(i) × (i⋄i=i)`
  (`l.833–835`).
- `l.838–841` — Remark: "being an equivalence" is propositional,
  "being idempotent" and "being a good identity" are data; the
  section's non-trivial result is that *having* a good identity
  structure is nonetheless propositional.
- `l.843–848` **Lemma** `\label{lem:id-characterisation}` — `i` is a
  good identity iff, for all `f : hom(w,x)` and `g : hom(x,z)`,
  `i⋄f = f` and `g⋄i = g`. Proof `l.849–855`: idempotence plus
  applying `(i⋄-)⁻¹`/`(-⋄i)⁻¹` gives the forward direction; the
  converse is immediate (two-sided-neutral ⇒ equivalence and
  idempotent).
- `l.857–859` **Corollary** `\label{cor:only-one-id}` — if
  `i₁, i₂ : hom(x,x)` are both good identities, `i₁ = i₂`.
- `l.861–863` — remark: Lemma `lem:id-characterisation` states
  "functions in both directions," **not** an equivalence of types
  (contrasted with the naive/coherence-broken characterisation from
  an earlier example); the definition via idempotent equivalences is
  "fully coherent."
- `l.865–867` **Theorem** `\label{thm:id-struc-is-prop}` — for a
  semicategory $\CC$, `hasGoodIdStruc(C)` is a proposition.
- `l.869–875` — the auxiliary construction: for an equivalence
  `e : hom(x,y)`, `I(e) := (e⋄-)⁻¹(e) : hom(x,x)` (`\label{eq:I-def}`
  at `l.871`); attributed to Harpaz and to Capriotti–Kraus as how
  identities are built when enough equivalences are already given.
- `l.876–878` **Lemma** `\label{lem:I-is-id}` — for any equivalence
  `e : hom(x,y)`, `I(e)` is a good identity. Proof `l.879–888`:
  idempotence by a four-step calculation setting `f := I(e)`;
  equivalence by 2-out-of-3 (cited, not re-derived in this excerpt)
  applied to `e⋄I(e) = e`.
- `l.890–895` **Lemma** `\label{lem:e-I-idem}` — for an equivalence
  `e : hom(x,x)`, `(e = I(e)) ≃ (e⋄e = e)` (`\label{eq:e-Ie}` at
  `l.892`). Proof `l.896–898`: the equivalence is `ap` along `(e⋄-)`.
- `l.901–909` — Proof of `thm:id-struc-is-prop` (transition sentence
  at `l.900`): fix `x`, reduce by
  function extensionality to propositionality of
  `Σ(i:hom(x,x)). iseqv(i) × (i⋄i=i)`; given `(i₀,p,q)`, chase an
  equivalence chain — by Lemma `lem:e-I-idem`, then by Corollary
  `cor:only-one-id` + Lemma `lem:I-is-id` — down to
  `Σ(i:hom(x,x)). iseqv(i) × (i=i₀)`, contractible with centre
  `(i₀,p,refl)`.
- `l.911–914` — the semi-Segal-type phrasing: an edge `e : A₁ x y` is
  an equivalence when each of the two horns `1 ←e 0 → 2` and
  `0 → 2 ←e 1` has a contractible type of fillers; a proof that
  `f : A₁ x x` is idempotent is an element of `A₂ f f f`.
- `l.916–918` **Definition** `\label{def:infcategory}` — an
  $\infty$-category is an $\infty$-semicategory with a good identity
  structure. `l.920–922`: from here on the paper drops "good" and
  just says "identity" (justified by Lemma `id-characterisation`:
  every identity is good).
- `l.924–927` — closing remark: "being a good identity" is equivalent
  to "being left- and right-neutral" **when `hom` is a family of
  sets** — so the usual (pre-)category definition (Ahrens–Kapulkin–
  Shulman) can equivalently use good identities. Contrast with Files:
  the vendored `Identities.agda` proves `good-iff-standard`
  unconditionally, with no `is-set` hypothesis appearing anywhere in
  `SemiCategory` or the surrounding module — this remark's set
  restriction is not read as a precondition the Agda development
  needs for the biimplication itself.

## Content digests

Statement-level, cross-referenced to `Identities.agda` (l.NNN) by
identifier. Every claim below is CONJECTURED until machine-checked in
this repository; the Agda file's own status (checked against Agda
2.6.1 + the pinned HoTT-Agda fork, per its header) is the source's
own claim, not re-verified here.

- **`iseqv`/`is-eqv`** (paper `l.821–827`; `Identities.agda:111–113`)
  — both composition maps equivalences of types. The paper calls this
  property *neutral morphism* in the companion
  Capriotti–Kraus paper (`l.821`, cross-reference, not vendored in
  this entry — see `resources/capriotti-kraus-semi-segal/`).
- **`idempotent`/`is-idpt`** (paper `l.828`; `Identities.agda:104–105`)
  — `f ⋄ f = f`; the paper and the Agda file agree this need not be
  propositional (`Hom x x` need not be a set).
- **good identity / `is-idpt+eqv`** (paper `l.829`;
  `Identities.agda:119–120`) — equivalence and idempotent together.
  Both sources state this conjunction is data, not a proposition. The
  paper calls "being a good identity" data (`l.839`). The Agda file
  gives a counterexample (`Identities.agda:122–126`): in the wild
  semicategory of types and functions, the identity on `S¹` is an
  idempotent equivalence in ℤ-many ways.
- **`hasGoodIdStruc`/`is-good-category`** (paper `l.833–835`;
  `Identities.agda:132`) — `Π(x:ob). Σ(i:hom(x,x)). iseqv(i)×(i⋄i=i)`,
  matching `(x : Ob) → Σ (Hom x x) is-idpt+eqv` up to notation and the
  order of the two conjuncts. The paper writes `iseqv(i)` first, the
  Agda file writes `is-idpt i × is-eqv i` (`Identities.agda:119–120`),
  and the uniqueness chain swaps them with `×-comm`
  (`Identities.agda:384`).
- **Lemma `id-characterisation` / `idpt+eqv⇔std`** (paper
  `l.843–848`; `Identities.agda:210–217`, with the two directions'
  witnesses at `idpt+eqv→std.left-neutral`/`.right-neutral`,
  `Identities.agda:150,169`, and `std→idpt+eqv.idpt`/`.eqv`,
  `Identities.agda:202,197`) — good identity ⟺ two-sided-neutral, and
  **both sources state this as a biimplication of propositions-as-
  functions, not a type equivalence**: the paper's `l.861–863` remark
  is matched exactly by the Agda file using `⇔` (defined in `Iff.agda`
  as `(A→B)×(B→A)`) rather than `≃` for `idpt+eqv⇔std`'s type.
- **Corollary `only-one-id` / `idpt+eqv-unique`** (paper `l.857–859`;
  `Identities.agda:221–229`) — two good identities at the same object
  are equal; the Agda proof plays `idpt+eqv→std.right-neutral i₂ p₂ i₁`
  against `idpt+eqv→std.left-neutral i₁ p₁ i₂` to chain
  `i₁ = i₁⋄i₂ = i₂`, playing the two conditions against each other.
- **Theorem `id-struc-is-prop` / `goodness-is-prop`** (paper
  `l.865–867`; `Identities.agda:439–444`) — `hasGoodIdStruc(C)` /
  `is-good-category C` is a proposition. The Agda proof composes
  `inhab-to-contr-is-prop` with `WeakFunext.weak-λ=` and, per object,
  `unique.unique-idpt+eqv` — matching the paper's per-object
  contractibility argument plus function extensionality.
- **`I(e)` construction** (paper `l.871–872`, eq. `eq:I-def`, label at
  `l.871` and the displayed equation at `l.872`; `Identities.agda`,
  module `I` at `l.298–339`, field `I` at
  `l.306–307`) — `I(e) := (e⋄-)⁻¹(e)`, syntactically
  `e⁻¹⋄- e` in the Agda naming.
- **Lemma `I-is-id` / `I-is-idpt+eqv`** (paper `l.876–889`;
  `Identities.agda:336–339`) — `I(e)` is a good identity for any
  equivalence `e`. Both proofs split into an idempotence calculation
  and a 2-out-of-3 appeal; the paper cites 2-out-of-3 for equivalences
  as known and does not re-derive it in this excerpt, while
  `Identities.agda` supplies an explicit standalone proof,
  **`eqv-2-out-of-3`** (`l.238–290`), used at exactly this call site
  (`Identities.agda:339`).
- **Lemma `e-I-idem` / `e-vs-I.e-I-idpt`** (paper `l.890–895`, eq.
  `eq:e-Ie` at `l.892`; `Identities.agda:346–359`) — for an
  equivalence `e`, `(e = I(e)) ≃ (e⋄e = e)`, by `ap` along `(e⋄-)`;
  both sources give the same one-line proof idea.
- **Proof of `id-struc-is-prop` / module `unique`** (paper
  `l.901–909`; `Identities.agda:366–414`, `unique-idpt+eqv` at
  `l.413–414`) — the per-object contraction argument. The Agda
  version spells the same reduction as an explicit chain of `≃`-steps
  ending at `is-eqv i₀ ≃ Unit` (via `inhab-prop-is-contr`), matching
  the paper's "reduce to `Σ(i,...). i=i₀`, contractible" at
  statement level; the paper elides the intermediate equivalence
  bookkeeping the Agda chain makes explicit.
- **`def:infcategory` / (no single Agda identifier)** (paper
  `l.916–918`) — an ∞-category is an ∞-semicategory with a good
  identity structure. `Identities.agda` works one level below this
  (semicategories, not the full semisimplicial ∞-semicategory
  structure the paper translates through via `subsec:highersemicats`,
  `l.699–771`, not vendored at full depth in this entry) and does not
  itself state a definition literally named "∞-category". The paper
  states the translation at `l.813–816`: wild-semicategory language
  suffices for the whole §5.2 argument.
- **`good-iff-standard`** (`Identities.agda:430–437`; paper
  `l.920–927` closing remark, with the fidelity caveat recorded in
  the Section map's last bullet) — `is-good-category C ⇔
  is-standard-category C`, unconditional in the Agda file (no
  `is-set` hypothesis in scope).

## What the source establishes

Everything below records what the source states; every mathematical
claim is CONJECTURED until machine-checked in this repository.

The paper defines $\infty$-categories with families ($\infty$-CwF's)
in two-level type theory, to give an internal notion of model for
dependent type theory that does not force unique identity proofs. The
identities-via-idempotent-equivalences development (§5.2, this
entry's load-bearing content) is presented as "a small part of the
paper" that nonetheless supplies "a core idea for the construction of
$\infty$-CwF's": replacing posited two-sided-neutral identities
(structure, and in general non-unique — the paper's Corollary
`only-one-id` and Theorem `id-struc-is-prop` are exactly what rules
this out) with the property "there is an idempotent equivalence at
every object" (`hasGoodIdStruc`), proved propositional without
assuming any set-truncation on the hom-family, via an explicit
construction `I(e) := (e⋄-)⁻¹(e)` and a per-object contraction
argument. The paper states this development "has been completely
formalised in Agda" and supplies the companion repository vendored
here as a secondary artifact; the correspondence table in Content
digests above is a direct read of both sources, not an independent
formalisation-fidelity audit (that is the verifier stage's job, not
yet run — see Vetting).

Field status: the paper was published at LICS 2021 (the 36th Annual
ACM/IEEE Symposium on Logic in Computer Science); the arXiv record
shows two revisions (Sep 2020, Jan 2021) with no later version as of
this ingestion.
