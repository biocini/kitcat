# Gist — 2025-06-03 — coherent units, idempotent equivalences, duploids

The argument referred to as "the gist" by
`2026-07-22-deductive-system-design.md` (obligation **O2**), vendored.
It carries the reason `is-unital` is a proposition even though its
idempotence component is an untruncated path, and the reason the tier
depends on `is-composable`.

**Status.** Superseded, retained for provenance. The deductive-system
and virtual-graph formulation is the record; the lines of
investigation that produced it depart from this document. Nothing
below is a current design proposal.

CONJECTURED throughout. The development is written in the vocabulary
of its own source tree, not kitcat's, and nothing here is
machine-checked in this repository. The transcription notes record
correspondences established by inspection only.

**Where it diverges.** `is-iso` below is stated over the
*composition-action* — `λ g → f ∙ g` and `λ h → h ∙ f` — which at
`f = idn` is the `is-equiv (idn ⨾ −)` form the deductive-system
ruling excludes from the unit tier's fields. The exclusion turns on
the stability tier, which postdates this document: the canonical
flank paths must exist readback-free, and the composition-action
forms do not reach the emb-action absorptions without readback, so
`is-stable` would be stated circularly over them. The
composition-action package is comparison material, not fields. What
survives here as live material is the *technique* — idempotence
obtained as a fiber centre — which is obligation O2's subject and
refines O1 without changing the field list.

**Custody.** Three external attributions appear and none has a
`resources/` entry yet: John Chen's *Semicategories with Identities*
literate Agda development; Kraus et al. on idempotent equivalences
(the Capriotti–Kraus package named in the design note); and the
TypeTopology duploid formalization. Entries are owed before any of
the three supports a load-bearing claim.

## What it settles

The `is-unital` package is a proposition. The idempotence datum
`idem : idn ⨾ idn ≡ idn` is a path in a hom type and homs are never
truncated here, so `idem` is not a proposition on its own — but the
other factors pin it. The pinning is exhibited twice: once by deriving
the coherences from idempotence, once by deriving idempotence from the
coherences as a fiber centre.

The tier's dependence on `is-composable` is likewise not bookkeeping.
The coherence conditions are associator-shaped —

```
has-lunit-coh i = ∀ {y} (f : C.₁ x y) → i ∙ (i ∙ f) ＝ i ∙ f
has-runit-coh i = ∀ {w} (f : C.₁ w x) → (f ∙ i) ∙ i ＝ f ∙ i
```

— so they mention the composition operation, which is the projected
centre of the composability fibers. The dependence is honest
type-former dependence, as the design note states; this is why.

## Isomorphism as a pair of composition equivalences

An isomorphism is not a bare inverse. It is the statement that pre-
and post-composition are equivalences, from which one-sided units are
extracted.

```agda
record is-iso {x y} (f : C.₁ x y) : Type C.ℓ where
  field
    pre  : (z : C.₀) → is-equiv (λ (g : C.₁ y z) → f ∙ g)
    post : (w : C.₀) → is-equiv (λ (h : C.₁ w x) → h ∙ f)

  linv : ∀ {z} → C.₁ x z → C.₁ y z
  linv {z} = eqv-inv (pre z)

  rinv : ∀ {w} → C.₁ w y → C.₁ w x
  rinv {w} = eqv-inv (post w)

  lunit : C.₁ x x
  lunit = rinv f

  runit : C.₁ y y
  runit = linv f

_≅_ : C.₀ → C.₀ → Type C.ℓ
x ≅ y = Σ f ∶ C.₁ x y , is-iso f
```

Chen's observation is the hinge: *the type of identifications of an
equivalence `f` with `ℐ f` is equivalent to the type of witnesses of
idempotence of `f`.*

## The two presentations

```agda
has-iso-lcoh : ∀ {x} {f : C.₁ x x} → is-iso f → Type C.ℓ₁
has-iso-lcoh {f} iso = is-iso.lunit iso ＝ f

has-iso-rcoh : ∀ {x} {f : C.₁ x x} → is-iso f → Type C.ℓ₁
has-iso-rcoh {f} iso = is-iso.runit iso ＝ f

record is-idem-equiv {x} (idn : C.₁ x x) : Type C.ℓ where
  field
    idem : is-idempotent idn
    iso  : is-iso idn

record is-coherent-unit {x} (idn : C.₁ x x) : Type C.ℓ where
  field
    iso  : is-iso idn
    lcoh : has-iso-lcoh iso
    rcoh : has-iso-rcoh iso
```

## Unit laws from the coherences

```agda
module idn-laws {x} {idn : C.₁ x x}
  (e : is-iso idn)
  (idem : is-idempotent idn)
  where
  module _ {y : C.₀} (f : C.₁ x y) where
    private
      einv = is-iso.pre e y
      linv = eqv-inv einv
      unit = eqv-sec einv

    lneutral : has-lunit-coh idn → idn ∙ f ＝ f
    lneutral coh i = hcomp (∂ i) λ where
      k (i = i0) → unit (idn ∙ f) k
      k (i = i1) → unit f k
      k (k = i0) → linv (coh f i)

  module _ {w : C.₀} (f : C.₁ w x) where
    private
      einv = is-iso.post e w
      rinv = eqv-inv einv
      unit = eqv-sec einv

    rneutral : has-runit-coh idn → f ∙ idn ＝ f
    rneutral coh i = hcomp (∂ i) λ where
      k (i = i0) → unit (f ∙ idn) k
      k (i = i1) → unit f k
      k (k = i0) → rinv (coh f i)
```

## Forward: coherences as fiber-path projections

From iso and idempotence, both coherences are `ap fst` of the fiber
path connecting the equivalence's centre to `(idn , idem)`.

```agda
module idem-equiv→coh {x} {idn : C.₁ x x}
  (e : is-iso idn)
  (idem : is-idempotent idn)
  where

  c0 : fiber (_∙_ idn) idn
  c0 = contr-map (is-iso.pre e x) idn .ctr

  c1 : fiber (_∙ idn) idn
  c1 = contr-map (is-iso.post e x) idn .ctr

  h0 : C.₁ x x
  h0 = c0 .fst

  p0 : idn ∙ h0 ＝ idn
  p0 = c0 .snd

  h1 : C.₁ x x
  h1 = c1 .fst

  p1 : h1 ∙ idn ＝ idn
  p1 = c1 .snd

  f0 : Path (fiber (idn ∙_) idn) (h0 , p0) (idn , idem)
  f0 = is-equiv.fibers (is-iso.pre e x) (idn , idem)

  f1 : Path (fiber (_∙ idn) idn) (h1 , p1) (idn , idem)
  f1 = is-equiv.fibers (is-iso.post e x) (idn , idem)

  α0 : h0 ＝ idn
  α0 = ap fst f0

  α1 : h1 ＝ idn
  α1 = ap fst f1

  has-rcoh : has-iso-rcoh e
  has-rcoh = α0

  has-lcoh : has-iso-lcoh e
  has-lcoh = α1
```

## Propositionality of the unit

Any two idempotent-equivalence units are identified, given the two
coherence conditions. This is the propositionality the tier needs.

```agda
module _ {x} {idn idn' : C.₁ x x}
  (e  : is-idem-equiv idn)
  (e' : is-idem-equiv idn')
  (lunit-coh : has-lunit-coh idn)
  (runit-coh : has-runit-coh idn')
  where
  module lcoh = idem-equiv→coh (is-idem-equiv.iso e)  (e  .is-idem-equiv.idem)
  module rcoh = idem-equiv→coh (is-idem-equiv.iso e') (e' .is-idem-equiv.idem)
  private
    rneutral' = idn-laws.rneutral
      (e' .is-idem-equiv.iso) (e' .is-idem-equiv.idem) idn runit-coh

    lneutral = idn-laws.lneutral
      (e .is-idem-equiv.iso) (e .is-idem-equiv.idem) idn' lunit-coh

  idem-equiv→contr-idn : idn ＝ idn'
  idem-equiv→contr-idn = sym rneutral' ∙ lneutral
```

## Backward: idempotence as a fiber centre

The map `is-coherent-unit → is-idem-equiv`. Idempotence is not
assumed; it is produced as the diagonal of a square whose sides are
the two routes from `idn ∙ idn` to `idn`.

```agda
module _ {x} {idn : C.₁ x x} (e : is-iso idn)
  (lcoh : has-iso-lcoh e)
  (rcoh : has-iso-rcoh e)
  where
  private
    module fibers
      (e : is-iso idn)
      (lcoh : has-iso-lcoh e)
      (rcoh : has-iso-rcoh e)
      where
      open is-iso e
      E = C.₁ x x

      lctr : (i : E) → fiber (idn ∙_) i
      lctr = is-equiv.center (pre x)

      rctr : (i : E) → fiber (_∙ idn) i
      rctr = is-equiv.center (post x)

      lpre : linv (idn ∙ idn) ＝ idn
      lpre = eqv-sec (pre x) idn

      rpre : idn ∙ runit ＝ idn
      rpre = eqv-retr (pre x) idn

      lpost : lunit ∙ idn ＝ idn
      lpost = eqv-retr (post x) idn

      w0 : idn ∙ idn ＝ idn
      w0 = ap (idn ∙_) (sym rcoh) ∙ rpre

      w1 : idn ∙ idn ＝ idn
      w1 = ap (_∙ idn) (sym lcoh) ∙ lpost

      w : idn ∙ idn ＝ idn ∙ idn
      w = w0 ∙ sym w1

      ι : Square w0 w w1 refl
      ι = cone w0 w1

      ψ : Path (fiber id idn) (idn ∙ idn , w0) (idn ∙ idn , w1)
      ψ i = w i , λ j → ι i j

      κ : idn ∙ idn ＝ idn
      κ i = ψ i .snd i

      idn-equiv : is-idem-equiv idn
      idn-equiv .is-idem-equiv.idem = κ
      idn-equiv .is-idem-equiv.iso .is-iso.pre  = pre
      idn-equiv .is-idem-equiv.iso .is-iso.post = post

    idn-equiv : is-idem-equiv idn
    idn-equiv = fibers.idn-equiv e lcoh rcoh
```

The idempotence lemma arrives as the propositional centre of the
fiber paths witnessing that idempotent composition is homotopy
equivalent to the identity map, over the canonical identity morphism
*between* left and right composition with the unit. That is the
candidate canonical centre of contraction for `is-idem-equiv`, drawn
out explicitly where the `is-idem-equiv` presentation leaves it
implicit.

## Transcription notes

Vocabulary key against kitcat, by inspection:

| gist | kitcat |
| --- | --- |
| `C.₀` / `C.₁ x y` | `vtx` / `edge x y` (`ob` / `hom` in `Cat.Logic`) |
| `＝` | `_≡_` |
| `hcomp` | `Core.Kan.hcom` |
| `contr-map … .ctr` | `is-contr … .center` |
| `is-equiv.fibers` | `Core.Equiv.Base.eqv-fibers` |
| `eqv-sec` / `eqv-retr` | same names, `Core.Equiv` |
| `cone w0 w1` | `Core.Kan.cone` — types agree exactly |

The `cone` correspondence is worth recording because it is the one
non-trivial cubical ingredient of the backward map. `Core.Kan.cone`
has

```agda
cone : {x y z : A} (q : y ≡ z) (r : x ≡ z) → Square q (q ∙ sym r) r (λ _ → z)
```

and the gist's `ι : Square w0 w w1 refl` with `w = w0 ∙ sym w1` is
`cone w0 w1` on the nose under kitcat's `Square p q r s` convention
(`p` left, `q` top, `r` right, `s` bottom). The backward map is
therefore transcribable against machinery already present.

## Duploids

The unit definition sits on top of the underlying graph and
composition data alone, so it applies to a deductive system as
readily as to a category. `has-lunit-coh` and `has-runit-coh` are the
linearity and thunkability conditions for identity morphisms: they
express the path-equivalence of pre- and post-unit composition to
composition with unit double-composites. Read that way, the two forms
factor the idempotence lemma through `is-linear`/`is-thunkable` at the
unit, and the derivation of the identity laws *is* the witnessing of
linearity and thunkability for units.

The programme this supports: work in a wild categorical setting after
Kraus et al. and impose stricter coherence axioms (`hom-is-set` and
above) only where needed. The payoff of routing the definition of
category through idempotent equivalence is that *category* becomes
the property of a semicategory possessing a propositional unit. The
same shape is expected for duploids, where the unit specifies a
property of the sub-semicategory carrying the deductive-system data,
together with the minimal collection of associator morphisms
establishing linearity and thunkability of units.

## Open threads

- The full equivalence `is-coherent-unit ≃ is-idem-equiv`. The
  forward map (`idem-equiv→coh`) and the backward map are both above;
  the round trips are not.
- **The HAE direction.** Whether the associator morphism can be taken
  as part of the data of an equivalence, so that the corresponding
  higher-path coherence of a half-adjoint equivalence is the law.
  Taking left neutrality WLOG, the target shape is
  `ap (idn ∙_) (idnl f) ＝ r (inv-idn-∙ f)` for a retraction datum
  `r`, with `idnl` as the section datum. Since `(idn ∙_)` is an
  equivalence by definition its inverse is unique, so the
  pre-composition inverse from `is-iso` is the obvious candidate for
  `r`. The ideal outcome is that the retraction-side expression is
  path-equivalent to `lunit f`, giving

  ```
  ap (idn ∙_) (idnl f) ＝ r (inv-idn-∙ f) ＝ idnl f
    ⟹  (idn ∙_) ＝ id  ∧  (λ f → r (inv-idn-∙ f)) ＝ lunit
                       ∧  (λ f → ap (idn ∙_) (idnl f)) ＝ idnl
  ```

  and with it the propositionality of the canonical identity laws from
  the assumed structure of units. Not worked out; this is O2's
  substance, and it refines O1 whichever way it lands.
- Reproduction of the TypeTopology duploid formalization in this
  framework, with attention to what the cubical setting buys. The
  stronger `is-iso` above is the first candidate refinement.
- Whether the restricted duploid setting yields meta-theoretic
  consequences for type-theoretic definitions of categorical data —
  the "right way" to situate duploids with respect to categories.
