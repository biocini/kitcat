Lane Biocini
July 2026

Gloss: machine-checked evidence for T23 in docs/gloss.md.
Self-contained modulo Core.* and Gloss.*: the three-layer records
are imported from `Gloss.TautologicalFilling` — the same frozen
types, so the two certificates speak about one nominal record
family — and the two-sided module below is frozen from its
tracked source file at the marked commit.

## Synopsis

Setting: the abstract three-layer structure certified in
`Gloss.TautologicalFilling` — families and cofamilies with
morphism actions (`fam-structure`), dependent composites over
contexts with function-valued invariance (`codep-structure`), and
a representable embedding with contractible composition fibers
(`codep-representable`) — equipped with BOTH one-sided
representabilities: the right-handed one is the record's
`compose-contr` field, and the left-handed one enters as an
explicit hypothesis `ccL`, so every theorem below names its exact
assumptions. Write `f ⨾ g` for the right extraction (the center of
the right fiber) and `f ⨾L g` for the left.

Four things are housed here. First, `agree→itc2` and
`itc2→agree`: over that two-sided setting, the agreement of the
two extractions (`f ⨾ g ≡ f ⨾L g`) and the interchange law
(`emb f · g ≡ f ⟩ emb g`, the type `itc2-stmt`) are
inter-derivable — upward by a single three-leg composite, downward
by a one-fiber identification. The two-sided route to proving
interchange is therefore exactly circular: it passes through a
statement equivalent to interchange itself. Second, `cc-τ-blind`:
contractibility witnesses are unique, so no data can hide in the
representability fields. Third, two walls: two routes, fixed in
advance, for deriving the agreement from the structure and `ccL`
alone, each forced with `refl` and each rejected by the
typechecker at the same missing pointwise bridge — the interchange
equation itself; the raw rejection residues are frozen verbatim
below. Fourth, the field inventory: no field of the three-layer
structure has the interchange law's type, so nothing in the axioms
supplies either side of the circle.

Why it matters: in ordinary category theory — morphisms forming
sets — the middle-interchange law is standardly derivable rather
than postulated (folklore, stated here only as contrast; this
certificate proves nothing about the set-level case). Over morphism
types carrying higher structure (this library never truncates
them), this certificate shows that the two-sided-representability
route to interchange is a closed circle: interchange is
inter-derivable with extraction agreement, and neither is
reachable from the axioms alone. That is why interchange is an
axiom of the representable presentation and — one level up — why
its coherence cells exist. The obstruction is intrinsic rather
than an artifact of the abstraction: at the tautological filling
the interchange statement is term-for-term the base category's
interchange axiom (`itc2-taut`, machine-checked in
`Gloss.TautologicalFilling`).

The honest boundary: the two walls are refutations of two routes
fixed in advance, not an independence theorem. The
independence-grade fact for the bridge's base-composition twin is
the collapsed-context countermodel of
`Gloss.ExtractAgreeIndependence`; the inventory is an inventory
of field types, not a non-derivability proof.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Gloss.InterchangeCircularity where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (is-contr→is-prop; _∙_; pcom)
open import Core.Transport.Properties using (is-contr-is-prop)

open import Gloss.TautologicalFilling
  using ( fam-structure; module fam-structure
        ; codep-structure; module codep-structure
        ; codep-representable; module codep-representable )
```

## The record family, imported

This certificate consumes no frozen instance from another
certificate, so the Gloss discipline would permit a fresh frozen
copy of the records; it imports `Gloss.TautologicalFilling`'s
instead because the two certificates freeze one development from
one source experiment, and a single nominal record family keeps the
cross-reference exact — the `itc2-taut` fact cited in the synopsis
is stated there about literally these types.

## The two-sided telescope, frozen

`module A2` binds the two structure layers as implicit parameters,
the representability as an explicit one, and the left
contractibility `ccL` as a hypothesis rather than a record field:
the library's representable records are deliberately right-handed,
and stating the left side as a hypothesis makes each theorem's
assumption set part of its signature. `_⨾L_` is the left
extraction and `itc2-stmt f g` is the interchange law as a type.
For the inventory claimed in the synopsis: the structure's only
path-valued fields are the four family laws and the four
invariance laws (unit and functoriality loci) and `extract-agree`
(the extraction locus) — none of these types is `itc2-stmt` — and
the contractibility fields are pinned by `cc-τ-blind` below.

```agda
-- Frozen from Test.CodepFaithful-20260713-140913 @ dde1f57
-- (tracked-Test provenance; the source may drift — this may not);
-- comments revised at freeze.
module A2 {o h fℓ rℓ} {ob : Type o}
  {FS : fam-structure {o} {h} {fℓ} ob}
  {CS : codep-structure {o} {h} {fℓ} {rℓ} FS}
  (RS : codep-representable CS)
  (open fam-structure FS)
  (open codep-structure CS)
  (open codep-representable RS)
  (ccL : ∀ {x y z} (f : hom x y) (g : hom y z)
       → is-contr (fiber emb (f ⟩ emb g)))
  where

  -- the left extraction over the hypothesis: ccL is a module
  -- parameter, so ⨾L is relative to it, not a second composition.
  _⨾L_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾L g = ccL f g .center .fst

  itc2-stmt : ∀ {x y z} (f : hom x y) (g : hom y z) → Type (fℓ ⊔ rℓ)
  itc2-stmt f g = (emb f · g) ≡ (f ⟩ emb g)

  -- (1) agreement ⇒ interchange-2, one pcom
  --     (pcom p q r : w ≡ z for p : x ≡ w, q : x ≡ y, r : y ≡ z):
  --   p := emb-comp f g          : emb (f ⨾ g)  ≡ emb f · g
  --   q := ap emb ag             : emb (f ⨾ g)  ≡ emb (f ⨾L g)
  --   r := ccL f g .center .snd  : emb (f ⨾L g) ≡ f ⟩ emb g
  agree→itc2 : ∀ {x y z} (f : hom x y) (g : hom y z)
             → f ⨾ g ≡ f ⨾L g → itc2-stmt f g
  agree→itc2 f g ag =
    pcom (emb-comp f g) (ap emb ag) (ccL f g .center .snd)

  -- (2) interchange-2 ⇒ agreement. The injected equation: p
  -- transports the right extraction's fiber witness across the
  -- composite gap, putting both extractions in ONE contractible
  -- fiber (over f ⟩ emb g).
  itc2→agree : ∀ {x y z} (f : hom x y) (g : hom y z)
             → itc2-stmt f g → f ⨾ g ≡ f ⨾L g
  itc2→agree f g p =
    ap fst (is-contr→is-prop (ccL f g) lhs-pt (ccL f g .center))
    where
      lhs-pt : fiber emb (f ⟩ emb g)
      lhs-pt = f ⨾ g , emb-comp f g ∙ p

  -- (3) the representability field is τ-blind.
  cc-τ-blind
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      (cc cc' : is-contr (fiber emb (emb f · g)))
    → cc ≡ cc'
  cc-τ-blind f g = is-contr-is-prop _
```

## The equivalence

Upward (`agree→itc2`): given the agreement
`ag : f ⨾ g ≡ f ⨾L g`, the three legs

- `emb-comp f g : emb (f ⨾ g) ≡ emb f · g`,
- `ap emb ag : emb (f ⨾ g) ≡ emb (f ⨾L g)`,
- `ccL f g .center .snd : emb (f ⨾L g) ≡ f ⟩ emb g`

close `emb f · g ≡ f ⟩ emb g` in one ternary composition —
`pcom p q r : w ≡ z` for `p : x ≡ w`, `q : x ≡ y`, `r : y ≡ z`.

Downward (`itc2→agree`): given `p : emb f · g ≡ f ⟩ emb g`, the
point `(f ⨾ g , emb-comp f g ∙ p)` lands in
`fiber emb (f ⟩ emb g)` — the left fiber, where the left center
already lives. That fiber is contractible, hence a proposition, so
the two points are identified, and `ap fst` projects the
identification to `f ⨾ g ≡ f ⨾L g`. Parallel points of one
contractible fiber are identified for free; the paid case is
bridging distinct fibers — and the walls below arise exactly
where a missing bridge would be needed to place a point into a
fiber at all.

## Twist-blindness and the inventory

Could interchange content hide inside a representability field
itself — a deformed contractibility witness carrying extra path
data? A deformation of a field is just a second value of the
field's type, and `is-contr` of a fixed fiber is a proposition, so
any second value is equal to the first: that is `cc-τ-blind`, and
propositionality is the precise formalization of "nothing can be
stored in the representability fields". Combined with the
inventory — no other field has the interchange law's type — a
twist, in the countermodel style that deforms a single field by a
nontrivial 2-cell, has nothing to deform in the three-layer
structure.

## The walls

The two routes below were fixed before any derivation was
attempted, so the obstruction is not an artifact of proof search:
derive the agreement `f ⨾ g ≡ f ⨾L g` from the three-layer
structure and `ccL` alone, without assuming interchange. Each
route reaches a hole whose type IS the
interchange statement (one per orientation), and forcing that hole
with `refl` asks the conversion checker to accept the pointwise
interchange equation as a definitional identity. The rejection is
the record: a forced-`refl` probe's error names the exact missing
content, with the typechecker as the judge. Both probes were run
live in this certificate's own frozen context (2026-07-13) and
reverted; each fenced block below is the raw typechecker error
verbatim from `The terms` onward — the leading location line names
the transient probe site and is omitted.

A consistency check bound the probes: had either one closed — the
checker accepting `refl` — the result would have contradicted the
trichotomy recorded in the theorem ledger (whose machine-checked
clauses live in `Gloss.PathGroupoid` and `Gloss.PropPinning`) and
the very claim this certificate evidences. Neither closed.

Route (a): one fiber, via `is-contr→is-prop (ccL f g)`. The
attempted term, inside `module A2`:

```text
agree-attempt : ∀ {x y z} (f : hom x y) (g : hom y z)
              → f ⨾ g ≡ f ⨾L g
agree-attempt f g =
  ap fst (is-contr→is-prop (ccL f g)
    (f ⨾ g , emb-comp f g ∙ ?)
    (ccL f g .center))
```

The injected fiber point is `(f ⨾ g , emb-comp f g ∙ ?)` with
`emb-comp f g : emb (f ⨾ g) ≡ emb f · g`, so the `?` is forced at
`emb f · g ≡ f ⟩ emb g` — `itc2-stmt` itself. Forcing it with
`refl`, the checker rejects (exit 42):

```text
The terms
  res-inv-r g (γ .fst) (γ .snd) (emb f (γ .fst , (g ◃ γ .snd)))
and
  res-inv-l f (γ .fst) (γ .snd) (emb g ((γ .fst ▹ f) , γ .snd))
are not equal at type res (γ .fst , γ .snd)
when checking that the expression emb-comp f g ∙ refl has type
emb (compose-contr f g .center .fst) ≡ (f ⟩ emb g)
```

Route (b): the reverse orientation — put the left extraction's
point into `compose-contr`'s fiber. The attempted term, inside
`module A2`:

```text
agree-attempt f g =
  ap fst (is-contr→is-prop (compose-contr f g)
    (compose-contr f g .center)
    (f ⨾L g , ccL f g .center .snd ∙ ?))
```

The injected fiber point is
`(f ⨾L g , ccL f g .center .snd ∙ ?)` with
`ccL f g .center .snd : emb (f ⨾L g) ≡ f ⟩ emb g`, so the `?` is
forced at `f ⟩ emb g ≡ emb f · g` — the inverse of `itc2-stmt`.
Forcing it with `refl`, the checker rejects (exit 42):

```text
The terms
  res-inv-l f (γ .fst) (γ .snd) (emb g ((γ .fst ▹ f) , γ .snd))
and
  res-inv-r g (γ .fst) (γ .snd) (emb f (γ .fst , (g ◃ γ .snd)))
are not equal at type res (γ .fst , γ .snd)
when checking that the expression ccL f g .center .snd ∙ refl has
type emb (ccL f g .center .fst) ≡ emb f · g
```

Both routes reduce to the SAME missing bridge, one per
orientation: the circularity is exact — `agree→itc2` and
`itc2→agree` pin agreement ⟺ interchange over the two-sided
setting, and no field supplies either side (the inventory above).
Neither probe closed, as the consistency check requires.
