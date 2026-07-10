Lane Biocini
July 2026

Representable codependent categories. A category is given by `hom`,
identities `idn`, a representable embedding `emb` into `composite`
morphisms, and one axiom: composition fibers of `emb` are contractible.

The carrier structure (`binder`, `unit`, `fam`) is canonical,
derived from `hom` and `idn`. The lax substitution `sub` and the
codependent application `_·_` are derived: acting by `g` is `emb g`
evaluated at the re-anchored identity context (`act = emb @ idn`).
Re-anchoring is idempotent definitionally, so `_·_` is transport-free
and `composite = Π` keeps a visible head.

`idn` here is the representable anchor — the slot the action reads at,
posited not characterized. No unit laws or identity uniqueness are
asserted or used; those (the full four-axiom wiring) are a later
milestone.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Transport.J using (J)
open import Core.Equiv.Base using (iso→equiv; _≃_)
```

## The record

The four fields are `hom`, `idn`, `emb`, `compose-contr`. Everything
else — the passenger/acted split, `at`, `acted`, `ctx`, `composite`,
`act`, `sub`, `_·_`, `_⨾_`, `emb-comp`, `act-comp`, `sub-comp`,
`·-comp` — is derived.

An element of `composite x y` is a *formal composite*: for any context
associating `x` and `y`, a `fam` witness. `compose-contr` is stated
through `is-representable`, exposing the axiom schema of the whole
theory: every representability axiom has the shape "a designated formal
composite is contractibly representable". The `hom` arrows are the
*tight* composites; that "names are tight" is a theorem
(`hom≃representable`, unconditional; `is-representable-prop` in
`Cat.Codep.Unit` upgrades its reading to a subtype inclusion), not a
definition — see docs/LEXICON.md for the tight/composite vocabulary.

```agda
record codep-category {o h} (ob : Type o)
  : Type (o ⊔ h ₊) where
  no-eta-equality
  field
    hom : ob → ob → Type h
    idn : (x : ob) → hom x x

  -- The carrier is canonical, derived from hom + idn: a binder is a
  -- hom into the domain; `unit` is the identity binder.
  binder : ob → Type (o ⊔ h)
  binder x = Σ w ∶ ob , hom w x

  unit : (y : ob) → binder y
  unit y = y , idn y

  -- A passenger carries an acted-object `v` and a `binder` (the inert
  -- left data); `fam v (w , a) = hom w v`, `acted` is `fam` re-anchored.
  pass : ob → Type (o ⊔ h)
  pass x = ob × binder x

  fam : ∀ {x} → pass x → Type h
  fam (v , w , a) = hom w v

  -- Re-anchor to a new domain `y`: keep the acted-object (the first
  -- component), swap in the identity binder. Definitionally idempotent.
  at : ∀ {x} → (y : ob) → pass x → pass y
  at y φ = φ .fst , unit y

  acted : ∀ {x} → pass x → ob → Type h
  acted φ z = fam (at z φ)

  ctx : ob → ob → Type (o ⊔ h)
  ctx x y = Σ φ ∶ pass x , acted φ y

  composite : ob → ob → Type (o ⊔ h)
  composite x y = (γ : ctx x y) → fam (γ .fst)

  composite-ext : ∀ {x y} {F G : composite x y} → (∀ γ → F γ ≡ G γ) → F ≡ G
  composite-ext h = funext h

  field
    emb : ∀ {x y} → hom x y → composite x y

  -- The tightness predicate: a composite arrow is representable when an
  -- `emb`-image.
  is-representable : ∀ {x y} → composite x y → Type (o ⊔ h)
  is-representable F = fiber emb F

  -- The lax action is derived: acting by `g` is `emb g` at the
  -- re-anchored (identity) context. This is the emb–act link the
  -- inner-associator coherence needs. `acted (at y φ) z = acted φ z`
  -- holds definitionally (re-anchoring is idempotent), so no transport.
  act : ∀ {x} (φ : pass x) {y z} → hom y z → acted φ z → acted φ y
  act φ {y} g α = emb g (at y φ , α)

  sub : ∀ {x y z} → hom y z → ctx x z → ctx x y
  sub g (φ , α) = φ , act φ g α

  _·_ : ∀ {x y z} → composite x y → hom y z → composite x z
  (F · g) γ = F (sub g γ)
  infixl 30 _·_

  field
    compose-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (is-representable (emb f · g))

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = compose-contr f g .center .fst
  infixr 40 _⨾_

  emb-comp : ∀ {x y z} (f : hom x y) (g : hom y z)
           → emb (f ⨾ g) ≡ emb f · g
  emb-comp f g = compose-contr f g .center .snd

  -- act-comp is a theorem: emb-comp evaluated at the identity context.
  -- `act (at y φ) h α = act φ h α` reduces definitionally.
  act-comp
    : ∀ {x} (φ : pass x) {y z w}
      (g : hom y z) (h : hom z w) (α : acted φ w)
    → act φ (g ⨾ h) α ≡ act φ g (act φ h α)
  act-comp φ {y} g h α = happly (emb-comp g h) (at y φ , α)

  sub-comp : ∀ {x y z w} (g : hom y z) (h : hom z w)
           → sub {x} (g ⨾ h) ≡ sub g ∘ sub h
  sub-comp g h = funext λ γ → ap (γ .fst ,_) (act-comp (γ .fst) g h (γ .snd))

  ·-comp : ∀ {x y z w} (F : composite x y) (g : hom y z) (h : hom z w)
         → F · (g ⨾ h) ≡ F · g · h
  ·-comp F g h = funext λ γ → ap F (happly (sub-comp g h) γ)

  -- Names are tight: `hom` ≃ the total space of the `emb`-fibers,
  -- unconditionally (the subtype reading needs `is-representable-prop`).
  hom≃representable
    : ∀ {x y} → hom x y ≃ (Σ F ∶ composite x y , is-representable F)
  hom≃representable {x} {y} = iso→equiv fwd bwd hom-ret rep-sec
    where
      fwd : hom x y → Σ F ∶ composite x y , is-representable F
      fwd f = emb f , (f , refl)

      bwd : (Σ F ∶ composite x y , is-representable F) → hom x y
      bwd (F , a , p) = a

      hom-ret : ∀ f → bwd (fwd f) ≡ f
      hom-ret f = refl

      rep-sec : ∀ s → fwd (bwd s) ≡ s
      rep-sec (F , a , p) = J (λ F' p' → fwd a ≡ (F' , a , p')) refl p
```

## Re-anchor idempotency

The definitional idempotency that `act` and `act-comp` rely on holds
by `refl`.

```agda
module _ {o h} {ob : Type o} (R : codep-category {o} {h} ob) where
  open codep-category R

  at-idem : ∀ {x} (φ : pass x) (y z : ob) → at z (at y φ) ≡ at z φ
  at-idem φ y z = refl
```
