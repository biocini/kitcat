Lane Biocini
July 2026

Representable codependent categories, in a trilayer presentation.

The operations — `hom`, identities `idn`, a representable embedding
`emb` into `composite` morphisms, and the two representable actions
`pre`/`post` — together with every axiom-free derived notion live in
`codep-structure`. The five axioms (contractible composition fibers,
the coupling `interchange`/`post-eval`, and the two unit equivalences)
plus the extraction `_⨾_` and derived laws live in `codep-axioms`,
stated over a `codep-structure` value. The universe-ranging
`codep-category` bundles `ob`, `structure`, `axioms` and re-exports the
other two — so the bundle IS the category and the refactor equation is
literal: `Cat.Type.category ≅ codep-category`.

The carrier structure (`binder`, `unit`, `fam`) is canonical,
derived from `hom` and `idn`. The lax substitution `sub` and the
codependent application `_·_` are derived: acting by `g` is `emb g`
evaluated at the re-anchored identity context (`act = emb @ idn`).
Re-anchoring is idempotent definitionally, so `_·_` is transport-free
and `composite = Π` keeps a visible head.

`idn` is the representable anchor — the slot the actions read at. The
unit axioms `unit-eqvl`/`unit-eqvr` make it a genuine unit; from them
the derived-law modules (`Cat.Codep.Coupling`, `Cat.Codep.Unit`)
recover idempotency, absorption, the unit laws, and identity
uniqueness.

Splitting the axioms off from the operations is what makes naive
multi-object instances termination-safe: `codep-axioms` states its
axioms over an *external* `codep-structure` value, so a direct
instance's proof only projects that closed value — a `hom`/`idn` that
cases on the object no longer leaves a stuck `idn y` self-call.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Transport.J using (J)
open import Core.Equiv.Base using (iso→equiv; _≃_; is-equiv)
```

`codep-structure`: the operations `hom`/`idn`/`emb`, the canonical
carrier, the two representable actions `pre`/`post` (`pre g` on the
acted slot, `post f` on the passenger binder — the axiom field types
`interchange`/`post-eval`/the unit equivalences reference them, so they
live here), and the remaining axiom-free derived notions.

```agda
record codep-structure {o h} (ob : Type o)
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

  -- `pre g` acts on the acted slot, `post f` on the passenger binder;
  -- both are `emb` at the identity context (structure-level).
  pre : ∀ {y z} (g : hom y z) {v} → hom z v → hom y v
  pre {y} g {v} b = emb g ((v , (y , idn y)) , b)

  post : ∀ {x y} (f : hom x y) {w} → hom w x → hom w y
  post {x} {y} f {w} a = emb f ((y , (w , a)) , idn y)

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

  -- Re-anchoring is definitionally idempotent.
  at-idem : ∀ {x} (φ : pass x) (y z : ob) → at z (at y φ) ≡ at z φ
  at-idem φ y z = refl
```

`codep-axioms`: the five axioms over a `codep-structure` value —
`compose-contr`, the coupling `interchange` and `post-eval`, and the
two unit equivalences — with the extraction `_⨾_` and the derived
composition laws. The structure parameter is annotated `{o} {h}` so the
level is fixed by the value.

```agda
record codep-axioms {o h} {ob : Type o}
  (S : codep-structure {o} {h} ob) : Type (o ⊔ h) where
  no-eta-equality
  open codep-structure S

  field
    compose-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (is-representable (emb f · g))
    interchange
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        {w} (a : hom w x) {v} (b : hom z v)
      → emb f ((v , (w , a)) , pre g b)
      ≡ emb g ((v , (w , post f a)) , b)
    post-eval
      : ∀ {x y} (f : hom x y) → post f (idn x) ≡ f
    unit-eqvl : ∀ {x} {v} → is-equiv (pre (idn x) {v})
    unit-eqvr : ∀ {x} {w} → is-equiv (post (idn x) {w})

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
```

`codep-category`: the universe-ranging bundle. The axioms record is now
complete, so the bundle IS the category. The two `open … public` lines
re-export the structure and axioms, so a single `open codep-category C`
recovers the entire API.

```agda
record codep-category (o h : Level) : Type ((o ⊔ h) ₊) where
  no-eta-equality
  field
    ob        : Type o
    structure : codep-structure {o} {h} ob
    axioms    : codep-axioms structure
  open codep-structure structure public
  open codep-axioms axioms public
```

Definitional regression witnesses: `composite` is a genuine Π
(application computes — the funext-merge substrate), and `act-comp` is
definitionally `happly` of `emb-comp`. (`at-idem` is a `refl` field-def
above.) The bundle re-export recovers both structure-level and
axioms-level names from one `open`.

```agda
module _ {o h} {ob : Type o} (S : codep-structure {o} {h} ob) where
  open codep-structure S

  composite-is-Π : ∀ {x y} (F : composite x y) (γ : ctx x y) → fam (γ .fst)
  composite-is-Π F γ = F γ

module _ {o h} {ob : Type o} {S : codep-structure {o} {h} ob}
  (A : codep-axioms S) where
  open codep-structure S
  open codep-axioms A

  act-comp-is-happly
    : ∀ {x} (φ : pass x) {y z w}
      (g : hom y z) (hh : hom z w) (α : acted φ w)
    → act-comp φ g hh α ≡ happly (emb-comp g hh) (at y φ , α)
  act-comp-is-happly φ g hh α = refl

module _ {o h} (C : codep-category o h) where
  open codep-category C

  -- structure-level and axioms-level names, from a single open.
  _ : ∀ {x y} → hom x y → composite x y
  _ = emb

  _ : ∀ {x y z} → hom x y → hom y z → hom x z
  _ = _⨾_
```
