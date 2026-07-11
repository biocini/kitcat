Lane Biocini
July 2026

The opposite of a representable hcategory — the polarity mirror of
the post-biased presentation. `op` reverses `hom`, swaps the two
context halves (`cofam ↔ fam`), and thereby swaps `pre ↔ post`
*definitionally*. Every mirror axiom is derivable from the base five
fields: the post-bias of `hcategory-axioms` is chirality, not
asymmetry.

The eval axiom is self-mirror. `pre f (idn y)` and `post f (idn x)`
are the same term — both read `emb f` at the doubly-centered context
— so op's `post-eval` is literally the base's. The unit equivalences
trade places (`unit-eqvl ↔ unit-eqvr`), interchange reverses (`sym`
of the base at swapped arguments), and only `compose-contr` needs
transport: through the fiber-transposing `swap·`/`swap·'` retraction
across `op-comp-path`, which is one application of `interchange`.

`op-structure`/`op-axioms`/`op` mirror the trilayer; `op-invol`
witnesses `op (op C) ≡ C`, definitional on `hom`/`idn`/`emb` and
`is-contr`-propositional on the composition fibers.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep.Op where

open import Cat.Codep.Base

open import Core.Data.Nat.Type using (Z)
open import Core.Data.Sigma.Base using (swap)
open import Core.Data.Sigma.Type using (_,_; fst; snd)
open import Core.HLevel.Base using (retract→is-hlevel)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.Base
open import Core.Kan using (_∙_; is-contr→is-prop)
open import Core.Type
```

## The opposite structure

`op-structure` reverses `hom`, keeps `idn`, and precomposes `emb`
with `swap`. The context types transpose (`cofamᵒ x = fam x`,
`famᵒ y = cofam y`), so `swap γ` retypes a `ctxᵒ x y` to a `ctx y x`
and `res (swap γ) = resᵒ γ` holds definitionally.

```agda
module _ {o h} {ob : Type o} where
  open hcategory-structure

  op-structure
    : hcategory-structure {o} {h} ob → hcategory-structure {o} {h} ob
  op-structure S .hom x y = S .hom y x
  op-structure S .idn     = S .idn
  op-structure S .emb f γ = S .emb f (swap γ)
```

## Definitional parity

The polarity swap trades the two representable actions. Both witnesses
hold by `refl`: op's `pre` at the reversed context is the base's
`post`, and vice versa. The transposition helpers `swap·`/`swap·'`
carry composites across the reversal; both roundtrips are the identity
by Σ- and function-eta, and `embᵒ f = swap· (emb f)` definitionally.

```agda
module _ {o h} {ob : Type o} (S : hcategory-structure {o} {h} ob) where
  private
    module S  = hcategory-structure S
    module Sᵒ = hcategory-structure (op-structure S)

  preᵒ-is-post
    : ∀ {y z v} (g : S.hom z y) (b : S.hom v z)
    → Sᵒ.pre g b ≡ S.post g b
  preᵒ-is-post g b = refl

  postᵒ-is-pre
    : ∀ {x y w} (f : S.hom y x) (a : S.hom x w)
    → Sᵒ.post f a ≡ S.pre f a
  postᵒ-is-pre f a = refl

  swap· : ∀ {x y} → S.composite y x → Sᵒ.composite x y
  swap· F γ = F (swap γ)

  swap·' : ∀ {x y} → Sᵒ.composite x y → S.composite y x
  swap·' G δ = G (swap δ)
```

## The opposite axioms

`op-comp-path` transports the reversed composite `emb g · f` onto the
transpose of the op composite `embᵒ f ·ᵒ g` by one `interchange`.
`compose-contr` is Route-B: its fiber center is *definitionally* the
base extraction `A._⨾_ g f` (transported to a `Sᵒ.emb`-fiber by
`swap·` across `op-comp-path`), and contractibility is discharged by
`is-contr→is-prop` against the transported base fiber (the
`swap·`/`swap·'` retract of `A.compose-contr g f` across
`op-comp-path`). The definitional center makes `Aᵒ._⨾_ f g` reduce to
`A._⨾_ g f`, so `op-comp-eq` is `refl`. `interchange` is the base at
reversed arguments under `sym`; `post-eval`, `unit-eqvl`, and
`unit-eqvr` are base fields verbatim (the last two swapped).

```agda
module _ {o h} {ob : Type o} {S : hcategory-structure {o} {h} ob}
  (A : hcategory-axioms S) where
  private
    module S  = hcategory-structure S
    module Sᵒ = hcategory-structure (op-structure S)
    module A  = hcategory-axioms A

  op-comp-path
    : ∀ {x y z} (f : S.hom y x) (g : S.hom z y)
    → S.emb g S.· f ≡ swap·' S (Sᵒ.emb f Sᵒ.· g)
  op-comp-path f g = funext λ γ →
    A.interchange g f (γ .fst .snd) (γ .snd .snd)

  op-axioms : hcategory-axioms (op-structure S)
  op-axioms .hcategory-axioms.compose-contr f g .center =
    A._⨾_ g f , ap (swap· S) (A.emb-comp g f ∙ op-comp-path f g)
  op-axioms .hcategory-axioms.compose-contr f g .paths =
    is-contr→is-prop
      (retract→is-hlevel Z to fro (λ _ → refl)
        (subst (λ T → is-contr (fiber S.emb T))
          (op-comp-path f g) (A.compose-contr g f)))
      (op-axioms .hcategory-axioms.compose-contr f g .center)
    where
      to : fiber S.emb (swap·' S (Sᵒ.emb f Sᵒ.· g))
         → fiber Sᵒ.emb (Sᵒ.emb f Sᵒ.· g)
      to (m , p) = m , ap (swap· S) p

      fro : fiber Sᵒ.emb (Sᵒ.emb f Sᵒ.· g)
          → fiber S.emb (swap·' S (Sᵒ.emb f Sᵒ.· g))
      fro (m , q) = m , ap (swap·' S) q
  op-axioms .hcategory-axioms.interchange f g a b =
    sym (A.interchange g f b a)
  op-axioms .hcategory-axioms.post-eval f = A.post-eval f
  op-axioms .hcategory-axioms.unit-eqvl   = A.unit-eqvr
  op-axioms .hcategory-axioms.unit-eqvr   = A.unit-eqvl

  private
    module Aᵒ = hcategory-axioms op-axioms

  -- Route-B regression witness: the op extraction is the base
  -- extraction swapped, now `refl` since the fiber center is
  -- definitional.
  op-comp-eq
    : ∀ {x y z} (f : S.hom y x) (g : S.hom z y)
    → Aᵒ._⨾_ f g ≡ A._⨾_ g f
  op-comp-eq f g = refl
```

## The bundle and its involution

`op` mirrors the trilayer. The structure involution is definitional
on all three fields (the double `swap` and double reversal cancel by
eta); the axioms involution is definitional on every field but
`compose-contr`, which is bridged propositionally through
`is-contr-is-prop`.

```agda
module _ {o h} {ob : Type o} where
  open hcategory-structure

  op-structure-invol
    : (S : hcategory-structure {o} {h} ob)
    → op-structure (op-structure S) ≡ S
  op-structure-invol S i .hom = S .hom
  op-structure-invol S i .idn = S .idn
  op-structure-invol S i .emb = S .emb

module _ {o h} {ob : Type o} {S : hcategory-structure {o} {h} ob} where
  private module S = hcategory-structure S

  op-axioms-invol
    : (A : hcategory-axioms S)
    → PathP (λ i → hcategory-axioms (op-structure-invol S i))
        (op-axioms (op-axioms A)) A
  op-axioms-invol A i .hcategory-axioms.compose-contr f g =
    is-prop→PathP
      {A = λ _ → is-contr (fiber S.emb (S.emb f S.· g))}
      (λ _ → is-contr-is-prop _)
      (op-axioms (op-axioms A) .hcategory-axioms.compose-contr f g)
      (A .hcategory-axioms.compose-contr f g) i
  op-axioms-invol A i .hcategory-axioms.interchange f g a b =
    A .hcategory-axioms.interchange f g a b
  op-axioms-invol A i .hcategory-axioms.post-eval f =
    A .hcategory-axioms.post-eval f
  op-axioms-invol A i .hcategory-axioms.unit-eqvl =
    A .hcategory-axioms.unit-eqvl
  op-axioms-invol A i .hcategory-axioms.unit-eqvr =
    A .hcategory-axioms.unit-eqvr

module _ {o h} where
  open hcategory using (ob; structure; axioms)

  op : hcategory o h → hcategory o h
  op C .ob        = C .ob
  op C .structure = op-structure (C .structure)
  op C .axioms    = op-axioms (C .axioms)

  op-invol : (C : hcategory o h) → op (op C) ≡ C
  op-invol C i .ob        = C .ob
  op-invol C i .structure = op-structure-invol (C .structure) i
  op-invol C i .axioms    = op-axioms-invol (C .axioms) i
```
