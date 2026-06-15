Lane Biocini, March 2026. Path characterization and monad laws
for the propositional lifting monad.

`LiftM-path` constructs paths between `LiftM` values via
Glue-based propositional extensionality. The monad laws follow as
corollaries with trivial value coherence.

This module uses `--cubical` (not `--erased-cubical`) because
`LiftM-path` constructs type paths between definedness predicates
via Glue types, which require full cubical.

```agda
{-# OPTIONS --safe --cubical --no-guardedness --no-sized-types #-}

module Core.Function.Partial.Properties where

open import Core.Type
open import Core.Base
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Kan using (hcom)
open import Core.Glue using (Glue; unglue)
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Transport.Properties using (is-prop-is-prop)
open import Core.Set using (prop-bi-impl→equiv)
open import Core.Equiv using (_≃_; aut)
open import Core.Function.Partial

private variable
  u v w x : Level
```


## Path between LiftM values

Two `LiftM` values are equal when their definedness types are
logically equivalent and their value functions agree through the
equivalence. Since both definedness types are propositions, logical
equivalence gives a type path via Glue. The `def-prop` field is
automatic by `is-prop-is-prop`, and the value field follows by
`hcom` with `unglue` at the base.

```agda
LiftM-path
  : ∀ {u v} {X : Type v}
  → (l r : LiftM u X)
  → (p : is-defined l → is-defined r)
  → (q : is-defined r → is-defined l)
  → (∀ d → value l d ≡ value r (p d))
  → l ≡ r
LiftM-path l r p q coh = path where
  Dl = is-defined l
  Dr = is-defined r
  e : Dl ≃ Dr
  e = prop-bi-impl→equiv (def-prop l) (def-prop r) p q

  Te : (i : I) → Partial (∂ i) (Σ T ∶ Type _ , T ≃ Dr)
  Te i (i = i0) = Dl , e
  Te i (i = i1) = Dr , aut

  path : l ≡ r
  path i .is-defined = Glue Dr (Te i)
  path i .def-prop =
    is-prop→PathP
      (λ i → is-prop-is-prop (Glue Dr (Te i)))
      (def-prop l) (def-prop r) i
  path i .value d =
    hcom (∂ i) λ where
      j (i = i0) → coh d (~ j)
      j (i = i1) → value r d
      j (j = i0) → value r (unglue (∂ i) {Te = Te i} d)
```


## Monad laws

At h-level 1, the monad laws are plain paths. Each uses
`LiftM-path` with the logical equivalence between propositional
definedness types and trivial value coherence.

### Left unit

Extending `f` over a fully-defined `η a` yields `f a`. The
definedness type contracts from `Σ (Lift ⊤) (λ _ → D)` to `D`.

```agda
♯-unitl
  : ∀ {u v w} {A : Type v} {B : Type w}
  → (f : A → LiftM u B) (a : A)
  → (f ♯) (η a) ≡ f a
♯-unitl f a = LiftM-path ((f ♯) (η a)) (f a)
  snd (λ d → liftℓ tt , d) (λ _ → refl)
```

### Right unit

Extending `η` over `a` yields `a`. The definedness type
contracts from `Σ D (λ _ → Lift ⊤)` to `D`.

```agda
♯-unitr
  : ∀ {u v} {A : Type v}
  → (a : LiftM u A)
  → (η ♯) a ≡ a
♯-unitr a = LiftM-path ((η ♯) a) a
  fst (λ d → d , liftℓ tt) (λ _ → refl)
```

### Associativity

Composing extensions `g ♯ ∘ f ♯` is the same as extending with
the composite `λ x → g ♯ (f x)`. The definedness types
reassociate from `Σ (Σ Da Df) Dg` to `Σ Da (λ p → Σ (Df p) Dg')`.

```agda
♯-assoc
  : ∀ {u v w x} {A : Type v} {B : Type w} {C : Type x}
  → (a : LiftM u A)
    (f : A → LiftM u B)
    (g : B → LiftM u C)
  → (g ♯) ((f ♯) a) ≡ ((λ x → (g ♯) (f x)) ♯) a
♯-assoc a f g = LiftM-path
  ((g ♯) ((f ♯) a)) (((λ x → (g ♯) (f x)) ♯) a)
  (λ ((p , d) , gd) → p , d , gd)
  (λ (p , d , gd) → (p , d) , gd)
  (λ _ → refl)
```
