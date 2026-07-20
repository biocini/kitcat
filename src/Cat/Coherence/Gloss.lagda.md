Lane Biocini
July 2026

A gloss on `Cat.Coherence`: the elementary form of the
nrm-straightening. The main line proves `assoc●-nrm` by the
`nrm-slide` connection — each witness rides its own path back to
normal form along an `∧`-connection, so both endpoints of the
straightening are definitional and its displaced mate is the same
slide one level up. That argument is cubical through and through:
it needs interval connections and the type-directed boundary
reduction of `PathP`, neither of which exists in standard MLTT.

This module records the transport-only construction: one `J` per
witness path component, innermost first. It is the port source
for an elementary presentation — with the straightening in this
form, every other leaf of the pentagon's `∙`-tree (`ap-comp`,
`is-contr→is-set`, the whiskers) is already J-expressible, so the
object-level coherence suite transfers to MLTT verbatim. The cost
the slide avoids shows up here as computation: the `J`s reduce
only propositionally (`J-refl`), so neither endpoint is strict,
and the `∙ refl` tails of the `●`-witnesses survive to be
discharged by whoever consumes the endpoints.

The two constructions share their type and are interchangeable
under `pentagon`'s tree, which consumes the lemma only through
its value. No agreement cell between them is stated: bridging two
straightenings of the same projection is exactly the fst-wobble
the one-construction discipline exists to avoid, and nothing
consumes such a bridge.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Coherence.Gloss where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.J using (J)

open import Cat.Type
open import Cat.Base

module _ {o h} (C : category o h) where
  open category C
  open theory C

  assoc●-nrm
    : ∀ {x y z w} {A : composite x y} {B : composite y z} {C : composite z w}
      (U : is-representable A) (V : is-representable B) (W : is-representable C)
    → assoc● U V W ≡ assoc (U .fst) (V .fst) (W .fst)
  assoc●-nrm (m , p) (n , q) (o , r) =
      J (λ _ r' → assoc● (m , p) (n , q) (o , r') ≡ assoc● (m , p) (n , q) (nrm o)) refl r
    ∙ J (λ _ q' → assoc● (m , p) (n , q') (nrm o) ≡ assoc● (m , p) (nrm n) (nrm o)) refl q
    ∙ J (λ _ p' → assoc● (m , p') (nrm n) (nrm o) ≡ assoc● (nrm m) (nrm n) (nrm o)) refl p
```
