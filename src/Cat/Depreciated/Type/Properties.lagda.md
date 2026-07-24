Lane Biocini
July 2026

Presentation-comparison material for the representable axioms.
The record's interchange field is the ♭ form and instances prove
it in that shape; the pointwise-to-♭ closure below is the
nontrivial direction of the comparison between the two possible
presentations of the axiom — a J-tower over the fibers of `emb`,
agreeing with its input at `nrm` endpoints only propositionally.
Nothing on the spine routes through it: it lives here as the
material a presentation-equivalence theorem would consume.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Depreciated.Type.Properties where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Transport.J using (J)

open import Cat.Depreciated.Type

module _ {o h}
  (S : reflexive-graph o h)
  (let private module S = reflexive-graph S
       private module T = virtual S)
  (emb : ∀ {x y} → S.edge x y → T.composite x y)
  where

  open virtual S
  open representable S emb

  interchange♭-from
    : (∀ {x y z} (f : hom x y) (g : hom y z) → emb f ▾ g ≡ f ▴ emb g)
    → ∀ {x y z} {A : composite x y} {B : composite y z}
    → is-representable A → is-representable B → A ▿ B ≡ A ▵ B
  interchange♭-from ι {B = B} (m , p) (n , q) =
    J (λ F' _ → F' ▿ B ≡ F' ▵ B)
      (J (λ G' _ → emb m ▿ G' ≡ emb m ▵ G') (ι m n) q)
      p
```
