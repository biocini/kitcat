Lane Biocini
July 2026

Regression witnesses for the @identity ap-legs of the θ-core in
`Cat.Codep.Coherent`. The absorb-cell family slots hold an identity,
so `emb (idn x)` at the doubly-centered context reads back as
`post`/`pre`. These `refl` witnesses record the definitional
reductions θ-core relies on; if either stops firing, the θ-core
derivation breaks with it.

Untimestamped Test/ regression witness, imported manually by
`src/All.lagda.md` per the Test/ rules, so the reductions are
re-checked by every `just check-all`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.CodepCoherentKillchecks where

open import Core.Base using (_≡_; ap; refl)
open import Core.Data.Sigma.Type using (_,_)

open import Cat.Type using (category)
```

```agda
module _ {o h} (C : category o h) where
  open category C

  killcheck-apPost
    : ∀ {x}
    → ap (λ a' → emb (idn x) ((x , a') , (x , idn x))) (post-eval (idn x))
    ≡ ap (post (idn x)) (post-eval (idn x))
  killcheck-apPost = refl

  killcheck-apPre
    : ∀ {x}
    → ap (λ b' → emb (idn x) ((x , idn x) , (x , b'))) (post-eval (idn x))
    ≡ ap (pre (idn x)) (post-eval (idn x))
  killcheck-apPre = refl
```
