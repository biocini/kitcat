A generic "coherence-via-contractibility" engine.

The pentagon, hexagon, syllepsis, and related coherence proofs for
virtual (and monoidal) categories all share one shape: two composites
of fiber-level paths agree because the fiber is contractible, and the
agreement is transported down to the hom level through a projection
`π` (typically `fst`). This module isolates that shape as a family of
`coh-project` combinators, one per truncation rung.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Coherence.Base where

open import Core.Type using (Level; Type)
open import Core.Base
open import Core.Kan using (pcom; is-contr→is-set; _∙_)
open import Core.Path.Base using (ap-comp)
open import Core.HLevel.Base using (is-groupoid; is-contr→is-hlevel)

private variable
  u v : Level
  F : Type u
  B : Type v
```

## Contractible types are groupoids

`is-groupoid = is-hlevel 3`, so the specialisation of
`is-contr→is-hlevel` at level `3` already has the desired type.

```agda
is-contr→is-groupoid : is-contr F → is-groupoid F
is-contr→is-groupoid = is-contr→is-hlevel 3
```

## Coherence projection

Given a contractible fiber `F`, any two parallel fiber paths `L R`
are equal; projecting that equality through `π` and re-expressing the
endpoints via `pL : ap π L ≡ L'` and `pR : ap π R ≡ R'` yields the
downstairs coherence `L' ≡ R'`. This is the pentagon rung.

```agda
coh-project
  : (c : is-contr F) (π : F → B)
  → {a b : F} (L R : a ≡ b) {L' R' : π a ≡ π b}
  → ap π L ≡ L' → ap π R ≡ R'
  → L' ≡ R'
coh-project c π L R pL pR =
  pcom pL (ap (ap π) (is-contr→is-set c _ _ L R)) pR
```

One rung up: two parallel fiber homotopies `P Q : L ≡ R` are equal
because `F` is a groupoid, and the same projection-and-re-expression
transports it to `P' ≡ Q'`. This is the syllepsis rung, obtained by
the identical construction at level `3`.

```agda
coh-project₃
  : (c : is-contr F) (π : F → B)
  → {a b : F} {L R : a ≡ b} (P Q : L ≡ R) {P' Q' : ap π L ≡ ap π R}
  → ap (ap π) P ≡ P' → ap (ap π) Q ≡ Q'
  → P' ≡ Q'
coh-project₃ c π P Q pP pQ =
  pcom pP (ap (ap (ap π)) (is-contr→is-groupoid c _ _ _ _ P Q)) pQ
```

## Glued coherence projection

The hexagon rung. Here the two fiber paths do not share a source: `L`
starts at `aᴸ` and `R` at `aᴿ`, bridged by `μ : aᴸ ≡ aᴿ`.
Contractibility identifies `L` with `μ ∙ R`; projecting and
re-expressing each leg via `pL`, `pR`, and the bridge `pμ : ap π μ ≡ e`
yields `L' ≡ e ∙ R'`. With `μ = refl` and `e = refl` this degenerates
(up to `refl ∙ R' ≡ R'`) to `coh-project`.

```agda
coh-project-glued
  : (c : is-contr F) (π : F → B)
  → {aᴸ aᴿ b : F} (μ : aᴸ ≡ aᴿ) (L : aᴸ ≡ b) (R : aᴿ ≡ b)
  → {L' : π aᴸ ≡ π b} {R' : π aᴿ ≡ π b} {e : π aᴸ ≡ π aᴿ}
  → ap π L ≡ L' → ap π R ≡ R' → ap π μ ≡ e
  → L' ≡ e ∙ R'
coh-project-glued c π μ L R pL pR pμ =
  pcom pL
    (ap (ap π) (is-contr→is-set c _ _ L (μ ∙ R)) ∙ ap-comp π μ R)
    (λ i → pμ i ∙ pR i)
```

