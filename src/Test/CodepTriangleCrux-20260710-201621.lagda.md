Spike: attempt to derive the codep triangle "crux" identity from the
five `hcategory` axiom fields alone. Scratch file — not in All.

The crux relates two constructions of the same left-unit path
`pre (idn y) (pre g b) ≡ pre g b`:

  * `absorb-l (pre g b)` — built from `unit-eqvl` + `pre-comp` + `idem`
  * the interchange route `happly (emb-idn-absorb g) δ₀` — built from
    `interchange` + `absorb-r` (= `unit-eqvr` + `post-comp` + `idem`).

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.CodepTriangleCrux-20260710-201621 where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (is-contr→is-prop; is-contr→is-set; _∙_; module Path)
open import Core.Transport.J using (subst; J)
open import Core.Function.Embedding
  using ( equiv→lc; equiv→lc-section
        ; is-embedding→ap-equiv; is-equiv→is-embedding )

open import Core.Path.Base using (ap-comp)
open import Core.Transport.Base using (transport-refl)

open import Cat.Type
```

## Generic helper: subst in a "left-varying endpoint" path family

```agda
subst-path-l
  : ∀ {u w} {A : Type u} {B : Type w} (Q : A → B)
    {a a' : A} {D : B} (e : a ≡ a') (P : Q a ≡ D)
  → subst (λ t → Q t ≡ D) e P ≡ sym (ap Q e) ∙ P
subst-path-l Q {D = D} e P =
  J (λ a'' e' → subst (λ t → Q t ≡ D) e' P ≡ sym (ap Q e') ∙ P)
    (transport-refl P ∙ sym (Path.unitl P)) e

sym-sym : ∀ {u} {A : Type u} {a b : A} (p : a ≡ b) → sym (sym p) ≡ p
sym-sym p = J (λ _ p → sym (sym p) ≡ p) refl p

sym-∙ : ∀ {u} {A : Type u} {a b d : A} (p : a ≡ b) (q : b ≡ d)
      → sym (p ∙ q) ≡ sym q ∙ sym p
sym-∙ {a = a} p q =
  J (λ _ q → sym (p ∙ q) ≡ sym q ∙ sym p)
    (ap sym (Path.unitr p) ∙ sym (Path.unitl (sym p))) q
```

## Setup

```agda
module _ {o h} (C : hcategory o h) where
  open hcategory C

  module crux-attempt {y z v : ob} (g : hom y z) (b : hom z v) where

    -- the doubly-centered context
    δ₀ : ctx y z
    δ₀ = ctr y , (v , b)

    c : hom y v
    c = pre g b

    -- the interchange-route path, read at δ₀. Its natural type
    -- (emb (idn y) · g) δ₀ ≡ emb g δ₀ is definitionally the left-unit
    -- path pre (idn y) c ≡ c.
    RHS : pre (idn y) c ≡ c
    RHS = happly (emb-idn-absorb g) δ₀

    -- the explicit crux right-hand side
    RHS-explicit : pre (idn y) c ≡ c
    RHS-explicit =
      interchange (idn y) g (idn y) b
      ∙ ap (λ a' → emb g ((y , a') , (v , b))) (absorb-r (idn y))

    -- (2) crux ⟺ crux' holds by refl: the happly reading of
    -- emb-idn-absorb g at δ₀ IS the explicit interchange expression.
    crux-iff : RHS-explicit ≡ RHS
    crux-iff = refl
```

## The goal, and its reduction to the residue R

`absorb-l c = equiv→lc unit-eqvl Qc` for a specific idempotency square
`Qc`, and `equiv→lc-section` computes `ap (pre (idn y)) (absorb-l c) = Qc`.
Since `pre (idn y)` is an equivalence, `ap (pre (idn y))` is injective,
so the whole crux collapses onto the single residue

    R : ap (pre (idn y)) RHS ≡ Qc.

```agda
    crux : absorb-l c ≡ RHS-explicit
    crux = crux' ∙ sym crux-iff
      where
      Qc : pre (idn y) (pre (idn y) c) ≡ pre (idn y) c
      Qc = sym (subst (λ t → pre t c ≡ pre (idn y) (pre (idn y) c))
                  idem (pre-comp (idn y) (idn y) c))

      -- absorb-l c unfolds (derived def, not a field) to
      -- equiv→lc unit-eqvl Qc, so its image under ap (pre (idn y)) is Qc.
      absorb-eq-lc : ap (pre (idn y)) (absorb-l c) ≡ Qc
      absorb-eq-lc = equiv→lc-section unit-eqvl Qc

      -- Split ap (pre (idn y)) RHS over the ∙ in RHS. RHS is
      -- definitionally IC ∙ AR with:
      IC : pre (idn y) c ≡ emb g ((y , post (idn y) (idn y)) , (v , b))
      IC = interchange (idn y) g (idn y) b

      AR : emb g ((y , post (idn y) (idn y)) , (v , b)) ≡ c
      AR = ap (λ a' → emb g ((y , a') , (v , b))) (absorb-r (idn y))

      -- Qc simplifies (subst-path-l + sym algebra) to
      --   sym (pre-comp (idn y) (idn y) c) ∙ ap (λ t → pre t c) idem,
      -- a path E(E c) → pre (idn⨾idn) c → E c through the emb-comp
      -- square pre-comp and the idempotency idem : idn⨾idn ≡ idn y.
      Qc-simp
        : Qc ≡ sym (pre-comp (idn y) (idn y) c) ∙ ap (λ t → pre t c) idem
      Qc-simp =
          ap sym (subst-path-l (λ t → pre t c) idem (pre-comp (idn y) (idn y) c))
        ∙ sym-∙ (sym (ap (λ t → pre t c) idem)) (pre-comp (idn y) (idn y) c)
        ∙ ap (sym (pre-comp (idn y) (idn y) c) ∙_)
            (sym-sym (ap (λ t → pre t c) idem))

      -- STUCK: the true minimal residue.
      --
      -- Goal (both sides : E(E c) ≡ E c, E := pre (idn y), c := pre g b):
      --
      --   ap (pre (idn y)) IC ∙ ap (pre (idn y)) AR
      --     ≡ sym (pre-comp (idn y) (idn y) c) ∙ ap (λ t → pre t c) idem
      --
      -- LHS routes through  E PG,  PG := emb g ((y , post (idn y)(idn y)) , (v , b));
      -- RHS routes through  pre (idn⨾idn) c.
      -- The two intermediate points differ, so this is NOT term-by-term
      -- path algebra: it requires reconciling the `interchange` application
      -- inside IC (and the `absorb-r` inside AR) with the `interchange`
      -- content buried in `idem` (idem = comp-eq ∙ post-eval, and comp-eq
      -- itself is post-comp-from-coupling, i.e. one `interchange`). Both
      -- sides ultimately trace to compose-contr + interchange + the right-unit
      -- equivalence, but matching them is a contractible-fiber coherence of
      -- the same shape as the associativity tower — not closable by direct
      -- ∙-manipulation. Pushed to here from BOTH routes (equiv→lc cancellation
      -- and the Route-1 fiber square, which give the identical obligation).
      R-core : ap (pre (idn y)) IC ∙ ap (pre (idn y)) AR ≡ Qc
      R-core = {!!}

      R : ap (pre (idn y)) RHS ≡ Qc
      R = ap-comp (pre (idn y)) IC AR ∙ R-core

      crux' : absorb-l c ≡ RHS
      crux' =
        equiv→lc (is-embedding→ap-equiv (is-equiv→is-embedding unit-eqvl))
          (absorb-eq-lc ∙ sym R)
```
