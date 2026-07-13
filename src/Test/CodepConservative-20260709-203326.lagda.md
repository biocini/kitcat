# Conservativity countermodels for `Cat.Codep`

> **Pending re-migration (axiom merge, 2026-07).** Predates the merge
> of the coupling/unit axioms into `codep-axioms`. The three direct
> countermodels (`Bℤ2`, `AndM`, `Bℤ2'`) fill only `compose-contr`; the
> merged five-field record now also demands `interchange`, `post-eval`,
> `unit-eqvl`, `unit-eqvr`. These hold (all three are genuine
> commutative groups/monoids); fills are mechanical — `post-eval` is
> `refl`/`xor.unitr`, units are `iso→equiv`, `interchange` a 16-case
> `refl` each — but add ~70 lines. Because these homs are `Bool` (a
> *set*, not a prop), `interchange` needs real xor/∧ algebra, unlike
> the thin `walking-arrow` (props → one-liners): evidence the merged
> record raises the bar for set-hom countermodels. The `walking-arrow`
> (thin, all cells) is now green in `Cat.Codep.Instances`. Re-migration
> tracked as a follow-up.

Does the representable codependent formulation secretly force a
groupoid-only theory, or force `emb` to be an equivalence? No. This
file exhibits independent countermodels refuting each danger, and a
polymorphic path instance certifying that no truncation assumption
leaks into the new foundation.

`emb`-equivalence and groupoid-ness are **independent** axes:

| | `emb` an equivalence | `emb` has a gap |
| --- | --- | --- |
| **groupoid** | path types (W3) | `Bℤ/2` (W2) |
| **non-groupoid** | walking arrow → Instances | meet monoid (W1) |

The h-level shift `emb` induces (paths at level 0, virtual `emb` at
level 1) is about **parametricity**, not invertibility. Witness 1
delivers the non-groupoid refutation single-object; the thin
`emb`-equivalence cell — the walking arrow — is now landed in
`Cat.Codep.Instances.WalkingArrow` (the trilayer split made the direct
multi-object instance termination-safe). Witnesses 4–5 stress the
fragments: W4 that the identity is posited, not characterized (with a
gauge surprise), and W5 that the pentagon tower is generic across alien
instances.

This file is trilayer-current: each direct instance is a
`codep-structure` + `codep-axioms` + `codep-category` bundle triple;
the proof bodies are unchanged from the original single-record version.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.CodepConservative-20260709-203326 where

open import Core.Type
open import Core.Base
open import Core.Kan using (_∙_)
open import Core.Data.Sigma
open import Core.Data.Empty using (⊥; ¬_)
open import Core.Data.Bool.Type using (Bool; true; false)
open import Core.Data.Bool.Base using (xor; and)
import Core.Data.Bool.Properties as BP
open import Core.Transport.J using (subst)
open import Core.Transport.Properties
  using (prop-inhabited→is-contr; is-prop→is-set)
open import Core.HLevel.Base using (Π-is-set)
open import Core.Function.Embedding using (injective→is-embedding; injective)

open import Cat.Type using (category)
open import Cat.Groupoid using (∞-groupoid)
open import Cat.Codep
open import Cat.Codep.Instances using (module TypeInstance)
absurd : ∀ {u} {A : Type u} → ⊥ → A
absurd ()

true≢false : ¬ (true ≡ false)
true≢false p = subst F p tt
  where
    F : Bool → Type
    F true  = ⊤
    F false = ⊥
module W3 {u} {A : Type u} where
  private module T = TypeInstance (∞-groupoid A)

  path-cat : codep-category u u
  path-cat = T.Type-cat

  path-coupling : codep-coupling T.Type-structure
  path-coupling = T.Type-coupling

  path-unit : codep-unit T.Type-structure path-coupling
  path-unit = T.Type-unit
module W2 where
  -- The derived context and composite for the one-object carrier,
  -- spelled out: `acted φ tt` and `fam (γ .fst)` both reduce to `Bool`.
  CtxB : Type
  CtxB = Σ φ ∶ (⊤ × (Σ w ∶ ⊤ , Bool)) , Bool

  CompB : Type
  CompB = CtxB → Bool

  -- a xor g xor c: the two legs bracket the operator.
  embB : Bool → CompB
  embB g ((_ , (_ , a)) , c) = xor g (xor a c)

  -- emb is injective: evaluation at the unit context recovers g.
  embB-inj : ∀ {h h'} → embB h ≡ embB h' → h ≡ h'
  embB-inj {h} {h'} q =
      sym (BP.xor.unitr h)
    ∙ happly q ((tt , (tt , false)) , false)
    ∙ BP.xor.unitr h'

  Bℤ2-str : codep-structure {0ℓ} {0ℓ} ⊤
  Bℤ2-str .codep-structure.hom _ _ = Bool
  Bℤ2-str .codep-structure.idn _ = false
  Bℤ2-str .codep-structure.emb g = embB g

  Bℤ2-ax : codep-axioms Bℤ2-str
  Bℤ2-ax .codep-axioms.compose-contr f g =
    prop-inhabited→is-contr fib-prop pt
    where
      fib-prop : is-prop (fiber embB _)
      fib-prop = injective→is-embedding (Π-is-set (λ _ → BP.set)) embB embB-inj _

      pt : fiber embB _
      pt = xor f g , funext λ where
        ((_ , (_ , a)) , c) →
            sym (BP.xor.assoc f g (xor a c))
          ∙ ap (xor f) ( BP.xor.assoc g a c
                       ∙ ap (λ t → xor t c) (BP.xor.comm g a)
                       ∙ sym (BP.xor.assoc a g c) )
          ∙ ap (λ t → xor f (xor a (xor g t))) (sym (BP.xor.unitl c))

  Bℤ2 : codep-category 0ℓ 0ℓ
  Bℤ2 .codep-category.ob = ⊤
  Bℤ2 .codep-category.structure = Bℤ2-str
  Bℤ2 .codep-category.axioms = Bℤ2-ax

  -- The constant-false operator: not in the image of `embB`, so `emb`
  -- is not surjective — a gap, in a groupoid (`xor` inverts everything).
  gap : Σ F ∶ CompB , ¬ (fiber embB F)
  gap = Fconst , not-rep
    where
      Fconst : CompB
      Fconst _ = false

      not-rep : ¬ (fiber embB Fconst)
      not-rep (g , p) =
        true≢false (sym (ap (λ b → xor b true) g≡false) ∙ happly p γ1)
        where
          γ0 γ1 : CtxB
          γ0 = (tt , (tt , false)) , false
          γ1 = (tt , (tt , true)) , false
          g≡false : g ≡ false
          g≡false = sym (BP.xor.unitr g) ∙ happly p γ0
module W1 where
  CtxA : Type
  CtxA = Σ φ ∶ (⊤ × (Σ w ∶ ⊤ , Bool)) , Bool

  CompA : Type
  CompA = CtxA → Bool

  -- (a ∧ c) ∧ g: at the all-true unit context this is g.
  embA : Bool → CompA
  embA g ((_ , (_ , a)) , c) = and (and a c) g

  embA-inj : ∀ {h h'} → embA h ≡ embA h' → h ≡ h'
  embA-inj q = happly q ((tt , (tt , true)) , true)

  AndM-str : codep-structure {0ℓ} {0ℓ} ⊤
  AndM-str .codep-structure.hom _ _ = Bool
  AndM-str .codep-structure.idn _ = true
  AndM-str .codep-structure.emb g = embA g

  AndM-ax : codep-axioms AndM-str
  AndM-ax .codep-axioms.compose-contr f g =
    prop-inhabited→is-contr fib-prop pt
    where
      fib-prop : is-prop (fiber embA _)
      fib-prop = injective→is-embedding (Π-is-set (λ _ → BP.set)) embA embA-inj _

      pt : fiber embA _
      pt = and f g , funext λ where
        ((_ , (_ , a)) , c) →
            ap (and (and a c)) (BP.and.comm f g)
          ∙ BP.and.assoc (and a c) g f
          ∙ ap (λ t → and t f) (sym (BP.and.assoc a c g))

  AndM : codep-category 0ℓ 0ℓ
  AndM .codep-category.ob = ⊤
  AndM .codep-category.structure = AndM-str
  AndM .codep-category.axioms = AndM-ax

  open codep-category AndM

  -- `false` has no inverse: every candidate `inv` would force
  -- `inv ⨾ false = and inv false ≡ true`, but `and _ false` is `false`.
  no-inverse
    : ¬ (Σ inv ∶ hom tt tt
             , (inv ⨾ false ≡ idn tt) × (false ⨾ inv ≡ idn tt))
  no-inverse (true  , p , _) = true≢false (sym p)
  no-inverse (false , p , _) = true≢false (sym p)
module W5 where
  module _ (f g h k : Bool) where
    _ = Pentagon5.pentagon W2.Bℤ2-ax {tt} {tt} {tt} {tt} {tt} f g h k
    _ = Pentagon5.pentagon W1.AndM-ax {tt} {tt} {tt} {tt} {tt} f g h k
module W4 where
  open W2 using (embB; embB-inj)

  Bℤ2'-str : codep-structure {0ℓ} {0ℓ} ⊤
  Bℤ2'-str .codep-structure.hom _ _ = Bool
  Bℤ2'-str .codep-structure.idn _ = true
  Bℤ2'-str .codep-structure.emb g = embB g

  Bℤ2'-ax : codep-axioms Bℤ2'-str
  Bℤ2'-ax .codep-axioms.compose-contr f g =
    prop-inhabited→is-contr fib-prop pt
    where
      fib-prop : is-prop (fiber embB _)
      fib-prop = injective→is-embedding (Π-is-set (λ _ → BP.set)) embB embB-inj _

      -- The twisted composite `f xor g xor true`; the equation is a
      -- xor-identity in the four legs, so each concrete case is refl.
      twist : ∀ p q r s
        → xor (xor (xor p q) true) (xor r s)
        ≡ xor p (xor r (xor q (xor true s)))
      twist false false false false = refl
      twist false false false true  = refl
      twist false false true  false = refl
      twist false false true  true  = refl
      twist false true  false false = refl
      twist false true  false true  = refl
      twist false true  true  false = refl
      twist false true  true  true  = refl
      twist true  false false false = refl
      twist true  false false true  = refl
      twist true  false true  false = refl
      twist true  false true  true  = refl
      twist true  true  false false = refl
      twist true  true  false true  = refl
      twist true  true  true  false = refl
      twist true  true  true  true  = refl

      pt : fiber embB _
      pt = xor (xor f g) true , funext λ where
        ((_ , (_ , a)) , c) → twist f g a c

  Bℤ2' : codep-category 0ℓ 0ℓ
  Bℤ2' .codep-category.ob = ⊤
  Bℤ2' .codep-category.structure = Bℤ2'-str
  Bℤ2' .codep-category.axioms = Bℤ2'-ax

  -- The gauge: `post-eval` survives the wrong anchor. `post f (idn) =
  -- f xor (true xor true) = f xor false = f`.
  open codep-category Bℤ2' using (idn)

  gauge-post-eval : ∀ f → Helpers.post Bℤ2'-str f (idn tt) ≡ f
  gauge-post-eval f = BP.xor.unitr f
```
