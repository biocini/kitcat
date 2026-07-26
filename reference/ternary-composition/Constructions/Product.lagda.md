Lane Biocini
March 2026

Product category. Given `C : category o₁ h₁` and `D : category o₂ h₂`,
construct `C ×Cat D : category (o₁ ⊔ o₂) (h₁ ⊔ h₂)` with componentwise
objects, morphisms, and ternary composition. The `unit` and `interchange`
fields are componentwise. The `compose-contr` contraction uses a
`comp` through the contractible total space to fill the gap between
dummy-projected component fibers and the original path.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Product where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv.Base using (is-equiv; eqv-fibers)
open import Cat.Virtual

```

## Helpers

Componentwise equivalence: `is-equiv f` and `is-equiv g` imply
`is-equiv (λ (a,b) → (f a, g b))`.

```agda
private
  ×-is-equiv
    : ∀ {u₁ v₁ u₂ v₂}
      {A₁ : Type u₁} {B₁ : Type v₁}
      {A₂ : Type u₂} {B₂ : Type v₂}
      {f : A₁ → B₁} {g : A₂ → B₂}
    → is-equiv f → is-equiv g
    → is-equiv
        (λ (x : A₁ × A₂) → f (fst x) , g (snd x))
  ×-is-equiv {f = f} {g} ef eg .eqv-fibers (b₁ , b₂)
    .center =
    (fc .center .fst , gc .center .fst)
    , λ i → fc .center .snd i , gc .center .snd i
    where
      fc = ef .eqv-fibers b₁
      gc = eg .eqv-fibers b₂
  ×-is-equiv {f = f} {g} ef eg .eqv-fibers (b₁ , b₂)
    .paths ((a₁ , a₂) , p) i =
    ( q₁ i .fst , q₂ i .fst )
    , λ j → q₁ i .snd j , q₂ i .snd j
    where
      fc = ef .eqv-fibers b₁
      gc = eg .eqv-fibers b₂
      q₁ = fc .paths (a₁ , λ j → fst (p j))
      q₂ = gc .paths (a₂ , λ j → snd (p j))
```

In a contractible total space `Σ B`, two elements of a fiber `B a`
are connected. The path goes backwards from `(a, b₁)` and `(a, b₂)`
to the contractible center, then `comp` pushes the dependent paths
into the fiber over `a`.

```agda
  contr-total→fiber-prop
    : ∀ {u v} {A : Type u} {B : A → Type v}
    → is-contr (Σ B) → (a : A) → is-prop (B a)
  contr-total→fiber-prop {B = B} cc a b₁ b₂ i = {!!}
    -- com (λ k → B (face k i)) {∂ i}
    --   (λ k → λ where
    --     (i = i0) → snd (p₁ k)
    --     (i = i1) → snd (p₂ k))
    --   (snd (cc .center))
    -- where
    --   p₁ = cc .paths (a , b₁)
    --   p₂ = cc .paths (a , b₂)
    --   face : I → I → _
    --   face k i = hfil (∂ i) k λ where
    --     j (i = i0) → fst (p₁ j)
    --     j (i = i1) → fst (p₂ j)
    --     j (j = i0) → fst (p₂ j)
```

## The product category

```agda
module _ {o₁ h₁ o₂ h₂}
  (C : category o₁ h₁) (D : category o₂ h₂) where
  private
    module C = Cat C
    module D = Cat D

  -- _×Cat_ : category (o₁ ⊔ o₂) (h₁ ⊔ h₂)
  -- _×Cat_ .category.ob = C.ob × D.ob
  -- _×Cat_ .category.hom (x₁ , x₂) (y₁ , y₂) =
  --   C.hom x₁ y₁ × D.hom x₂ y₂
  -- _×Cat_ .category.emb (f₁ , f₂)
  --   (w₁ , w₂) (a₁ , a₂) (z₁ , z₂) (b₁ , b₂) =
  --   C.emb f₁ w₁ a₁ z₁ b₁ , D.emb f₂ w₂ a₂ z₂ b₂
  -- _×Cat_ .category.unit =
  --   (C.idn , D.idn)
  --   , ( ×-is-equiv
  --         (C.unit .snd .fst .fst)
  --         (D.unit .snd .fst .fst)
  --     , ×-is-equiv
  --         (C.unit .snd .fst .snd)
  --         (D.unit .snd .fst .snd) )
  --   , (λ (h₁ , h₂) i →
  --       C.unit .snd .snd .fst h₁ i
  --       , D.unit .snd .snd .fst h₂ i)
  --   , (λ (g₁ , g₂) i →
  --       C.unit .snd .snd .snd g₁ i
  --       , D.unit .snd .snd .snd g₂ i)
```

### Compose-contr

The center is componentwise. The contraction goes in two steps:
first, use the component fiber contractions with fixed dummies to
reach a midpoint; then use `contr-total→fiber-prop` on each
component fiber to fill from midpoint to target.

```agda
--   _×Cat_ .category.compose-contr
--     {x₁ , x₂} {_ , _} {z₁ , z₂}
--     (f₁ , f₂) (g₁ , g₂) .center =
--     (cc₁ .center .fst , cc₂ .center .fst)
--     , λ i (w₁ , w₂) (a₁ , a₂) (v₁ , v₂) (b₁ , b₂) →
--         cc₁ .center .snd i w₁ a₁ v₁ b₁
--         , cc₂ .center .snd i w₂ a₂ v₂ b₂
--     where
--       cc₁ = C.compose-contr f₁ g₁
--       cc₂ = D.compose-contr f₂ g₂
--   _×Cat_ .category.compose-contr
--     {x₁ , x₂} {_ , _} {z₁ , z₂}
--     (f₁ , f₂) (g₁ , g₂) .paths ((s₁ , s₂) , p) =
--     step₁ ∙ step₂
--     where
--       cc₁ = C.compose-contr f₁ g₁
--       cc₂ = D.compose-contr f₂ g₂

--       v-fib : fiber C.emb
--         (λ w₁ a₁ v₁ b₁ →
--           C.emb f₁ w₁ a₁ v₁ (C.noy g₁ v₁ b₁))
--       v-fib =
--         s₁ , λ j w₁ a₁ v₁ b₁ →
--           fst (p j (w₁ , x₂) (a₁ , D.idn)
--                  (v₁ , z₂) (b₁ , D.idn))

--       w-fib : fiber D.emb
--         (λ w₂ a₂ v₂ b₂ →
--           D.emb f₂ w₂ a₂ v₂ (D.noy g₂ v₂ b₂))
--       w-fib =
--         s₂ , λ j w₂ a₂ v₂ b₂ →
--           snd (p j (x₁ , w₂) (C.idn , a₂)
--                  (z₁ , v₂) (C.idn , b₂))

--       q₁ : cc₁ .center ≡ v-fib
--       q₁ = cc₁ .paths v-fib

--       q₂ : cc₂ .center ≡ w-fib
--       q₂ = cc₂ .paths w-fib

--       mid = ( (s₁ , s₂)
--             , λ j (w₁ , w₂) (a₁ , a₂)
--                   (v₁ , v₂) (b₁ , b₂) →
--                 v-fib .snd j w₁ a₁ v₁ b₁
--                 , w-fib .snd j w₂ a₂ v₂ b₂ )

--       step₁ : _ ≡ mid
--       step₁ i =
--         (q₁ i .fst , q₂ i .fst)
--         , λ j (w₁ , w₂) (a₁ , a₂)
--               (v₁ , v₂) (b₁ , b₂) →
--             q₁ i .snd j w₁ a₁ v₁ b₁
--             , q₂ i .snd j w₂ a₂ v₂ b₂
-- ```

-- For step₂, both endpoints have `.fst = (s₁, s₂)`. The `.snd`
-- difference is between the dummy-projected component paths and the
-- original `p`. Since `cc₁` and `cc₂` are contractible, their fibers
-- over `s₁` and `s₂` are propositional by `contr-total→fiber-prop`.
-- So the two `.snd` paths agree pointwise.

-- ```agda
--       c-prop
--         : (α β : C.emb s₁
--           ≡ (λ w₁ a₁ v₁ b₁ →
--               C.emb f₁ w₁ a₁ v₁ (C.noy g₁ v₁ b₁)))
--         → α ≡ β
--       c-prop = contr-total→fiber-prop cc₁ s₁

--       d-prop
--         : (α β : D.emb s₂
--           ≡ (λ w₂ a₂ v₂ b₂ →
--               D.emb f₂ w₂ a₂ v₂ (D.noy g₂ v₂ b₂)))
--         → α ≡ β
--       d-prop = contr-total→fiber-prop cc₂ s₂

--       step₂ : mid ≡ ((s₁ , s₂) , p)
--       step₂ i =
--         (s₁ , s₂)
--         , λ j (w₁ , w₂) (a₁ , a₂)
--               (v₁ , v₂) (b₁ , b₂) →
--             c-prop
--               (λ j w₁ a₁ v₁ b₁ →
--                 v-fib .snd j w₁ a₁ v₁ b₁)
--               (λ j w₁ a₁ v₁ b₁ →
--                 fst (p j (w₁ , w₂) (a₁ , a₂)
--                        (v₁ , v₂) (b₁ , b₂)))
--               i j w₁ a₁ v₁ b₁
--             , d-prop
--               (λ j w₂ a₂ v₂ b₂ →
--                 w-fib .snd j w₂ a₂ v₂ b₂)
--               (λ j w₂ a₂ v₂ b₂ →
--                 snd (p j (w₁ , w₂) (a₁ , a₂)
--                        (v₁ , v₂) (b₁ , b₂)))
--               i j w₂ a₂ v₂ b₂
-- ```

-- ### Interchange

-- Interchange is componentwise, since `noy` and `yon` in the product
-- category compute componentwise from the component `noy` and `yon`.

-- ```agda
--   _×Cat_ .category.interchange
--     (f₁ , f₂) (g₁ , g₂)
--     (w₁ , w₂) (a₁ , a₂) (v₁ , v₂) (b₁ , b₂) i =
--     C.interchange f₁ g₁ w₁ a₁ v₁ b₁ i
--     , D.interchange f₂ g₂ w₂ a₂ v₂ b₂ i
-- ```
