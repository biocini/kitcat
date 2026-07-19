Lane Biocini
July 2026

The morphism-level derived theory of a `Cat.Monoidal` category:
functoriality of the derived 2-cell tensor `_⊗₁_` in vertical
composition.

Both sides of `⊗₁-preserves-⨾` inhabit the contractible fiber of
hom-level spines. Any fiber element `(σ , p)` extends to a full
`⊗₁-spine`: the post side is the pre side composed with
`⊗₁-interchange`, and the 2-cell is the Kan lid over the object
spine's square. The fiber is therefore contractible by projection
from `⊗₁-spine-contr`, and the interchange law is the `ap fst` of
the center agreeing with the composite side.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal.Bifunctor where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.J using (subst)
open import Core.Path.Base
open import Core.Transport.Base using (module Path-over; transport)

open import Cat.Type
import Cat.Base
open import Cat.Morphism
open import Cat.Monoidal

module _ {o h} {C : category o h} (M : monoidal C) where
  open monoidal M
  open Cat.Monoidal.theory M
  private module C = category C
  private module Ct = Cat.Base.theory C
```

## Pasting PathPs over composable object paths

`compHomP` concatenates two `C.hom`-valued `PathP`s displaced over
composable object paths. It is the two-object image of the standard
`compPathP`, gluing along the `cat.fill` fillers of the two `_∙_`s
with a single heterogeneous `com`.

```agda
  private
    compHomP
      : {a₀ a₁ a₂ : C.ob} (pa : a₀ ≡ a₁) (qa : a₁ ≡ a₂)
        {b₀ b₁ b₂ : C.ob} (pb : b₀ ≡ b₁) (qb : b₁ ≡ b₂)
        {h₀ : C.hom a₀ b₀} {h₁ : C.hom a₁ b₁} {h₂ : C.hom a₂ b₂}
      → PathP (λ i → C.hom (pa i) (pb i)) h₀ h₁
      → PathP (λ i → C.hom (qa i) (qb i)) h₁ h₂
      → PathP (λ i → C.hom ((pa ∙ qa) i) ((pb ∙ qb) i)) h₀ h₂
    compHomP pa qa pb qb {h₀ = h₀} P Q i =
      com (λ j → C.hom (fa j i) (fb j i)) (∂ i) λ where
        j (i = i0) → h₀
        j (i = i1) → Q j
        j (j = i0) → P i
      where
        fa : (j i : _) → C.ob
        fa j i = cat.fill pa qa i j
        fb : (j i : _) → C.ob
        fb j i = cat.fill pb qb i j
```

## The tensor composition coherence

The object spine's 2-cell relates the two composite comparisons
`⊗₀-emb-comp` and `⊗₀-emb-comp-op` along `⊗₀-interchange`. It is
part of the object-level API of `Cat.Monoidal` as `⊗₀-emb-comp-coh`,
with `⊗coh→∙` its `_∙_`-form corollary.

## Collapsing a vertical composite of pre-actions

```agda
  ⊗₁-pre-comp
    : ∀ {y y'} (ψ : C.hom y y') {y''} (ψ' : C.hom y' y'')
        {r r'} (β : C.hom r r')
    → (⊗₁-pre ψ β) Ct.⨾ (⊗₁-pre ψ' (C.idn r')) ≡ ⊗₁-pre (ψ Ct.⨾ ψ') β
  ⊗₁-pre-comp {y} {y'} ψ {y''} ψ' {r} {r'} β =
      sym (⊗₁-bifunctor ψ ψ' (C.idn I) (C.idn I) β (C.idn r'))
    ∙ (λ i → ⊗₁-emb (ψ Ct.⨾ ψ') (Ct.idem {I} i , Ct.unitr β i))
```

## The contractible hom-level fiber

A spine candidate `σ` with the pre-side characterization extends to a
full `⊗₁-spine`: the post side is the pre side pasted with
`⊗₁-interchange` along `⊗coh→∙`, and the 2-cell is the Kan lid whose
vertical faces are the two characterizations. The fiber is thus
contractible by projection from `⊗₁-spine-contr`.

```agda
  module hfiber {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y') where

    p-char : C.hom (x ⊗ y) (x' ⊗ y') → Type (o ⊔ h)
    p-char σ = ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
             → PathP (λ j → C.hom (happly (⊗₀-emb-comp x y) (l , r) j)
                                  (happly (⊗₀-emb-comp x' y') (l' , r') j))
                     (⊗₁-emb σ (α , β))
                     (⊗₁-emb φ (α , ⊗₁-pre ψ β))

    q-char : C.hom (x ⊗ y) (x' ⊗ y') → Type (o ⊔ h)
    q-char σ = ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
             → PathP (λ j → C.hom (happly (⊗₀-emb-comp-op x y) (l , r) j)
                                  (happly (⊗₀-emb-comp-op x' y') (l' , r') j))
                     (⊗₁-emb σ (α , β))
                     (⊗₁-emb ψ (⊗₁-post φ α , β))

    -- extend-q : ∀ {σ} → p-char σ → q-char σ

    -- extend-θ
    --   : ∀ {σ} (pc : p-char σ)
    --   → ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
    --   → PathP
    --       (λ i → PathP
    --         (λ j → C.hom (⊗₀-emb-comp-coh x y i j (l , r))
    --                       (⊗₀-emb-comp-coh x' y' i j (l' , r')))
    --         (⊗₁-emb σ (α , β))
    --         (⊗₁-interchange φ ψ α β i))
    --       (pc α β) (extend-q pc α β)

    -- extend-q {σ} pc α β j = extend-θ pc α β i1 j
    -- extend-θ {σ} pc {l} {l'} α {r} {r'} β i j = ?


    hfiber-contr : is-contr (Σ σ ∶ C.hom (x ⊗ y) (x' ⊗ y') , p-char σ)
    hfiber-contr .center =
      (φ ⊗₁ ψ) , ⊗₁-emb-comp φ ψ
    hfiber-contr .paths (σ , pc) i =
      {!!} -- Φ i .fst , Φ i .snd .fst
      -- where
        -- Φ : ⊗₁-spine-contr φ ψ .center ≡ (σ , pc , extend-q pc , extend-θ pc)
        -- Φ = ⊗₁-spine-contr φ ψ .paths (σ , pc , extend-q pc , extend-θ pc)
```

## Functoriality of the derived 2-cell tensor

Both sides inhabit the contractible `hfiber`: the left side is its
center, and the composite side satisfies the characterization by
gluing three links — two `⊗₁-bifunctor` rewrites sandwiching the
side-by-side paste of the two spine characterizations, with
`⊗₁-pre-comp` collapsing the doubled pre-action.

```agda
  ⊗₁-preserves-⨾
    : ∀ {x x'} (φ : C.hom x x') {x''} (φ' : C.hom x' x'')
        {y y'} (ψ : C.hom y y') {y''} (ψ' : C.hom y' y'')
    → (φ Ct.⨾ φ') ⊗₁ (ψ Ct.⨾ ψ') ≡ (φ ⊗₁ ψ) Ct.⨾ (φ' ⊗₁ ψ')
  ⊗₁-preserves-⨾ {x} {x'} φ {x''} φ' {y} {y'} ψ {y''} ψ' = {!!}
    -- ap fst
    --   (is-contr→is-prop
    --     (hfiber.hfiber-contr M (φ Ct.⨾ φ') (ψ Ct.⨾ ψ'))
    --     (hfiber.hfiber-contr M (φ Ct.⨾ φ') (ψ Ct.⨾ ψ') .center)
    --     ((φ ⊗₁ ψ) Ct.⨾ (φ' ⊗₁ ψ') , rhs-charac))
    -- where
      -- disp₂ : ∀ {l l' r r'} → Type h
      -- disp₂ {l} {l'} {r} {r'} = ?
      --   --  C.hom (⊗₀-emb (x ⊗ y) (l , r)) (⊗₀-emb (x'' ⊗ y'') (l' , r'))
      --   --  ≡ C.hom (⊗₀-emb x (⊗sub y (l , r))) (⊗₀-emb x'' (⊗sub y'' (l' , r')))

      -- rhs-charac
      --   : hfiber.p-char M (φ Ct.⨾ φ') (ψ Ct.⨾ ψ')
      --       ((φ ⊗₁ ψ) Ct.⨾ (φ' ⊗₁ ψ'))
      -- rhs-charac {l} {l'} α {r} {r'} β =
      --   Path-over.to-pathp
      --     ( ap (transport disp₂) link-pre
      --     ∙ Path-over.from-pathp mid
      --     ∙ suf )
      --   where
      --     link-pre
      --       : ⊗₁-emb ((φ ⊗₁ ψ) Ct.⨾ (φ' ⊗₁ ψ')) (α , β)
      --       ≡ ⊗₁-emb (φ ⊗₁ ψ) (α , β)
      --         Ct.⨾ ⊗₁-emb (φ' ⊗₁ ψ') (C.idn l' , C.idn r')
      --     link-pre =
      --         (λ i → ⊗₁-emb ((φ ⊗₁ ψ) Ct.⨾ (φ' ⊗₁ ψ'))
      --                  (Ct.unitr α (~ i) , Ct.unitr β (~ i)))
      --       ∙ ⊗₁-bifunctor (φ ⊗₁ ψ) (φ' ⊗₁ ψ')
      --           α (C.idn l') β (C.idn r')

      --     mid : PathP (λ i → disp₂)
      --             ( ⊗₁-emb (φ ⊗₁ ψ) (α , β)
      --               Ct.⨾ ⊗₁-emb (φ' ⊗₁ ψ') (C.idn l' , C.idn r') )
      --             ( ⊗₁-emb φ (α , ⊗₁-pre ψ β)
      --               Ct.⨾ ⊗₁-emb φ' (C.idn l' , ⊗₁-pre ψ' (C.idn r')) )
      --     mid i =
      --       ⊗₁-emb-comp φ ψ α β i
      --       Ct.⨾ ⊗₁-emb-comp φ' ψ' (C.idn l' , C.idn r') i

      --     suf
      --       : ⊗₁-emb φ (α , ⊗₁-pre ψ β)
      --         Ct.⨾ ⊗₁-emb φ' (C.idn l' , ⊗₁-pre ψ' (C.idn r'))
      --       ≡ ⊗₁-emb (φ Ct.⨾ φ') (α , ⊗₁-pre (ψ Ct.⨾ ψ') β)
      --     suf =
      --         sym (⊗₁-bifunctor φ φ'
      --                α (C.idn l') (⊗₁-pre ψ β) (⊗₁-pre ψ' (C.idn r')))
      --       ∙ (λ i → ⊗₁-emb (φ Ct.⨾ φ')
      --                  (Ct.unitr α i , ⊗₁-pre-comp ψ ψ' β i))
```
