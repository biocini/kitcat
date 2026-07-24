Lane Biocini
July 2026

The morphism-level derived theory of the two-field monoidal record —
functoriality of the derived 2-cell tensor `_⊗₁_` in vertical
composition, the displaced unit and composite comparisons, the
displaced representability and witness calculi, and naturality of
the associator and unitors. The archived single-field form is
`Cat.Depreciated.Monoidal.Legacy.Bifunctor`; the split here follows the record:
every cell consuming an interchange lives in
`over-interchange-bifunctor`, developed once over an arbitrary
pointwise pair and instantiated at either field, and every cell
that never touches one ports unchanged.

The pull-side hom fiber needs no construction at all: its statement
is definitionally the `⊗₁-pull-contr` field. The push side extends
a characterization to a full displaced spine by the Kan lid over
the derived coherence square and projects contractibility from the
derived `⊗₁-spine-contr`. The image contraction lands through `ι⁺`
exactly as the object grade's does, with the propositional
invariance line beside it; the straightening computation
`unitl-ap` loses its final leaf to the two-field record, where
`⊗₀-coh→∙` holds by `refl`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Depreciated.Monoidal.Bifunctor where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using (ap-comp)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.J using (J; subst)
open import Core.Transport.Properties
  using (ap-fst-fiber; sq-from-∙; is-contr-is-prop)
open import Core.Equiv.Base using (iso→equiv; _≃_)
open import Core.Function.Embedding
  using (image-fibers-contr→is-embedding)

open import Cat.Depreciated.Type
open import Cat.Depreciated.Base
open import Cat.Depreciated.Monoidal

module bifunctor-theory {o h} {C : category o h} (M : monoidal C) where
  open monoidal M
  private module C = category C
  private module Ct = theory C
```

## The contractible hom-level fiber, pull side

A spine candidate `σ` with the pre-side characterization: the
fiber is the statement of the `⊗₁-pull-contr` field — the pull
centers project `x ⊗₀ y` and `⊗₀-emb-comp` definitionally, so no
reshaping intervenes.

```agda
  module ⊗₁-hfiber {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y') where

    p-char : C.hom (x ⊗₀ y) (x' ⊗₀ y') → Type (o ⊔ h)
    p-char σ =
      PathP (λ i → ⊗₁-composite (⊗₀-emb-comp x y i) (⊗₀-emb-comp x' y' i))
            (⊗₁-emb σ) (⊗₁-emb φ ▾₁ ψ)

    pull-contr : is-contr (Σ σ ∶ C.hom (x ⊗₀ y) (x' ⊗₀ y') , p-char σ)
    pull-contr = ⊗₁-pull-contr φ ψ
```

## Fibers

`⊗₁-cast-path` and its inverse move between the pre-side
characterization and a plain equation with the derived tensor,
exactly as `Cat.Depreciated.Base`'s `cast-path` pair.

```agda
  ⊗₁-cast-path
    : ∀ {x x'} {φ : C.hom x x'} {y y'} {ψ : C.hom y y'}
        {σ : C.hom (x ⊗₀ y) (x' ⊗₀ y')}
    → ⊗₁-hfiber.p-char φ ψ σ → φ ⊗₁ ψ ≡ σ
  ⊗₁-cast-path {φ = φ} {ψ = ψ} {σ} pc =
    ap fst (⊗₁-hfiber.pull-contr φ ψ .paths (σ , pc))

  -- a plain equation transports the center's characterization
  -- across it: cap the spine's PathP with the ap-rewrite
  ⊗₁-cast-path⁻¹
    : ∀ {x x'} {φ : C.hom x x'} {y y'} {ψ : C.hom y y'}
        {σ : C.hom (x ⊗₀ y) (x' ⊗₀ y')}
    → φ ⊗₁ ψ ≡ σ → ⊗₁-hfiber.p-char φ ψ σ
  ⊗₁-cast-path⁻¹ {φ = φ} {ψ = ψ} p = pcom (ap ⊗₁-emb p) (⊗₁-emb-comp φ ψ) refl
```

## The displaced unit chain, pull side

Each identity of `theory₀`'s interchange-free unit chain has a
morphism-level image displaced over the same base path, glued link
by link by `Core.Kan`'s `comp-pathp₂` at the family `C.hom`.

```agda
  ⊗₁-comp-eq-ev
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
    → PathP (λ i → C.hom (⊗₀-comp-eq-ev x y i) (⊗₀-comp-eq-ev x' y' i))
            (φ ⊗₁ ψ) (⊗₁-ev (⊗₁-emb φ ▾₁ ψ))
  ⊗₁-comp-eq-ev {x} {x'} φ {y} {y'} ψ =
    comp-pathp₂ C.hom
      (sym (⊗₀-unit (x ⊗₀ y))) (ap ⊗₀-ev (⊗₀-emb-comp x y))
      (sym (⊗₀-unit (x' ⊗₀ y'))) (ap ⊗₀-ev (⊗₀-emb-comp x' y'))
      (sym (⊗₁-unit (φ ⊗₁ ψ)))
      (apd (λ i → ⊗₁-ev) (⊗₁-emb-comp φ ψ))

  ⊗₁-comp-eq-pre
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
    → PathP (λ i → C.hom (⊗₀-comp-eq-pre x y i) (⊗₀-comp-eq-pre x' y' i))
            (φ ⊗₁ ψ) (⊗₁-pre φ ψ)
  ⊗₁-comp-eq-pre {x} {x'} φ {y} {y'} ψ =
    comp-pathp₂ C.hom
      (⊗₀-comp-eq-ev x y) (ap (⊗₀-pre x) (⊗₀-unit y))
      (⊗₀-comp-eq-ev x' y') (ap (⊗₀-pre x') (⊗₀-unit y'))
      (⊗₁-comp-eq-ev φ ψ)
      (apd (λ i χ → ⊗₁-emb φ $₁ (⊗₁-ov-idn , χ)) (⊗₁-unit ψ))

  ⊗₁-pre-distr
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        {r r'} (β : C.hom r r')
    → PathP (λ i → C.hom (⊗₀-pre-distr x y r i) (⊗₀-pre-distr x' y' r' i))
            (⊗₁-pre (φ ⊗₁ ψ) β) (⊗₁-pre φ (⊗₁-pre ψ β))
  ⊗₁-pre-distr φ ψ β = λ i → ⊗₁-emb-comp φ ψ i $₁ (⊗₁-ov-idn , β)
```

## Collapsing a vertical composite of pre-actions

```agda
  ⊗₁-pre-comp
    : ∀ {y y'} (ψ : C.hom y y') {y''} (ψ' : C.hom y' y'')
        {r r'} (β : C.hom r r')
    → (⊗₁-pre ψ β) Ct.⨾ (⊗₁-pre ψ' (C.idn r')) ≡ ⊗₁-pre (ψ Ct.⨾ ψ') β
  ⊗₁-pre-comp {y} {y'} ψ {y''} ψ' {r} {r'} β =
      sym (⊗₁-emb-⨾ ψ ψ' (⊗₁-ov-idn , β) (⊗₁-ov-idn , C.idn r'))
    ∙ (λ i → ⊗₁-emb (ψ Ct.⨾ ψ') $₁ (Ct.idem {I} i , Ct.unitr β i))
```

## Functoriality of the derived 2-cell tensor

Both sides inhabit the contractible `⊗₁-hfiber`: the left side is
its center, and the composite side satisfies the characterization
by three links — two `⊗₁-emb-⨾` rewrites at the endpoint fibers
sandwiching the side-by-side paste `W` of the two spine
characterizations, with `⊗₁-pre-comp` collapsing the doubled
pre-action. The glue is `Core.Kan`'s `pcom`. Nothing here touches
an interchange.

```agda
  ⊗₁-preserves-⨾
    : ∀ {x x'} (φ : C.hom x x') {x''} (φ' : C.hom x' x'')
        {y y'} (ψ : C.hom y y') {y''} (ψ' : C.hom y' y'')
    → (φ Ct.⨾ φ') ⊗₁ (ψ Ct.⨾ ψ') ≡ (φ ⊗₁ ψ) Ct.⨾ (φ' ⊗₁ ψ')
  ⊗₁-preserves-⨾ {x} {x'} φ {x''} φ' {y} {y'} ψ {y''} ψ' =
    ap fst
      (⊗₁-hfiber.pull-contr (φ Ct.⨾ φ') (ψ Ct.⨾ ψ') .paths
        ((φ ⊗₁ ψ) Ct.⨾ (φ' ⊗₁ ψ') , glued))
    where
      σ₁ = φ ⊗₁ ψ
      σ₂ = φ' ⊗₁ ψ'

      -- the side-by-side paste of the two characterizations; the
      -- middle operators ⊗₀-emb-comp x' y' i match, so this is a
      -- PathP over the composite line
      W : PathP (λ i → ⊗₁-composite (⊗₀-emb-comp x y i)
                                     (⊗₀-emb-comp x'' y'' i))
                (⊗₁-emb σ₁ ⨾₁ ⊗₁-emb σ₂)
                ((⊗₁-emb φ ▾₁ ψ) ⨾₁ (⊗₁-emb φ' ▾₁ ψ'))
      W i = ⊗₁-emb-comp φ ψ i ⨾₁ ⊗₁-emb-comp φ' ψ' i

      -- link A, in the fixed i0-fiber: the frame rewrite by
      -- unitr lands on δ ⊗₁-ctx-⨾ ⊗₁-ctx-idn, where ⊗₁-emb-⨾ splits
      linkA : PathP (λ i → ⊗₁-composite (⊗₀-emb (x ⊗₀ y)) (⊗₀-emb (x'' ⊗₀ y'')))
                    (⊗₁-emb (σ₁ Ct.⨾ σ₂)) (W i0)
      linkA i γ γ' (α , β) =
        ( (λ j → ⊗₁-emb (σ₁ Ct.⨾ σ₂) $₁ (sym (Ct.unitr α) j , sym (Ct.unitr β) j))
        ∙ ⊗₁-emb-⨾ σ₁ σ₂ (α , β) ⊗₁-ctx-idn ) i

      -- link B, in the fixed i1-fiber: W i1 computes to the two
      -- pre-actions, ⊗₁-emb-⨾ rejoins them, and the second slot is
      -- exactly ⊗₁-pre-comp
      linkB : PathP (λ i → ⊗₁-composite (⊗₀-emb x ▾₀ y) (⊗₀-emb x'' ▾₀ y''))
                    (W i1) (⊗₁-emb (φ Ct.⨾ φ') ▾₁ (ψ Ct.⨾ ψ'))
      linkB i γ γ' (α , β) =
        ( sym (⊗₁-emb-⨾ φ φ' (α , ⊗₁-pre ψ β) (C.idn _ , ⊗₁-pre ψ' (C.idn _)))
        ∙ (λ j → ⊗₁-emb (φ Ct.⨾ φ') $₁ (Ct.unitr α j , ⊗₁-pre-comp ψ ψ' β j)) ) i

      glued : ⊗₁-hfiber.p-char (φ Ct.⨾ φ') (ψ Ct.⨾ ψ') (σ₁ Ct.⨾ σ₂)
      glued = pcom {A = λ i → ⊗₁-composite (⊗₀-emb-comp x y i)
                                            (⊗₀-emb-comp x'' y'' i)}
                   (sym linkA) W linkB
```

## Cells over an interchange pair

Developed once, over an arbitrary pointwise interchange with its
displaced mate, and instantiated at either field — the statements
below depend on the supplied pair exactly as their level-0 mirrors
depend on theirs.

```agda
  module over-interchange-bifunctor
    (ι₀ : (x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y)
    (ι₁ : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        → PathP (λ i → ⊗₁-composite (ι₀ x y i) (ι₀ x' y' i))
                (⊗₁-emb φ ▾₁ ψ) (φ ▴₁ ⊗₁-emb ψ))
    where

    open over-interchange ι₀
    open over-interchange₁ ι₀ ι₁
    open unitors ι₀
```

### The push-side hom fiber

With the post-side characterization as base, the missing lid over
the derived coherence square is the pre-side one, and the `q-char`
fiber is contractible by projection from the derived
`⊗₁-spine-contr`.

```agda
    module ⊗₁-hfiber-op {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y') where

      q-char : C.hom (x ⊗₀ y) (x' ⊗₀ y') → Type (o ⊔ h)
      q-char σ =
        PathP (λ i → ⊗₁-composite (⊗₀-emb-comp-op x y i)
                                   (⊗₀-emb-comp-op x' y' i))
              (⊗₁-emb σ) (φ ▴₁ ⊗₁-emb ψ)

      private
        rlid : ∀ {σ} (qc : q-char σ)
            → (i j : Core.Base.I)
            → ⊗₁-composite (⊗₀-emb-comp-coh x y (~ i) j)
                            (⊗₀-emb-comp-coh x' y' (~ i) j)
        rlid {σ} qc i j =
          fil (λ k → ⊗₁-composite (⊗₀-emb-comp-coh x y (~ k) j)
                                   (⊗₀-emb-comp-coh x' y' (~ k) j))
              (∂ j) i λ where
            k (j = i0) → ⊗₁-emb σ
            k (j = i1) → ι₁ φ ψ (~ k)
            k (k = i0) → qc j

      extend-p : ∀ {σ} → q-char σ → ⊗₁-hfiber.p-char φ ψ σ
      extend-p qc j = rlid qc i1 j

      extend-θ⁻
        : ∀ {σ} (qc : q-char σ)
        → PathP
            (λ i → PathP
              (λ j → ⊗₁-composite (⊗₀-emb-comp-coh x y i j)
                                   (⊗₀-emb-comp-coh x' y' i j))
              (⊗₁-emb σ)
              (ι₁ φ ψ i))
            (extend-p qc) qc
      extend-θ⁻ qc i j = rlid qc (~ i) j

      push-contr : is-contr (Σ σ ∶ C.hom (x ⊗₀ y) (x' ⊗₀ y') , q-char σ)
      push-contr .center = (φ ⊗₁ ψ) , ⊗₁-emb-comp-op φ ψ
      push-contr .paths (σ , qc) i = Φ i .fst , Φ i .snd .snd .fst
        where
          Φ : ⊗₁-spine-contr φ ψ .center ≡ (σ , extend-p qc , qc , extend-θ⁻ qc)
          Φ = ⊗₁-spine-contr φ ψ .paths (σ , extend-p qc , qc , extend-θ⁻ qc)

    ⊗₁-push-contr
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
      → is-contr (Σ σ ∶ C.hom (x ⊗₀ y) (x' ⊗₀ y') , ⊗₁-hfiber-op.q-char φ ψ σ)
    ⊗₁-push-contr φ ψ = ⊗₁-hfiber-op.push-contr φ ψ
```

### The displaced unit chain, post side

```agda
    ⊗₁-comp-eq-post
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
      → PathP (λ i → C.hom (⊗₀-comp-eq-post x y i) (⊗₀-comp-eq-post x' y' i))
              (φ ⊗₁ ψ) (⊗₁-post ψ φ)
    ⊗₁-comp-eq-post {x} {x'} φ {y} {y'} ψ =
      comp-pathp₂ C.hom
        (sym (⊗₀-unit (x ⊗₀ y)))
        (ap ⊗₀-ev (⊗₀-emb-comp-op x y) ∙ ap (⊗₀-post y) (⊗₀-unit x))
        (sym (⊗₀-unit (x' ⊗₀ y')))
        (ap ⊗₀-ev (⊗₀-emb-comp-op x' y') ∙ ap (⊗₀-post y') (⊗₀-unit x'))
        (sym (⊗₁-unit (φ ⊗₁ ψ)))
        (comp-pathp₂ C.hom
          (ap ⊗₀-ev (⊗₀-emb-comp-op x y)) (ap (⊗₀-post y) (⊗₀-unit x))
          (ap ⊗₀-ev (⊗₀-emb-comp-op x' y')) (ap (⊗₀-post y') (⊗₀-unit x'))
          (apd (λ i → ⊗₁-ev) (⊗₁-emb-comp-op φ ψ))
          (apd (λ i χ → ⊗₁-emb ψ $₁ (χ , ⊗₁-un-idn)) (⊗₁-unit φ)))

    ⊗₁-pre-is-post
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
      → PathP (λ i → C.hom (⊗₀-pre-is-post x y i) (⊗₀-pre-is-post x' y' i))
              (⊗₁-pre φ ψ) (⊗₁-post ψ φ)
    ⊗₁-pre-is-post {x} {x'} φ {y} {y'} ψ =
      comp-pathp₂ C.hom
        (sym (⊗₀-comp-eq-pre x y)) (⊗₀-comp-eq-post x y)
        (sym (⊗₀-comp-eq-pre x' y')) (⊗₀-comp-eq-post x' y')
        (sym (⊗₁-comp-eq-pre φ ψ))
        (⊗₁-comp-eq-post φ ψ)

    ⊗₁-absorb-l
      : ∀ {r r'} (β : C.hom r r')
      → PathP (λ i → C.hom (⊗₀-absorb-l r i) (⊗₀-absorb-l r' i))
              (⊗₁-pre (C.idn I) β) β
    ⊗₁-absorb-l {r} {r'} β =
      comp-pathp₂ C.hom
        (⊗₀-pre-is-post I r) (⊗₀-unit r)
        (⊗₀-pre-is-post I r') (⊗₀-unit r')
        (⊗₁-pre-is-post (C.idn I) β)
        (⊗₁-unit β)

    ⊗₁-absorb-r
      : ∀ {l l'} (α : C.hom l l')
      → PathP (λ i → C.hom (⊗₀-absorb-r l i) (⊗₀-absorb-r l' i))
              (⊗₁-post (C.idn I) α) α
    ⊗₁-absorb-r {l} {l'} α =
      comp-pathp₂ C.hom
        (sym (⊗₀-pre-is-post l I)) (⊗₀-unit l)
        (sym (⊗₀-pre-is-post l' I)) (⊗₀-unit l')
        (sym (⊗₁-pre-is-post α (C.idn I)))
        (⊗₁-unit α)
```

### Displaced funext and pointwise projections

```agda
    ⊗₁-idn-▴
      : ∀ {F F'} (η : ⊗₁-composite F F')
      → PathP (λ i → ⊗₁-composite (⊗₀-idn-▴ F i) (⊗₀-idn-▴ F' i))
              (C.idn I ▴₁ η) η
    ⊗₁-idn-▴ η i γ γ' (α , β) = η $₁ (⊗₁-absorb-r α i , β)

    ▾₁-idn
      : ∀ {F F'} (η : ⊗₁-composite F F')
      → PathP (λ i → ⊗₁-composite (▾₀-idn F i) (▾₀-idn F' i))
              (η ▾₁ C.idn I) η
    ▾₁-idn η i γ γ' (α , β) = η $₁ (α , ⊗₁-absorb-l β i)

    -- the displaced image of ⊗₀-emb-idn-absorb: the interchange at
    -- the identity glued to the displaced funext absorption
    ⊗₁-emb-idn-absorb
      : ∀ {x x'} (φ : C.hom x x')
      → PathP (λ i → ⊗₁-composite (⊗₀-emb-idn-absorb x i)
                                   (⊗₀-emb-idn-absorb x' i))
              (⊗₁-emb (C.idn I) ▾₁ φ) (⊗₁-emb φ)
    ⊗₁-emb-idn-absorb {x} {x'} φ =
      comp-pathp₂ ⊗₁-composite
        (ι₀ I x) (⊗₀-idn-▴ (⊗₀-emb x))
        (ι₀ I x') (⊗₀-idn-▴ (⊗₀-emb x'))
        (ι₁ (C.idn I) φ)
        (⊗₁-idn-▴ (⊗₁-emb φ))

    ⊗₁-post-distr
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
          {l l'} (α : C.hom l l')
      → PathP (λ i → C.hom (⊗₀-post-distr x y l i) (⊗₀-post-distr x' y' l' i))
              (⊗₁-post (φ ⊗₁ ψ) α) (⊗₁-post ψ (⊗₁-post φ α))
    ⊗₁-post-distr φ ψ α = λ i → ⊗₁-emb-comp-op φ ψ i $₁ (α , ⊗₁-un-idn)
```

### The post-side pairing

```agda
    _○₁_
      : ∀ {F F' G G' : ⊗₀-composite}
          {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
          {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
          {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
      → ⊗₁-wit U U' η → ⊗₁-wit V V' ζ
      → ⊗₁-wit (U ○₀ V) (U' ○₀ V') (η ▵₁ ζ)
    _○₁_ {U = m , p} {m' , p'} {n , q} {n' , q'} (σ , P) (τ , Q) =
      σ ⊗₁ τ ,
      comp-pathp₂ ⊗₁-composite
        (⊗₀-emb-comp-op m n) (λ i → p i ▵₀ q i)
        (⊗₀-emb-comp-op m' n') (λ i → p' i ▵₀ q' i)
        (⊗₁-emb-comp-op σ τ) (λ i → P i ▵₁ Q i)
```

### The image contraction

The `q-char` fiber at the identity slot is straightened to the
plain image fiber along `⊗₁-idn-▴`, one `subst` in a line of
Σ-of-PathP types. The straightening square is the computation of
`ap ⊗₀-emb (⊗₀-unitl x)` out of the level-0 calculus: the
representability computation (`ap-fst-fiber` at the canonical κ)
and the `∙ refl` redexes discharged by `unitr` — the spine's
2-cell `⊗₀-coh→∙` holds by `refl` here, so the chain closes on
the definitional composite.

```agda
    private
      unitl-ap
        : ∀ (x : C.ob)
        → ap ⊗₀-emb (⊗₀-unitl x) ≡ ⊗₀-emb-comp-op I x ∙ ⊗₀-idn-▴ (⊗₀-emb x)
      unitl-ap x =
          ap-fst-fiber κ₀
        ∙ Path.unitr (U .snd)
        ∙ ap (_∙ ⊗₀-emb-idn-absorb x) (Path.unitr (⊗₀-emb-comp I x))
        ∙ Path.assoc (⊗₀-emb-comp I x) (ι₀ I x) (⊗₀-idn-▴ (⊗₀-emb x))
        where
          U V : is-⊗₀-representable (⊗₀-emb x)
          U = (⊗₀-nrm I ●₀ ⊗₀-nrm x) ↝ ⊗₀-emb-idn-absorb x
          V = ⊗₀-nrm x

          κ₀ : U ≡ V
          κ₀ = unitl-σ●₀ x

      -- the straightening square: top ap ⊗₀-emb (⊗₀-unitl x),
      -- left ⊗₀-emb-comp-op I x, bottom ⊗₀-idn-▴, right constant
      unitl-sq : ∀ (x : C.ob) → (j i : Core.Base.I) → ⊗₀-composite
      unitl-sq x j i = sq-from-∙ (unitl-ap x) i j

      -- the line of displaced fibers along ⊗₀-unitl
      unitl-line : ∀ {x x'} (φ : C.hom x x') → Core.Base.I → Type (o ⊔ h)
      unitl-line {x} {x'} φ j =
        Σ χ ∶ C.hom (⊗₀-unitl x j) (⊗₀-unitl x' j) ,
        PathP (λ i → ⊗₁-composite (unitl-sq x j i) (unitl-sq x' j i))
              (⊗₁-emb χ) (⊗₁-idn-▴ (⊗₁-emb φ) j)

    ⊗₁-emb-image-contr
      : ∀ {x x'} (φ : C.hom x x')
      → is-contr (is-⊗₁-representable (⊗₁-emb φ))
    ⊗₁-emb-image-contr {x} {x'} φ =
      subst is-contr (λ j → unitl-line φ j) (⊗₁-push-contr (C.idn I) φ)
```

## The representability calculus

The embedding property is landed through `ι⁺`, and
`is-contr-is-prop` certifies the contraction is the same through
`ι⁻`: everything below is insensitive to the choice. With the
frame endpoints fixed, `⊗₁-emb` is an ordinary map between fixed
types, and its plain fibers support the `Cat.Depreciated.Base` calculus by
transcription.

```agda
  ⊗₁-emb-image-contr
    : ∀ {x x'} (φ : C.hom x x')
    → is-contr (is-⊗₁-representable (⊗₁-emb φ))
  ⊗₁-emb-image-contr = over-interchange-bifunctor.⊗₁-emb-image-contr ι⁺-pt ι⁺₁-pt

  image-contr₁-invariant
    : ∀ {x x'} (φ : C.hom x x')
    → over-interchange-bifunctor.⊗₁-emb-image-contr ι⁺-pt ι⁺₁-pt φ
    ≡ over-interchange-bifunctor.⊗₁-emb-image-contr ι⁻-pt ι⁻₁-pt φ
  image-contr₁-invariant φ = is-contr-is-prop _ _ _

  is-⊗₁-representable-prop
    : ∀ {x x'} (η : ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x'))
    → is-prop (is-⊗₁-representable η)
  is-⊗₁-representable-prop = image-fibers-contr→is-embedding (λ φ → ⊗₁-emb-image-contr φ)

  ⊗₁-rep-contr
    : ∀ {x x'} {η : ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x')}
    → is-⊗₁-representable η → is-contr (is-⊗₁-representable η)
  ⊗₁-rep-contr {η = η} u .center = u
  ⊗₁-rep-contr {η = η} u .paths  = is-⊗₁-representable-prop η u

  ⊗₁-repr-unique
    : ∀ {x x'} {η : ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x')}
    → (u v : is-⊗₁-representable η) → u .fst ≡ v .fst
  ⊗₁-repr-unique {η = η} u v = ap fst (is-⊗₁-representable-prop η u v)

  ⊗₁-repr-lc
    : ∀ {x x'} {η : ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x')}
        {U V : is-⊗₁-representable η}
    → (κ : U ≡ V) → ap fst κ ≡ ⊗₁-repr-unique U V
  ⊗₁-repr-lc {η = η} {U} {V} κ =
    ap (ap fst) (is-contr→is-set (⊗₁-rep-contr U) U V κ
      (is-⊗₁-representable-prop η U V))

  ⊗₁-repr-refl
    : ∀ {x x'} {η : ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x')} {m : C.hom x x'}
      (p q : ⊗₁-emb m ≡ η)
    → p ≡ q → ⊗₁-repr-unique (m , p) (m , q) ≡ refl
  ⊗₁-repr-refl {η = η} {m} p q =
    J (λ q' _ → ⊗₁-repr-unique (m , p) (m , q') ≡ refl)
      (sym (⊗₁-repr-lc (refl {x = m , p})))

  ⊗₁-repr-cast
    : ∀ {x x'} {η : ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x')}
        {m : C.hom x x'} {p q : ⊗₁-emb m ≡ η}
    → (V : is-⊗₁-representable η) → p ≡ q
    → ⊗₁-repr-unique (m , p) V ≡ ⊗₁-repr-unique (m , q) V
  ⊗₁-repr-cast {m = m} V e i = ⊗₁-repr-unique (m , e i) V

  ⊗₁-repr-ap
    : ∀ {x x' y y'} {η : ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x')}
        {ζ : ⊗₁-composite (⊗₀-emb y) (⊗₀-emb y')}
      (Ĝ : is-⊗₁-representable η → is-⊗₁-representable ζ)
      (U V : is-⊗₁-representable η)
    → ⊗₁-repr-unique (Ĝ U) (Ĝ V)
    ≡ ap (λ u → Ĝ u .fst) (is-⊗₁-representable-prop η U V)
  ⊗₁-repr-ap Ĝ U V = sym (⊗₁-repr-lc (λ i → Ĝ (is-⊗₁-representable-prop _ U V i)))

  ⊗₁-repr-∙
    : ∀ {x x'} {η : ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x')}
    → (U V W : is-⊗₁-representable η)
    → ⊗₁-repr-unique U V ∙ ⊗₁-repr-unique V W ≡ ⊗₁-repr-unique U W
  ⊗₁-repr-∙ {η = η} U V W =
      sym (ap-comp fst (is-⊗₁-representable-prop η U V)
            (is-⊗₁-representable-prop η V W))
    ∙ ⊗₁-repr-lc
        (is-⊗₁-representable-prop η U V ∙ is-⊗₁-representable-prop η V W)

  _↝₁_
    : ∀ {x x'} {η ζ : ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x')}
    → is-⊗₁-representable η → η ≡ ζ → is-⊗₁-representable ζ
  (m , p) ↝₁ e = m , p ∙ e

  -- ↝₁ preserves fst definitionally, so the slid line's shadow is
  -- the shadow of the slid propositionality path — no transport
  ↝₁-repr
    : ∀ {x x'} {η ζ : ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x')}
      (U V : is-⊗₁-representable η) (e : η ≡ ζ)
    → ⊗₁-repr-unique (U ↝₁ e) (V ↝₁ e) ≡ ⊗₁-repr-unique U V
  ↝₁-repr {η = η} U V e = sym (⊗₁-repr-lc (λ i → is-⊗₁-representable-prop η U V i ↝₁ e))

  ap-⊗₁-emb-lc
    : ∀ {x x'} {m n : C.hom x x'} {r s : m ≡ n}
    → ap ⊗₁-emb r ≡ ap ⊗₁-emb s → r ≡ s
  ap-⊗₁-emb-lc {n = n} {r} {s} h =
    total-contr-unique (⊗₁-emb-image-contr n) r s (sq r)
      (subst (λ t → PathP (λ i → ⊗₁-emb (s i) ≡ ⊗₁-emb n) t refl)
        (sym h) (sq s))
    where
      sq : (t : _ ≡ n)
        → PathP (λ i → ⊗₁-emb (t i) ≡ ⊗₁-emb n) (ap ⊗₁-emb t) refl
      sq t i j = ⊗₁-emb (t (i ∨ j))

  ⊗₁-hom≃total-representable
    : ∀ {x x'}
    → C.hom x x'
    ≃ (Σ η ∶ ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x') , is-⊗₁-representable η)
  ⊗₁-hom≃total-representable {x} {x'} = iso→equiv fwd bwd hom-ret rep-sec
    where
      fwd : C.hom x x'
          → Σ η ∶ ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x') , is-⊗₁-representable η
      fwd f = ⊗₁-emb f , f , refl

      bwd : (Σ η ∶ ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x') , is-⊗₁-representable η)
          → C.hom x x'
      bwd (_ , a , _) = a

      hom-ret : ∀ f → bwd (fwd f) ≡ f
      hom-ret f = refl

      -- boundaries, both definitional: at i0 the triple is
      -- (p i0 , a , λ j → p (0 ∧ j)) = (⊗₁-emb a , a , refl)
      -- = fwd a, since p i0 computes to the path's endpoint and
      -- 0 ∧ j = 0; at i1 it is (p i1 , a , λ j → p j) = s by
      -- path- and Σ-eta
      rep-sec : ∀ s → fwd (bwd s) ≡ s
      rep-sec (_ , a , p) i = p i , a , λ j → p (i ∧ j)
```

## The displaced witness calculus

Contractibility of the displaced witness space needs no nest
chains: sliding an inhabitant's characterization along its own
base line connects the space to the plain image fiber.

```agda
  ⊗₁-wit-contr
    : ∀ {F F' : ⊗₀-composite}
        {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
        {η : ⊗₁-composite F F'}
    → ⊗₁-wit U U' η → is-contr (⊗₁-wit U U' η)
  ⊗₁-wit-contr {U = U} {U'} (τ , t) =
    subst is-contr
      (λ j → Σ σ ∶ C.hom (U .fst) (U' .fst) ,
             PathP (λ i → ⊗₁-composite (U .snd (j ∧ i)) (U' .snd (j ∧ i)))
                   (⊗₁-emb σ) (t j))
      (⊗₁-emb-image-contr τ)
```

`_●₁_` and `_↝̂_` mirror `_●₀_` and `_↝_` token-for-token, with
`comp-pathp₂` in the role of `∙`.

```agda
  _●₁_
    : ∀ {F F' G G' : ⊗₀-composite}
        {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
        {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
        {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
    → ⊗₁-wit U U' η → ⊗₁-wit V V' ζ
    → ⊗₁-wit (U ●₀ V) (U' ●₀ V') (η ▿₁ ζ)
  _●₁_ {U = m , p} {m' , p'} {n , q} {n' , q'} (σ , P) (τ , Q) =
    σ ⊗₁ τ ,
    comp-pathp₂ ⊗₁-composite
      (⊗₀-emb-comp m n) (λ i → p i ▿₀ q i)
      (⊗₀-emb-comp m' n') (λ i → p' i ▿₀ q' i)
      (⊗₁-emb-comp σ τ) (λ i → P i ▿₁ Q i)
  infixr 40 _●₁_

  _↝̂_
    : ∀ {F F' G G' : ⊗₀-composite}
        {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
        {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
        {e : F ≡ G} {e' : F' ≡ G'}
    → ⊗₁-wit U U' η
    → PathP (λ i → ⊗₁-composite (e i) (e' i)) η ζ
    → ⊗₁-wit (U ↝ e) (U' ↝ e') ζ
  _↝̂_ {U = m , p} {U' = m' , p'} {e = e} {e' = e'} (σ , P) ê =
    σ , comp-pathp₂ ⊗₁-composite p e p' e' P ê

  -- the displaced ↝-fill: the same slide one level up, with
  -- comp-pathp₂-fill in the role of cat.fill — the hom is constant,
  -- at m = i0 the slide is Û (the fil cap), at m = i1 the transport
  -- Û ↝̂ ê (the com), both definitional
  ↝̂-fill
    : ∀ {F F' G G' : ⊗₀-composite}
        {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
        {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
        {e : F ≡ G} {e' : F' ≡ G'}
      (Û : ⊗₁-wit U U' η)
      (ê : PathP (λ i → ⊗₁-composite (e i) (e' i)) η ζ)
      (m : Core.Base.I)
    → ⊗₁-wit (↝-fill U e m) (↝-fill U' e' m) (ê m)
  ↝̂-fill {U = m₀ , p} {U' = m₀' , p'} {e = e} {e' = e'} (σ , P) ê m =
    σ , comp-pathp₂-fill ⊗₁-composite p e p' e' P ê m
```

`⊗₁-wit-σ[_,_]` is the displaced line over an arbitrary pair of
level-0 identifications: the level-0 fibers are propositional, so
every pair of σs lifts. It is opaque for the same reason as
`assoc-σ●₀`: a consumer's family projects its components at
generic interval points, and the sealed head keeps that comparison
syntactic.

```agda
  opaque
    ⊗₁-wit-σ[_,_]
      : ∀ {F F' : ⊗₀-composite}
          {u₀ u₁ : is-⊗₀-representable F}
          {u₀' u₁' : is-⊗₀-representable F'}
          (σ : u₀ ≡ u₁) (σ' : u₀' ≡ u₁')
          {η : ⊗₁-composite F F'}
        (Û : ⊗₁-wit u₀ u₀' η) (V̂ : ⊗₁-wit u₁ u₁' η)
      → PathP (λ i → ⊗₁-wit (σ i) (σ' i) η) Û V̂
    ⊗₁-wit-σ[_,_] σ σ' {η} Û V̂ =
      is-prop→PathP
        (λ i → is-contr→is-prop
          (subst is-contr
            (λ k → ⊗₁-wit (σ (i ∧ k)) (σ' (i ∧ k)) η)
            (⊗₁-wit-contr Û)))
        Û V̂

  ⊗₁-wit-σ
    : ∀ {F F' : ⊗₀-composite}
        {U V : is-⊗₀-representable F} {U' V' : is-⊗₀-representable F'}
        {η : ⊗₁-composite F F'}
      (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' η)
    → PathP (λ i → ⊗₁-wit (is-⊗₀-representable-prop F U V i)
                          (is-⊗₀-representable-prop F' U' V' i) η)
            Û V̂
  ⊗₁-wit-σ {F} {F'} {U} {V} {U'} {V'} =
    ⊗₁-wit-σ[ is-⊗₀-representable-prop F U V
            , is-⊗₀-representable-prop F' U' V' ]

  ⊗₁-wit-unique
    : ∀ {F F' : ⊗₀-composite}
        {U V : is-⊗₀-representable F} {U' V' : is-⊗₀-representable F'}
        {η : ⊗₁-composite F F'}
      (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' η)
    → PathP (λ i → C.hom (⊗₀-repr-unique U V i) (⊗₀-repr-unique U' V' i))
            (Û .fst) (V̂ .fst)
  ⊗₁-wit-unique Û V̂ i = ⊗₁-wit-σ Û V̂ i .fst

  assoc-σ●₁
    : ∀ {F F' G G' H H' : ⊗₀-composite}
        {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
        {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
        {W : is-⊗₀-representable H} {W' : is-⊗₀-representable H'}
        {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
        {θ : ⊗₁-composite H H'}
      (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ) (Ŵ : ⊗₁-wit W W' θ)
    → PathP (λ i → ⊗₁-wit (assoc-σ●₀ U V W i) (assoc-σ●₀ U' V' W' i)
                          (η ▿₁ ζ ▿₁ θ))
            (Û ●₁ (V̂ ●₁ Ŵ)) ((Û ●₁ V̂) ●₁ Ŵ)
  assoc-σ●₁ {U = U} {U'} {V} {V'} {W} {W'} Û V̂ Ŵ =
    ⊗₁-wit-σ[ assoc-σ●₀ U V W , assoc-σ●₀ U' V' W' ]
      (Û ●₁ (V̂ ●₁ Ŵ)) ((Û ●₁ V̂) ●₁ Ŵ)

  assoc●₁
    : ∀ {F F' G G' H H' : ⊗₀-composite}
        {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
        {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
        {W : is-⊗₀-representable H} {W' : is-⊗₀-representable H'}
        {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
        {θ : ⊗₁-composite H H'}
      (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ) (Ŵ : ⊗₁-wit W W' θ)
    → PathP (λ i → C.hom (assoc●₀ U V W i) (assoc●₀ U' V' W' i))
            (Û .fst ⊗₁ (V̂ .fst ⊗₁ Ŵ .fst))
            ((Û .fst ⊗₁ V̂ .fst) ⊗₁ Ŵ .fst)
  assoc●₁ Û V̂ Ŵ i = assoc-σ●₁ Û V̂ Ŵ i .fst
```

`⊗₁-wit-∙` glues witness lines over composite fiber paths, with
`comp-pathp₂-over` supplying the characterization over the
hom-level `comp-pathp₂`: the hom component of the glue is the
`comp-pathp₂` of the hom components by construction — `hcom` at a
Σ-type does not project componentwise, so the pair is assembled,
never projected.

```agda
  ⊗₁-wit-∙
    : ∀ {T T' : ⊗₀-composite} {η : ⊗₁-composite T T'}
        {u₀ u₁ u₂ : is-⊗₀-representable T}
        {u₀' u₁' u₂' : is-⊗₀-representable T'}
      (σa : u₀ ≡ u₁) (σb : u₁ ≡ u₂)
      (σa' : u₀' ≡ u₁') (σb' : u₁' ≡ u₂')
      {ĥ₀ : ⊗₁-wit u₀ u₀' η} {ĥ₁ : ⊗₁-wit u₁ u₁' η} {ĥ₂ : ⊗₁-wit u₂ u₂' η}
    → PathP (λ i → ⊗₁-wit (σa i) (σa' i) η) ĥ₀ ĥ₁
    → PathP (λ i → ⊗₁-wit (σb i) (σb' i) η) ĥ₁ ĥ₂
    → PathP (λ i → ⊗₁-wit ((σa ∙ σb) i) ((σa' ∙ σb') i) η) ĥ₀ ĥ₂
  ⊗₁-wit-∙ {η = η} σa σb σa' σb' P̂ Q̂ i =
      comp-pathp₂ (λ u u' → C.hom (u .fst) (u' .fst)) σa σb σa' σb'
        (λ j → P̂ j .fst) (λ j → Q̂ j .fst) i
    , comp-pathp₂-over (λ u u' → C.hom (u .fst) (u' .fst))
        (λ u u' σ → PathP (λ k → ⊗₁-composite (u .snd k) (u' .snd k))
                          (⊗₁-emb σ) η)
        σa σb σa' σb'
        (λ j → P̂ j .fst) (λ j → Q̂ j .fst)
        (λ j → P̂ j .snd) (λ j → Q̂ j .snd) i
```

## Naturality of the associator

```agda
  ⊗₁-assoc
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        {z z'} (χ : C.hom z z')
    → PathP (λ i → C.hom (⊗₀-assoc x y z i) (⊗₀-assoc x' y' z' i))
            (φ ⊗₁ (ψ ⊗₁ χ)) ((φ ⊗₁ ψ) ⊗₁ χ)
  ⊗₁-assoc φ ψ χ = assoc●₁ (⊗₁-wit-nrm φ) (⊗₁-wit-nrm ψ) (⊗₁-wit-nrm χ)
```

## The unitors, displaced

The unitors are the `fst`-shadows of `⊗₁-wit-σ[_,_]` at the sealed
level-0 unitor σ-lines, threading the `↝̂`-transports of the normal
pairings along the displaced funext absorptions — relative to the
supplied interchange pair exactly as their level-0 mates are.
Naturality is the type: one `PathP` between the derived tensors
over the level-0 identity.

```agda
  module unitors₁
    (ι₀ : (x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y)
    (ι₁ : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        → PathP (λ i → ⊗₁-composite (ι₀ x y i) (ι₀ x' y' i))
                (⊗₁-emb φ ▾₁ ψ) (φ ▴₁ ⊗₁-emb ψ))
    where

    open over-interchange ι₀ using (▾₀-idn; ⊗₀-emb-idn-absorb)
    open over-interchange-bifunctor ι₀ ι₁ using (▾₁-idn; ⊗₁-emb-idn-absorb)
    open unitors ι₀

    unitr-σ●₁
      : ∀ {x x'} (φ : C.hom x x')
      → PathP (λ i → ⊗₁-wit (unitr-σ●₀ x i) (unitr-σ●₀ x' i) (⊗₁-emb φ))
              ((⊗₁-wit-nrm φ ●₁ ⊗₁-wit-nrm (C.idn I)) ↝̂ ▾₁-idn (⊗₁-emb φ))
              (⊗₁-wit-nrm φ)
    unitr-σ●₁ {x} {x'} φ =
      ⊗₁-wit-σ[ unitr-σ●₀ x , unitr-σ●₀ x' ]
        ((⊗₁-wit-nrm φ ●₁ ⊗₁-wit-nrm (C.idn I)) ↝̂ ▾₁-idn (⊗₁-emb φ))
        (⊗₁-wit-nrm φ)

    unitl-σ●₁
      : ∀ {x x'} (φ : C.hom x x')
      → PathP (λ i → ⊗₁-wit (unitl-σ●₀ x i) (unitl-σ●₀ x' i) (⊗₁-emb φ))
              ((⊗₁-wit-nrm (C.idn I) ●₁ ⊗₁-wit-nrm φ) ↝̂ ⊗₁-emb-idn-absorb φ)
              (⊗₁-wit-nrm φ)
    unitl-σ●₁ {x} {x'} φ =
      ⊗₁-wit-σ[ unitl-σ●₀ x , unitl-σ●₀ x' ]
        ((⊗₁-wit-nrm (C.idn I) ●₁ ⊗₁-wit-nrm φ) ↝̂ ⊗₁-emb-idn-absorb φ)
        (⊗₁-wit-nrm φ)

    ⊗₁-unitr
      : ∀ {x x'} (φ : C.hom x x')
      → PathP (λ i → C.hom (⊗₀-unitr x i) (⊗₀-unitr x' i))
              (φ ⊗₁ C.idn I) φ
    ⊗₁-unitr φ i = unitr-σ●₁ φ i .fst

    ⊗₁-unitl
      : ∀ {x x'} (φ : C.hom x x')
      → PathP (λ i → C.hom (⊗₀-unitl x i) (⊗₀-unitl x' i))
              (C.idn I ⊗₁ φ) φ
    ⊗₁-unitl φ i = unitl-σ●₁ φ i .fst
```
