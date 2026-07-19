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
open import Core.Groupoid using (sym-distr)
open import Core.Transport.Base
  using (module Path-over; transport; transport⁻)

open import Cat.Type
import Cat.Base
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
```

The extension itself: over the object spine's square
`⊗₀-emb-comp-coh`, the pre-side characterization (bottom face),
the constant `⊗₁-emb σ` (left face), and `⊗₁-interchange` (right
face) are three sides of an open box whose missing top face is the
post-side characterization. `fil` fills the box; `extend-q` reads
off the lid and `extend-θ` is the filler square.

```agda
    private
      lid : ∀ {σ} (pc : p-char σ)
          → ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
          → (i j : _)
          → C.hom (⊗₀-emb-comp-coh x y i j (l , r))
                  (⊗₀-emb-comp-coh x' y' i j (l' , r'))
      lid {σ} pc {l} {l'} α {r} {r'} β i j =
        fil (λ k → C.hom (⊗₀-emb-comp-coh x y k j (l , r))
                         (⊗₀-emb-comp-coh x' y' k j (l' , r')))
            (∂ j) i λ where
          k (j = i0) → ⊗₁-emb σ (α , β)
          k (j = i1) → ⊗₁-interchange φ ψ α β k
          k (k = i0) → pc α β j

    extend-q : ∀ {σ} → p-char σ → q-char σ
    extend-q pc α β j = lid pc α β i1 j

    extend-θ
      : ∀ {σ} (pc : p-char σ)
      → ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
      → PathP
          (λ i → PathP
            (λ j → C.hom (⊗₀-emb-comp-coh x y i j (l , r))
                          (⊗₀-emb-comp-coh x' y' i j (l' , r')))
            (⊗₁-emb σ (α , β))
            (⊗₁-interchange φ ψ α β i))
          (pc α β) (extend-q pc α β)
    extend-θ pc α β i j = lid pc α β i j

    hfiber-contr : is-contr (Σ σ ∶ C.hom (x ⊗ y) (x' ⊗ y') , p-char σ)
    hfiber-contr .center =
      (φ ⊗₁ ψ) , ⊗₁-emb-comp φ ψ
    hfiber-contr .paths (σ , pc) i =
      Φ i .fst , Φ i .snd .fst
      where
        Φ : ⊗₁-spine-contr φ ψ .center ≡ (σ , pc , extend-q pc , extend-θ pc)
        Φ = ⊗₁-spine-contr φ ψ .paths (σ , pc , extend-q pc , extend-θ pc)
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
  ⊗₁-preserves-⨾ {x} {x'} φ {x''} φ' {y} {y'} ψ {y''} ψ' =
    ap fst
      (is-contr→is-prop
        (hfiber.hfiber-contr (φ Ct.⨾ φ') (ψ Ct.⨾ ψ'))
        (hfiber.hfiber-contr (φ Ct.⨾ φ') (ψ Ct.⨾ ψ') .center)
        ((φ ⊗₁ ψ) Ct.⨾ (φ' ⊗₁ ψ') , rhs-charac))
    where
      rhs-charac
        : hfiber.p-char (φ Ct.⨾ φ') (ψ Ct.⨾ ψ')
            ((φ ⊗₁ ψ) Ct.⨾ (φ' ⊗₁ ψ'))
      rhs-charac {l} {l'} α {r} {r'} β =
        Path-over.to-pathp
          ( ap (transport disp₂) link-pre
          ∙ Path-over.from-pathp mid
          ∙ suf )
        where
          disp₂
            : C.hom (⊗₀-emb (x ⊗ y) (l , r))
                    (⊗₀-emb (x'' ⊗ y'') (l' , r'))
            ≡ C.hom (⊗₀-emb x (l , ⊗₀-pre y r))
                    (⊗₀-emb x'' (l' , ⊗₀-pre y'' r'))
          disp₂ i =
            C.hom (happly (⊗₀-emb-comp x y) (l , r) i)
                  (happly (⊗₀-emb-comp x'' y'') (l' , r') i)

          link-pre
            : ⊗₁-emb ((φ ⊗₁ ψ) Ct.⨾ (φ' ⊗₁ ψ')) (α , β)
            ≡ ⊗₁-emb (φ ⊗₁ ψ) (α , β)
              Ct.⨾ ⊗₁-emb (φ' ⊗₁ ψ') (C.idn l' , C.idn r')
          link-pre =
              (λ i → ⊗₁-emb ((φ ⊗₁ ψ) Ct.⨾ (φ' ⊗₁ ψ'))
                       (Ct.unitr α (~ i) , Ct.unitr β (~ i)))
            ∙ ⊗₁-bifunctor (φ ⊗₁ ψ) (φ' ⊗₁ ψ')
                α (C.idn l') β (C.idn r')

          mid : PathP (λ i → disp₂ i)
                  ( ⊗₁-emb (φ ⊗₁ ψ) (α , β)
                    Ct.⨾ ⊗₁-emb (φ' ⊗₁ ψ') (C.idn l' , C.idn r') )
                  ( ⊗₁-emb φ (α , ⊗₁-pre ψ β)
                    Ct.⨾ ⊗₁-emb φ' (C.idn l' , ⊗₁-pre ψ' (C.idn r')) )
          mid i =
            ⊗₁-emb-comp φ ψ α β i
            Ct.⨾ ⊗₁-emb-comp φ' ψ' (C.idn l') (C.idn r') i

          suf
            : ⊗₁-emb φ (α , ⊗₁-pre ψ β)
              Ct.⨾ ⊗₁-emb φ' (C.idn l' , ⊗₁-pre ψ' (C.idn r'))
            ≡ ⊗₁-emb (φ Ct.⨾ φ') (α , ⊗₁-pre (ψ Ct.⨾ ψ') β)
          suf =
              sym (⊗₁-bifunctor φ φ'
                     α (C.idn l') (⊗₁-pre ψ β) (⊗₁-pre ψ' (C.idn r')))
            ∙ (λ i → ⊗₁-emb (φ Ct.⨾ φ')
                       (Ct.unitr α i , ⊗₁-pre-comp ψ ψ' β i))
```

## Morphism-level pre and post comparisons

The pre-composite comparison is the spine's pre-side
characterization read at the unit context. The two composite
comparisons `⊗₁-comp-eq-pre`/`⊗₁-comp-eq-post` displace the
object-level factorizations of `⊗₀-comp-eq-pre`/`⊗₀-comp-eq-post`:
each is a three-piece paste through the spine center — `⊗₁-unit`
at the identity context, the spine's pre- or post-side
characterization, and a `⊗₁-unit` whisker collapsing the
unit-slot action.

```agda
  ⊗₁-pre-composite
    : ∀ {y y'} (ψ : C.hom y y') {z z'} (θ : C.hom z z')
        {r r'} (β : C.hom r r')
    → PathP (λ i → C.hom (⊗₀-pre-composite y z r i)
                         (⊗₀-pre-composite y' z' r' i))
            (⊗₁-pre (ψ ⊗₁ θ) β)
            (⊗₁-pre ψ (⊗₁-pre θ β))
  ⊗₁-pre-composite ψ θ β = ⊗₁-emb-comp ψ θ (C.idn I) β

  ⊗₁-comp-eq-pre
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
    → PathP (λ i → C.hom (⊗₀-comp-eq-pre x y i)
                         (⊗₀-comp-eq-pre x' y' i))
            (φ ⊗₁ ψ) (⊗₁-pre φ ψ)
  ⊗₁-comp-eq-pre {x} {x'} φ {y} {y'} ψ =
    compHomP
      (sym (⊗₀-unit (x ⊗ y)) ∙ ap ⊗₀-ev (⊗₀-emb-comp x y))
      (ap (λ t → ⊗₀-pre x t) (⊗₀-unit y))
      (sym (⊗₀-unit (x' ⊗ y')) ∙ ap ⊗₀-ev (⊗₀-emb-comp x' y'))
      (ap (λ t → ⊗₀-pre x' t) (⊗₀-unit y'))
      (compHomP
        (sym (⊗₀-unit (x ⊗ y))) (ap ⊗₀-ev (⊗₀-emb-comp x y))
        (sym (⊗₀-unit (x' ⊗ y'))) (ap ⊗₀-ev (⊗₀-emb-comp x' y'))
        (sym (⊗₁-unit (φ ⊗₁ ψ)))
        (⊗₁-emb-comp φ ψ (C.idn I) (C.idn I)))
      (λ i → ⊗₁-emb φ (C.idn I , ⊗₁-unit ψ i))

  ⊗₁-comp-eq-post
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
    → PathP (λ i → C.hom (⊗₀-comp-eq-post x y i)
                         (⊗₀-comp-eq-post x' y' i))
            (φ ⊗₁ ψ) (⊗₁-post ψ φ)
  ⊗₁-comp-eq-post {x} {x'} φ {y} {y'} ψ =
    compHomP
      (sym (⊗₀-unit (x ⊗ y)))
      (ap ⊗₀-ev (⊗₀-emb-comp-op x y)
        ∙ ap (λ t → ⊗₀-post y t) (⊗₀-unit x))
      (sym (⊗₀-unit (x' ⊗ y')))
      (ap ⊗₀-ev (⊗₀-emb-comp-op x' y')
        ∙ ap (λ t → ⊗₀-post y' t) (⊗₀-unit x'))
      (sym (⊗₁-unit (φ ⊗₁ ψ)))
      (compHomP
        (ap ⊗₀-ev (⊗₀-emb-comp-op x y))
        (ap (λ t → ⊗₀-post y t) (⊗₀-unit x))
        (ap ⊗₀-ev (⊗₀-emb-comp-op x' y'))
        (ap (λ t → ⊗₀-post y' t) (⊗₀-unit x'))
        (⊗₁-emb-comp-op φ ψ (C.idn I) (C.idn I))
        (λ i → ⊗₁-emb ψ (⊗₁-unit φ i , C.idn I)))
```

## Unit idempotence and absorption

The unit is idempotent under the derived tensor, and its pre-
and post-actions are absorbed, at the morphism level. Absorption
is the round trip from the unit action through the spine center
to the identity context, pasted over the object absorption's own
factorization; `⊗₁-idem` is the same paste at the unit.

```agda
  ⊗₁-idem
    : PathP (λ i → C.hom (⊗₀-idem i) (⊗₀-idem i))
            ((C.idn I) ⊗₁ (C.idn I)) (C.idn I)
  ⊗₁-idem =
    compHomP
      (⊗₀-comp-eq-pre I I) (⊗₀-unit I)
      (⊗₀-comp-eq-pre I I) (⊗₀-unit I)
      (⊗₁-comp-eq-pre (C.idn I) (C.idn I))
      (⊗₁-unit (C.idn I))

  ⊗₁-absorb-l
    : ∀ {r r'} (β : C.hom r r')
    → PathP (λ i → C.hom (⊗₀-absorb-l r i) (⊗₀-absorb-l r' i))
            (⊗₁-pre (C.idn I) β) β
  ⊗₁-absorb-l {r} {r'} β =
    compHomP
      (sym (⊗₀-comp-eq-pre I r) ∙ ⊗₀-comp-eq-post I r)
      (⊗₀-unit r)
      (sym (⊗₀-comp-eq-pre I r') ∙ ⊗₀-comp-eq-post I r')
      (⊗₀-unit r')
      (compHomP
        (sym (⊗₀-comp-eq-pre I r)) (⊗₀-comp-eq-post I r)
        (sym (⊗₀-comp-eq-pre I r')) (⊗₀-comp-eq-post I r')
        (sym (⊗₁-comp-eq-pre (C.idn I) β))
        (⊗₁-comp-eq-post (C.idn I) β))
      (⊗₁-unit β)
```

The right-hand absorption factors through the same round trip,
but the object `⊗₀-absorb-r` presents as the symmetry of a
composite. The paste is built over the equivalent `∙`-chain
`sym ⊗₀-comp-eq-post ∙ ⊗₀-comp-eq-pre ∙ ⊗₀-unit` and carried
across the `sym-distr` identification.

```agda
  private
    absorb-r-chain
      : ∀ (l : C.ob)
      → ⊗₀-absorb-r l
      ≡ sym (⊗₀-comp-eq-post l I)
        ∙ (⊗₀-comp-eq-pre l I ∙ ⊗₀-unit l)
    absorb-r-chain l =
        ap (_∙ ⊗₀-unit l)
          (sym-distr (sym (⊗₀-comp-eq-pre l I)) (⊗₀-comp-eq-post l I))
      ∙ sym (Path.assoc
              (sym (⊗₀-comp-eq-post l I)) (⊗₀-comp-eq-pre l I)
              (⊗₀-unit l))

  ⊗₁-absorb-r
    : ∀ {l l'} (χ : C.hom l l')
    → PathP (λ i → C.hom (⊗₀-absorb-r l i) (⊗₀-absorb-r l' i))
            (⊗₁-post (C.idn I) χ) χ
  ⊗₁-absorb-r {l} {l'} χ =
    transport⁻
      (ap2s (λ p q → PathP (λ i → C.hom (p i) (q i))
                       (⊗₁-post (C.idn I) χ) χ)
        (absorb-r-chain l) (absorb-r-chain l'))
      chain-absorb
    where
      chain-absorb
        : PathP (λ i → C.hom
                  ((sym (⊗₀-comp-eq-post l I)
                     ∙ (⊗₀-comp-eq-pre l I ∙ ⊗₀-unit l)) i)
                  ((sym (⊗₀-comp-eq-post l' I)
                     ∙ (⊗₀-comp-eq-pre l' I ∙ ⊗₀-unit l')) i))
                (⊗₁-post (C.idn I) χ) χ
      chain-absorb =
        compHomP
          (sym (⊗₀-comp-eq-post l I))
          (⊗₀-comp-eq-pre l I ∙ ⊗₀-unit l)
          (sym (⊗₀-comp-eq-post l' I))
          (⊗₀-comp-eq-pre l' I ∙ ⊗₀-unit l')
          (sym (⊗₁-comp-eq-post χ (C.idn I)))
          (compHomP
            (⊗₀-comp-eq-pre l I) (⊗₀-unit l)
            (⊗₀-comp-eq-pre l' I) (⊗₀-unit l')
            (⊗₁-comp-eq-pre χ (C.idn I))
            (⊗₁-unit χ))
```
