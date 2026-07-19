Lane Biocini
July 2026

Monoidal categories over a `Cat.Type` category, presented through a
representable tensor embedding `⊗₀-emb` into two-slot tensor contexts.

This is the erased-index image of the `Cat.Type` presentation:
contexts collapse to pairs of objects, composites are object-valued
families on contexts, the monoidal unit is the erased identity, and
the binary tensor is the center of a contractible spine. The unit
laws, absorption, uniqueness of the unit, and the associator are
derived from the contractibility machinery rather than assumed.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base
open import Core.Transport.J using (J; subst)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding
  using (image-fibers-contr→is-embedding; equiv→lc)

open import Cat.Type
import Cat.Base
```

## Tensor contexts

The erased virtual layer: over- and under-arrows collapse to bare
objects, so a tensor context is a pair of factor slots `(l , r)`,
a composite is an object-valued family on contexts, and evaluation
`⊗₀-ev` reads at the identity context `(I , I)`. The unit slot plays
the role of the graph's reflexivity: it is the erased `idn`.

```agda
module tensor-virtual {o h} (C : category o h) (I : category.ob C) where
  private module C = category C

  ⊗₀-composite : Type o
  ⊗₀-composite = C.ob × C.ob → C.ob

  ⊗₀-ev : ⊗₀-composite → C.ob
  ⊗₀-ev F = F (I , I)
```

## The representable layer

`⊗₀-is-representable F` is the fiber of `⊗₀-emb` at `F`; `⊗₀-nrm` is the
canonical representation. `⊗₀-pre` and `⊗₀-post` are the unit-slot
actions; `⊗₀-sub`/`⊗₀-cosub` substitute them into context slots, giving
the two one-sided composite operators `⊗₀·`/`⊗₀·ᵒᵖ` and the two
composite-composite orders `⊗₀·'`/`⊗₀·''`. `⊗₀-interchange♭-from` closes
the ternary interchange over the fibers of `⊗₀-emb`.

```agda
module tensor-representable {o h} (C : category o h) (I : category.ob C)
  (⊗₀-emb : category.ob C → category.ob C × category.ob C → category.ob C) where
  private module C = category C
  open tensor-virtual C I

  ⊗₀-is-representable : ⊗₀-composite → Type o
  ⊗₀-is-representable = fiber ⊗₀-emb

  _⊨_ : ⊗₀-composite → C.ob → Type o
  F ⊨ s = ⊗₀-emb s ≡ F

  ⊗₀-nrm : (x : C.ob) → ⊗₀-is-representable (⊗₀-emb x)
  ⊗₀-nrm x = x , refl

  ⊗₀-pre : C.ob → C.ob → C.ob
  ⊗₀-pre y r = ⊗₀-emb y (I , r)

  ⊗₀-post : C.ob → C.ob → C.ob
  ⊗₀-post x l = ⊗₀-emb x (l , I)

  ⊗₀-sub : C.ob → C.ob × C.ob → C.ob × C.ob
  ⊗₀-sub y (l , r) = l , ⊗₀-pre y r

  ⊗₀-cosub : C.ob → C.ob × C.ob → C.ob × C.ob
  ⊗₀-cosub x (l , r) = ⊗₀-post x l , r

  _⊗₀·_ : ⊗₀-composite → C.ob → ⊗₀-composite
  (F ⊗₀· y) γ = F (⊗₀-sub y γ)
  infixl 30 _⊗₀·_

  _⊗₀·ᵒᵖ_ : C.ob → ⊗₀-composite → ⊗₀-composite
  (x ⊗₀·ᵒᵖ F) γ = F (⊗₀-cosub x γ)
  infixl 30 _⊗₀·ᵒᵖ_

  _⊗₀·'_ : (⊗₀-composite) → (⊗₀-composite) → ⊗₀-composite
  (F ⊗₀·' G) (l , r) = F (l , G (I , r))
  infixl 30 _⊗₀·'_

  _⊗₀·''_ : (⊗₀-composite) → (⊗₀-composite) → ⊗₀-composite
  (F ⊗₀·'' G) (l , r) = G (F (l , I) , r)
  infixl 30 _⊗₀·''_

  -- closure of the ternary interchange over the fibers of ⊗₀-emb;
  -- at ⊗₀-nrm endpoints it agrees with the input up to J-refl
  ⊗₀-interchange♭-from
    : (∀ (x y : C.ob) → ⊗₀-emb x ⊗₀· y ≡ x ⊗₀·ᵒᵖ ⊗₀-emb y)
    → ∀ {F G : ⊗₀-composite}
    → ⊗₀-is-representable F → ⊗₀-is-representable G
    → F ⊗₀·' G ≡ F ⊗₀·'' G
  ⊗₀-interchange♭-from ι {G = G} (m , p) (n , q) =
    J (λ F' _ → F' ⊗₀·' G ≡ F' ⊗₀·'' G)
      (J (λ G' _ → ⊗₀-emb m ⊗₀·' G' ≡ ⊗₀-emb m ⊗₀·'' G') (ι m n) q)
      p
```

## The monoidal record

`I` is the erased reflexive element; `⊗₀-interchange♭` is the flat
interchange at arbitrary representables; `⊗₀-spine-contr` packs the
tensor candidate, its two comparisons, and the coherence 2-cell into
a contractible spine; `⊗₀-unit` is evaluation at the identity context.
The binary tensor is the spine's center.

```agda
record monoidal {o h} (C : category o h) : Type₊ (o ⊔ h) where
  no-eta-equality
  private module C = category C

  field
    I : C.ob

  open tensor-virtual C I public

  field
    ⊗₀-emb : C.ob → ⊗₀-composite

  open tensor-representable C I ⊗₀-emb public

  field
    ⊗₀-interchange♭
      : ∀ {F G : ⊗₀-composite}
      → ⊗₀-is-representable F → ⊗₀-is-representable G
      → F ⊗₀·' G ≡ F ⊗₀·'' G

  ⊗₀-interchange : (x y : C.ob) → ⊗₀-emb x ⊗₀· y ≡ x ⊗₀·ᵒᵖ ⊗₀-emb y
  ⊗₀-interchange x y = ⊗₀-interchange♭ (⊗₀-nrm x) (⊗₀-nrm y)

  ⊗₀-spine : (x y : C.ob) → Type o
  ⊗₀-spine x y =
    Σ k ∶ C.ob ,
    Σ p ∶ (⊗₀-emb k ≡ ⊗₀-emb x ⊗₀· y) ,
    Σ q ∶ (⊗₀-emb k ≡ x ⊗₀·ᵒᵖ ⊗₀-emb y) ,
      PathP (λ i → ⊗₀-emb k ≡ ⊗₀-interchange x y i) p q

  field
    ⊗₀-spine-contr : ∀ x y → is-contr (⊗₀-spine x y)
    ⊗₀-unit : ∀ x → ⊗₀-emb x (I , I) ≡ x

  _⊗_ : C.ob → C.ob → C.ob
  x ⊗ y = ⊗₀-spine-contr x y .center .fst
  infixr 40 _⊗_

  ⊗₀-emb-comp : ∀ x y → ⊗₀-emb (x ⊗ y) ≡ ⊗₀-emb x ⊗₀· y
  ⊗₀-emb-comp x y = ⊗₀-spine-contr x y .center .snd .fst

  ⊗₀-emb-comp-op : ∀ x y → ⊗₀-emb (x ⊗ y) ≡ x ⊗₀·ᵒᵖ ⊗₀-emb y
  ⊗₀-emb-comp-op x y = ⊗₀-spine-contr x y .center .snd .snd .fst

  -- the spine's 2-cell: the two composite comparisons agree along
  -- ⊗₀-interchange
  ⊗₀-emb-comp-coh
    : ∀ x y
    → PathP (λ i → ⊗₀-emb (x ⊗ y) ≡ ⊗₀-interchange x y i)
            (⊗₀-emb-comp x y) (⊗₀-emb-comp-op x y)
  ⊗₀-emb-comp-coh x y = ⊗₀-spine-contr x y .center .snd .snd .snd

  ⊗coh→∙ : ∀ x y → ⊗₀-emb-comp x y ∙ ⊗₀-interchange x y ≡ ⊗₀-emb-comp-op x y
  ⊗coh→∙ x y =
      Path.commutes
        (⊗₀-emb-comp x y) (⊗₀-interchange x y) refl (⊗₀-emb-comp-op x y)
        (⊗₀-emb-comp-coh x y)
    ∙ Path.unitl (⊗₀-emb-comp-op x y)

  private module Ct = Cat.Base.theory C

  -- the morphism layer: a morphism of tensor contexts is a pair of
  -- morphisms, and ⊗₁-emb is the trifunctor action on it; the indices
  -- of the derived binary tensor range over the derived _⊗_
  field
    ⊗₁-emb : ∀ {m m'} (φ : C.hom m m') {l l' r r'}
          → C.hom l l' × C.hom r r'
          → C.hom (⊗₀-emb m (l , r)) (⊗₀-emb m' (l' , r'))

  ⊗₁-pre : ∀ {y y'} (ψ : C.hom y y') {r r'} (χ : C.hom r r')
        → C.hom (⊗₀-pre y r) (⊗₀-pre y' r')
  ⊗₁-pre ψ χ = ⊗₁-emb ψ (C.idn I , χ)

  ⊗₁-post : ∀ {x x'} (φ : C.hom x x') {l l'} (α : C.hom l l')
        → C.hom (⊗₀-post x l) (⊗₀-post x' l')
  ⊗₁-post φ α = ⊗₁-emb φ (α , C.idn I)

  field
    ⊗₁-unit
      : ∀ {x x'} (φ : C.hom x x')
      → PathP (λ i → C.hom (⊗₀-unit x i) (⊗₀-unit x' i))
              (⊗₁-emb φ (C.idn I , C.idn I)) φ

    ⊗₁-interchange
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
          {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
      → PathP (λ i → C.hom (happly (⊗₀-interchange x y) (l , r) i)
                            (happly (⊗₀-interchange x' y') (l' , r') i))
              (⊗₁-emb φ (α , ⊗₁-pre ψ β))
              (⊗₁-emb ψ (⊗₁-post φ α , β))

    ⊗₁-bifunctor
      : ∀ {x x' x''} (φ₁ : C.hom x x') (φ₂ : C.hom x' x'')
          {l l' l''} (α₁ : C.hom l l') (α₂ : C.hom l' l'')
          {r r' r''} (β₁ : C.hom r r') (β₂ : C.hom r' r'')
      → ⊗₁-emb (φ₁ Ct.⨾ φ₂) ((α₁ Ct.⨾ α₂) , (β₁ Ct.⨾ β₂))
      ≡ ⊗₁-emb φ₁ (α₁ , β₁) Ct.⨾ ⊗₁-emb φ₂ (α₂ , β₂)

  ⊗₁-spine : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y') → Type (o ⊔ h)
  ⊗₁-spine {x} {x'} φ {y} {y'} ψ =
    Σ σ ∶ C.hom (x ⊗ y) (x' ⊗ y') ,
    Σ p ∶ (∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
           → PathP (λ j → C.hom (happly (⊗₀-emb-comp x y) (l , r) j)
                                 (happly (⊗₀-emb-comp x' y') (l' , r') j))
                   (⊗₁-emb σ (α , β))
                   (⊗₁-emb φ (α , ⊗₁-pre ψ β))) ,
    Σ q ∶ (∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
           → PathP (λ j → C.hom (happly (⊗₀-emb-comp-op x y) (l , r) j)
                                 (happly (⊗₀-emb-comp-op x' y') (l' , r') j))
                   (⊗₁-emb σ (α , β))
                   (⊗₁-emb ψ (⊗₁-post φ α , β))) ,
      ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
      → PathP
          (λ i → PathP
            (λ j → C.hom (⊗₀-emb-comp-coh x y i j (l , r))
                          (⊗₀-emb-comp-coh x' y' i j (l' , r')))
            (⊗₁-emb σ (α , β))
            (⊗₁-interchange φ ψ α β i))
          (p α β) (q α β)

  field
    ⊗₁-spine-contr : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
                  → is-contr (⊗₁-spine φ ψ)
```

## Derived theory

The derived tensor on morphisms `_⊗₁_` is the hom-spine's center,
with `⊗₁-emb-comp`, `⊗₁-emb-comp-op`, and `⊗₁-emb-comp-coh` its
characterizations. `_●_`/`_●''_` compose representations along the
two composite orders; the pull and push fibers of `⊗₀-emb` over the
one-sided composites are contractible by projection from the object
spine, giving the `cast-path` pair for composite witnesses.

```agda
module theory {o h} {C : category o h} (M : monoidal C) where
  private module C = category C
  open monoidal M

  _⊗₁_ : ∀ {x x'} → C.hom x x' → ∀ {y y'} → C.hom y y' → C.hom (x ⊗ y) (x' ⊗ y')
  φ ⊗₁ ψ = ⊗₁-spine-contr φ ψ .center .fst
  infixr 40 _⊗₁_

  -- the remaining hom-spine projections: the pre- and post-side
  -- characterizations of φ ⊗₁ ψ, and the 2-cell relating them over
  -- the object spine's square
  ⊗₁-emb-comp
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
    → PathP (λ j → C.hom (happly (⊗₀-emb-comp x y) (l , r) j)
                          (happly (⊗₀-emb-comp x' y') (l' , r') j))
            (⊗₁-emb (φ ⊗₁ ψ) (α , β))
            (⊗₁-emb φ (α , ⊗₁-pre ψ β))
  ⊗₁-emb-comp φ ψ α β = ⊗₁-spine-contr φ ψ .center .snd .fst α β

  ⊗₁-emb-comp-op
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
    → PathP (λ j → C.hom (happly (⊗₀-emb-comp-op x y) (l , r) j)
                          (happly (⊗₀-emb-comp-op x' y') (l' , r') j))
            (⊗₁-emb (φ ⊗₁ ψ) (α , β))
            (⊗₁-emb ψ (⊗₁-post φ α , β))
  ⊗₁-emb-comp-op φ ψ α β = ⊗₁-spine-contr φ ψ .center .snd .snd .fst α β

  ⊗₁-emb-comp-coh
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
    → PathP
        (λ i → PathP
          (λ j → C.hom (⊗₀-emb-comp-coh x y i j (l , r))
                        (⊗₀-emb-comp-coh x' y' i j (l' , r')))
          (⊗₁-emb (φ ⊗₁ ψ) (α , β))
          (⊗₁-interchange φ ψ α β i))
        (⊗₁-emb-comp φ ψ α β) (⊗₁-emb-comp-op φ ψ α β)
  ⊗₁-emb-comp-coh φ ψ α β = ⊗₁-spine-contr φ ψ .center .snd .snd .snd α β

  _●_ : ∀ {F G : ⊗₀-composite}
      → ⊗₀-is-representable F → ⊗₀-is-representable G
      → ⊗₀-is-representable (F ⊗₀·' G)
  (m , p) ● (n , q) = m ⊗ n , ⊗₀-emb-comp m n ∙ (λ i → p i ⊗₀·' q i)

  _●''_ : ∀ {F G : ⊗₀-composite}
        → ⊗₀-is-representable F → ⊗₀-is-representable G
        → ⊗₀-is-representable (F ⊗₀·'' G)
  (m , p) ●'' (n , q) = m ⊗ n , ⊗₀-emb-comp-op m n ∙ (λ i → p i ⊗₀·'' q i)

  private
    fwd : ∀ x y → fiber ⊗₀-emb (⊗₀-emb x ⊗₀· y) → ⊗₀-spine x y
    fwd x y (k , r) =
      k , r , r ∙ ⊗₀-interchange x y , transpose (cat.fill r (⊗₀-interchange x y))

    bwd : ∀ x y → fiber ⊗₀-emb (x ⊗₀·ᵒᵖ ⊗₀-emb y) → ⊗₀-spine x y
    bwd x y (k , r) =
      k , r ∙ sym ι , r , sym (transpose (cat.fill r (sym ι)))
      where ι = ⊗₀-interchange x y

  -- the spine's candidate and each comparison, coerced to the two
  -- fibers of ⊗₀-emb over the one-sided composites
  ⊗₀-spine→pull : ∀ {x y} → ⊗₀-spine x y → fiber ⊗₀-emb (⊗₀-emb x ⊗₀· y)
  ⊗₀-spine→pull s = s .fst , s .snd .fst

  ⊗₀-spine→push : ∀ {x y} → ⊗₀-spine x y → fiber ⊗₀-emb (x ⊗₀·ᵒᵖ ⊗₀-emb y)
  ⊗₀-spine→push s = s .fst , s .snd .snd .fst

  ⊗₀-pull-contr : ∀ x y → is-contr (fiber ⊗₀-emb (⊗₀-emb x ⊗₀· y))
  ⊗₀-pull-contr x y .center = x ⊗ y , ⊗₀-emb-comp x y
  ⊗₀-pull-contr x y .paths u i = ⊗₀-spine→pull (φ i) where
    φ : ⊗₀-spine-contr x y .center ≡ fwd x y u
    φ = ⊗₀-spine-contr x y .paths (fwd x y u)

  ⊗₀-push-contr : ∀ x y → is-contr (fiber ⊗₀-emb (x ⊗₀·ᵒᵖ ⊗₀-emb y))
  ⊗₀-push-contr x y .center = x ⊗ y , ⊗₀-emb-comp-op x y
  ⊗₀-push-contr x y .paths u i = ⊗₀-spine→push (φ i) where
    φ : ⊗₀-spine-contr x y .center ≡ bwd x y u
    φ = ⊗₀-spine-contr x y .paths (bwd x y u)

  -- a composite witness: k represents the two-sided tensor of x and y
  ⊗₀-cast-path : ∀ {x y k} → (⊗₀-emb x ⊗₀· y) ⊨ k → x ⊗ y ≡ k
  ⊗₀-cast-path {x} {y} {k} α = ap fst (⊗₀-pull-contr x y .paths (k , α))

  ⊗₀-cast-path⁻¹ : ∀ {x y k} → x ⊗ y ≡ k → (⊗₀-emb x ⊗₀· y) ⊨ k
  ⊗₀-cast-path⁻¹ {x} {y} p = ap ⊗₀-emb (sym p) ∙ ⊗₀-emb-comp x y

  ⊗₀-post-composite : ∀ x y l → ⊗₀-post (x ⊗ y) l ≡ ⊗₀-post y (⊗₀-post x l)
  ⊗₀-post-composite x y l = happly (⊗₀-emb-comp x y ∙ ⊗₀-interchange x y) (l , I)

  ⊗₀-pre-composite : ∀ y z r → ⊗₀-pre (y ⊗ z) r ≡ ⊗₀-pre y (⊗₀-pre z r)
  ⊗₀-pre-composite y z r = happly (⊗₀-emb-comp y z) (I , r)
```

The following lemmas depend on ⊗₀-unit

```agda
  ⊗₀-comp-eq-ev : ∀ x y → x ⊗ y ≡ ⊗₀-ev (⊗₀-emb x ⊗₀· y)
  ⊗₀-comp-eq-ev x y = sym (⊗₀-unit (x ⊗ y)) ∙ ap ⊗₀-ev (⊗₀-emb-comp x y)

  ⊗₀-comp-eq-pre : ∀ x y → x ⊗ y ≡ ⊗₀-pre x y
  ⊗₀-comp-eq-pre x y = ⊗₀-comp-eq-ev x y ∙ ap (λ t → ⊗₀-pre x t) (⊗₀-unit y)

  ⊗₀-comp-eq-post : ∀ x y → x ⊗ y ≡ ⊗₀-post y x
  ⊗₀-comp-eq-post x y =
    sym (⊗₀-unit (x ⊗ y)) ∙ ap ⊗₀-ev (⊗₀-emb-comp-op x y) ∙ ap (λ t → ⊗₀-post y t) (⊗₀-unit x)

  ⊗₀-idem : I ⊗ I ≡ I
  ⊗₀-idem = ⊗₀-comp-eq-pre I I ∙ ⊗₀-unit I

  ⊗₀-pre-is-post : ∀ x y → ⊗₀-pre x y ≡ ⊗₀-post y x
  ⊗₀-pre-is-post x y = sym (⊗₀-comp-eq-pre x y) ∙ ⊗₀-comp-eq-post x y

  ⊗₀-absorb-l : ∀ r → ⊗₀-pre I r ≡ r
  ⊗₀-absorb-l r = ⊗₀-pre-is-post I r ∙ ⊗₀-unit r

  ⊗₀-absorb-r : ∀ l → ⊗₀-post I l ≡ l
  ⊗₀-absorb-r l = sym (⊗₀-pre-is-post l I) ∙ ⊗₀-unit l

  ⊗₀-I-·ᵒᵖ : ∀ (F : ⊗₀-composite) → I ⊗₀·ᵒᵖ F ≡ F
  ⊗₀-I-·ᵒᵖ F = funext λ (l , r) → ap (λ t → F (t , r)) (⊗₀-absorb-r l)

  ⊗₀-·-I : ∀ (F : ⊗₀-composite) → F ⊗₀· I ≡ F
  ⊗₀-·-I F = funext λ (l , r) → ap (λ t → F (l , t)) (⊗₀-absorb-l r)

  ⊗₀-emb-I-· : ∀ x → ⊗₀-emb I ⊗₀· x ≡ ⊗₀-emb x
  ⊗₀-emb-I-· x = ⊗₀-interchange I x ∙ ⊗₀-I-·ᵒᵖ (⊗₀-emb x)

  ⊗₀-emb-image-contr : ∀ x → is-contr (fiber ⊗₀-emb (⊗₀-emb x))
  ⊗₀-emb-image-contr x =
    subst (λ F → is-contr (fiber ⊗₀-emb F)) (⊗₀-I-·ᵒᵖ (⊗₀-emb x)) (⊗₀-push-contr I x)

  ⊗₀-is-representable-prop : ∀ F → is-prop (⊗₀-is-representable F)
  ⊗₀-is-representable-prop = image-fibers-contr→is-embedding ⊗₀-emb-image-contr

  ⊗₀-rep-contr : ∀ {F} → ⊗₀-is-representable F → is-contr (⊗₀-is-representable F)
  ⊗₀-rep-contr {F} u .center = u
  ⊗₀-rep-contr {F} u .paths = ⊗₀-is-representable-prop F u

  ⊗₀-repr-unique : ∀ {F} (u v : ⊗₀-is-representable F) → u .fst ≡ v .fst
  ⊗₀-repr-unique {F} u v = ap fst (⊗₀-is-representable-prop F u v)

  _⊳_ : ∀ {F G : ⊗₀-composite}
      → ⊗₀-is-representable F → F ≡ G → ⊗₀-is-representable G
  (m , p) ⊳ e = m , p ∙ e

  ⊗₀-emb-post : ∀ x l r → ⊗₀-emb x (l , r) ≡ ⊗₀-emb I (⊗₀-post x l , r)
  ⊗₀-emb-post x l r =
    ap (λ t → ⊗₀-emb x (l , t)) (sym (⊗₀-absorb-l r))
    ∙ happly (⊗₀-interchange x I) (l , r)

  ⊗₀-emb-pre : ∀ x l r → ⊗₀-emb x (l , r) ≡ ⊗₀-emb I (l , ⊗₀-pre x r)
  ⊗₀-emb-pre x l r =
    ap (λ t → ⊗₀-emb x (t , r)) (sym (⊗₀-absorb-r l))
    ∙ sym (happly (⊗₀-interchange I x) (l , r))
```

Associativity and the unit laws are projections from contractible
fibers of representations

```agda
  ⊗₀-assoc-σ● : ∀ {F G H : ⊗₀-composite}
            → (U : ⊗₀-is-representable F) (V : ⊗₀-is-representable G)
              (W : ⊗₀-is-representable H)
            → U ● (V ● W) ≡ (U ● V) ● W
  ⊗₀-assoc-σ● U V W = ⊗₀-is-representable-prop _ (U ● (V ● W)) ((U ● V) ● W)

  ⊗₀-assoc● : ∀ {F G H : ⊗₀-composite}
          → (U : ⊗₀-is-representable F) (V : ⊗₀-is-representable G)
            (W : ⊗₀-is-representable H)
          → fst (U ● (V ● W)) ≡ fst ((U ● V) ● W)
  ⊗₀-assoc● U V W = ap fst (⊗₀-assoc-σ● U V W)

  ⊗₀-assoc : ∀ x y z → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
  ⊗₀-assoc x y z = sym (⊗₀-assoc● (⊗₀-nrm x) (⊗₀-nrm y) (⊗₀-nrm z))

  ⊗₀-unitr : ∀ x → x ⊗ I ≡ x
  ⊗₀-unitr x = ⊗₀-repr-unique ((⊗₀-nrm x ● ⊗₀-nrm I) ⊳ ⊗₀-·-I (⊗₀-emb x)) (⊗₀-nrm x)

  ⊗₀-unitl : ∀ x → I ⊗ x ≡ x
  ⊗₀-unitl x = ⊗₀-repr-unique ((⊗₀-nrm I ● ⊗₀-nrm x) ⊳ ⊗₀-emb-I-· x) (⊗₀-nrm x)
```

## Unit uniqueness

Any object whose middle-slot action at itself is an equivalence and
which is idempotent under `⊗₀-post` is uniquely the chosen unit `I`.
The argument is the Kraus chain: `⊗₀-post e` squares to itself and is
idempotent, so it absorbs, forcing `e ≡ I`.

```agda
  ⊗₀-unit-is-prop
    : (e : C.ob)
    → is-equiv (λ l → ⊗₀-emb e (l , e))
    → ⊗₀-post e e ≡ e
    → e ≡ I
  ⊗₀-unit-is-prop e re idpt =
    sym (⊗₀-unit e) ∙ post-e-absorb I
    where
      e-idem : e ⊗ e ≡ e
      e-idem = ⊗₀-comp-eq-post e e ∙ idpt

      post-e-idpt : ∀ l → ⊗₀-post e (⊗₀-post e l) ≡ ⊗₀-post e l
      post-e-idpt l =
        sym (⊗₀-post-composite e e l) ∙ ap (λ t → ⊗₀-post t l) e-idem

      post-e-squared : ∀ l → ⊗₀-emb e (l , e) ≡ ⊗₀-post e (⊗₀-post e l)
      post-e-squared l =
        ⊗₀-emb-post e l e
        ∙ sym (ap (λ t → ⊗₀-emb I (⊗₀-post e l , t)) (⊗₀-unit e))
        ∙ happly (⊗₀-interchange I e) (⊗₀-post e l , I)
        ∙ ap (⊗₀-post e) (⊗₀-absorb-r (⊗₀-post e l))

      post-e-absorb : ∀ l → ⊗₀-post e l ≡ l
      post-e-absorb l = equiv→lc re
        (post-e-squared (⊗₀-post e l)
        ∙ post-e-idpt (⊗₀-post e l)
        ∙ sym (post-e-squared l))
```
