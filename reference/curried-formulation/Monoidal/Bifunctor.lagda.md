Lane Biocini
July 2026

The 2-cell tensor `_⊗ₕ_` is functorial in vertical
composition. This is the morphism-level image of the
object-level `⊗-η` reasoning in `Cat.Depreciated.Type`: both sides of
`⊗ₕ-preserves-⨾` inhabit the contractible fiber
`htensor-compose-contr (φ ⨾ φ') (ψ ⨾ ψ')`, so the equation is
the `ap fst` of the canonical center agreeing with the
composite side.

The composite side is shown to satisfy the fiber
characterization by gluing three links: two homogeneous
rewrites through `htensor-bifunctor` (the horizontal/vertical
interchange) sandwich one `PathP` whisker, obtained by pasting
the two `⊗ₕ-comp-pt` displacement paths side by side. The
`hpre-comp` lemma collapses a vertical composite of
`hpre`-actions into a single one; it recurs in the later
naturality work.

The `PathP` link is threaded through `to-pathp`/`from-pathp`
directly, since `Core` carries only homogeneous whiskers.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Depreciated.Monoidal.Bifunctor where

open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Function.Embedding using (equiv→lc; equiv→lc-section)
open import Core.Kan
open import Core.Transport.Base
open import Core.Transport.J using (J)

open import Cat.Depreciated.Type
open import Cat.Depreciated.Monoidal
```

## Functoriality of the 2-cell tensor

```agda
module _ {o h} {C : category o h} (M : monoidal C) where
  open monoidal M
  private module C = category C
```

`compHomP` concatenates two `C.hom`-valued `PathP`s displaced
over composable object paths `pa ∙ qa` (left slot) and
`pb ∙ qb` (right slot). It is the two-object image of the
standard `compPathP`, gluing along the `cat.fill` fillers of
the two `_∙_`s with a single heterogeneous `com`. A candidate
for promotion to `Core.Path` should the need recur.

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

`hpre-comp` witnesses that stacking two `hpre`-actions
vertically is a single `hpre` of the composite. The two
injected splits cancelled are the unit slot `idn ⨾ idn` (via
`C.idem`) and the right slot `β ⨾ idn` (via `C.unitr`).

```agda
  hpre-comp
    : ∀ {y y'} (ψ : C.hom y y') {y''} (ψ' : C.hom y' y'')
        {r r'} (β : C.hom r r')
    → (hpre ψ β) C.⨾ (hpre ψ' (C.idn r')) ≡ hpre (ψ C.⨾ ψ') β
  hpre-comp {y} {y'} ψ {y''} ψ' {r} {r'} β =
      sym (htensor-bifunctor ψ ψ' (C.idn I) (C.idn I) β (C.idn r'))
    ∙ (λ i → htensor-emb (ψ C.⨾ ψ') (C.idem {I} i) (C.unitr β i))
```

Both sides of `⊗ₕ-preserves-⨾` live in the contractible fiber
of `htensor-compose-contr (φ ⨾ φ') (ψ ⨾ ψ')`. The left side is
its center; `rhs-charac` shows the composite side satisfies the
fiber's `PathP` characterization at every pair of slots.

```agda
  ⊗ₕ-preserves-⨾
    : ∀ {x x'} (φ : C.hom x x') {x''} (φ' : C.hom x' x'')
        {y y'} (ψ : C.hom y y') {y''} (ψ' : C.hom y' y'')
    → (φ C.⨾ φ') ⊗ₕ (ψ C.⨾ ψ') ≡ (φ ⊗ₕ ψ) C.⨾ (φ' ⊗ₕ ψ')
  ⊗ₕ-preserves-⨾ {x} {x'} φ {x''} φ' {y} {y'} ψ {y''} ψ' =
    ap fst
      (is-contr→is-prop
        (htensor-compose-contr (φ C.⨾ φ') (ψ C.⨾ ψ'))
        (htensor-compose-contr (φ C.⨾ φ') (ψ C.⨾ ψ') .center)
        ((φ ⊗ₕ ψ) C.⨾ (φ' ⊗ₕ ψ') , rhs-charac))
    where
      rhs-charac
        : ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
        → PathP (λ i → C.hom (tensor-emb-comp-pt x  y  l  r  i)
                             (tensor-emb-comp-pt x'' y'' l' r' i))
                (htensor-emb ((φ ⊗ₕ ψ) C.⨾ (φ' ⊗ₕ ψ')) α β)
                (htensor-emb (φ C.⨾ φ') α (hpre (ψ C.⨾ ψ') β))
      rhs-charac {l} {l'} α {r} {r'} β =
        Path-over.to-pathp
          ( ap (transport disp₂) link-pre
          ∙ Path-over.from-pathp mid
          ∙ suf )
        where
          disp₂ : C.hom (tensor-emb (x ⊗ y) l r)
                        (tensor-emb (x'' ⊗ y'') l' r')
                ≡ C.hom (tensor-emb x l (pre y r))
                        (tensor-emb x'' l' (pre y'' r'))
          disp₂ i = C.hom (tensor-emb-comp-pt x  y  l  r  i)
                          (tensor-emb-comp-pt x'' y'' l' r' i)

          link-pre : htensor-emb ((φ ⊗ₕ ψ) C.⨾ (φ' ⊗ₕ ψ')) α β
              ≡ htensor-emb (φ ⊗ₕ ψ) α β
                C.⨾ htensor-emb (φ' ⊗ₕ ψ') (C.idn l') (C.idn r')
          link-pre =
              (λ i → htensor-emb ((φ ⊗ₕ ψ) C.⨾ (φ' ⊗ₕ ψ'))
                       (C.unitr α (~ i)) (C.unitr β (~ i)))
            ∙ htensor-bifunctor (φ ⊗ₕ ψ) (φ' ⊗ₕ ψ')
                α (C.idn l') β (C.idn r')

          mid : PathP (λ i → disp₂ i)
                  ( htensor-emb (φ ⊗ₕ ψ) α β
                    C.⨾ htensor-emb (φ' ⊗ₕ ψ') (C.idn l') (C.idn r') )
                  ( htensor-emb φ α (hpre ψ β)
                    C.⨾ htensor-emb φ' (C.idn l') (hpre ψ' (C.idn r')) )
          mid i = ⊗ₕ-comp-pt φ ψ α β i
                  C.⨾ ⊗ₕ-comp-pt φ' ψ' (C.idn l') (C.idn r') i

          suf : htensor-emb φ α (hpre ψ β)
                C.⨾ htensor-emb φ' (C.idn l') (hpre ψ' (C.idn r'))
              ≡ htensor-emb (φ C.⨾ φ') α (hpre (ψ C.⨾ ψ') β)
          suf =
              sym (htensor-bifunctor φ φ'
                     α (C.idn l') (hpre ψ β) (hpre ψ' (C.idn r')))
            ∙ (λ i → htensor-emb (φ C.⨾ φ')
                       (C.unitr α i) (hpre-comp ψ ψ' β i))
```

## Morphism-level identity and absorption

Each lemma below is the `PathP`-displacement of an object-level
tensor identity, over the *same* object path. The base axioms
`⊗ₕ-comp-pt`, `htensor-interchange`, and `htensor-post-eval`
supply the displaced pieces; `compHomP` glues them over
concatenated object paths.

`hpre-composite` mirrors `tensor-pre-composite`: it is
`⊗ₕ-comp-pt` in the pre slot (`l = I`, `α = idn`). Both
endpoints reduce definitionally to `hpre` actions.

```agda
  hpre-composite
    : ∀ {y y'} (ψ : C.hom y y') {z z'} (ψ' : C.hom z z')
        {r r'} (β : C.hom r r')
    → PathP (λ i → C.hom (tensor-pre-composite y z r i)
                         (tensor-pre-composite y' z' r' i))
            (hpre (ψ ⊗ₕ ψ') β)
            (hpre ψ (hpre ψ' β))
  hpre-composite ψ ψ' β = ⊗ₕ-comp-pt ψ ψ' (C.idn I) β
```

`htensor-post-composite` mirrors `tensor-post-composite`: the
comp-pt displacement in the post slot (`r = I`, `β = idn`)
followed by the interchange displacement, glued over
`tensor-emb-comp-pt _ _ _ I ∙ tensor-interchange _ _ _ I`.

```agda
  htensor-post-composite
    : ∀ {x x'} (φ : C.hom x x') {y y'} (φ' : C.hom y y')
        {l l'} (α : C.hom l l')
    → PathP (λ i → C.hom (tensor-post-composite x y l i)
                         (tensor-post-composite x' y' l' i))
            (hpost (φ ⊗ₕ φ') α)
            (hpost φ' (hpost φ α))
  htensor-post-composite {x} {x'} φ {y} {y'} φ' {l} {l'} α =
    compHomP
      (tensor-emb-comp-pt x  y  l  I) (tensor-interchange x  y  l  I)
      (tensor-emb-comp-pt x' y' l' I) (tensor-interchange x' y' l' I)
      (⊗ₕ-comp-pt φ φ' α (C.idn I))
      (htensor-interchange φ φ' α (C.idn I))
```

`⊗ₕ-comp-eq` mirrors `⊗-comp-eq`: three displaced pieces over
`sym (tensor-post-eval _)`, `tensor-post-composite _ _ I`, and
`ap (post _) (tensor-post-eval _)`, glued with nested `compHomP`.

```agda
  ⊗ₕ-comp-eq
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
    → PathP (λ i → C.hom (⊗-comp-eq x y i) (⊗-comp-eq x' y' i))
            (φ ⊗ₕ ψ)
            (hpost ψ φ)
  ⊗ₕ-comp-eq {x} {x'} φ {y} {y'} ψ =
    compHomP
      (sym (tensor-post-eval (x ⊗ y)))
      (tensor-post-composite x y I ∙ ap (post y) (tensor-post-eval x))
      (sym (tensor-post-eval (x' ⊗ y')))
      (tensor-post-composite x' y' I ∙ ap (post y') (tensor-post-eval x'))
      (sym (htensor-post-eval (φ ⊗ₕ ψ)))
      (compHomP
        (tensor-post-composite x y I) (ap (post y) (tensor-post-eval x))
        (tensor-post-composite x' y' I) (ap (post y') (tensor-post-eval x'))
        (htensor-post-composite φ ψ (C.idn I))
        (λ i → hpost ψ (htensor-post-eval φ i)))
```

`htensor-post-idpt` is `htensor-post-eval` at the unit identity,
displacing `tensor-post-idpt`.

```agda
  htensor-post-idpt
    : PathP (λ i → C.hom (tensor-post-idpt i) (tensor-post-idpt i))
            (hpost (C.idn I) (C.idn I))
            (C.idn I)
  htensor-post-idpt = htensor-post-eval (C.idn I)
```

`⊗ₕ-idem` mirrors `⊗-idem`: the unit `⊗ₕ-comp-eq` glued with
`htensor-post-idpt` over `⊗-comp-eq I I ∙ tensor-post-idpt`. It
proves `idn ⊗ₕ idn ≡ idn` at the unit is field-free.

```agda
  ⊗ₕ-idem
    : PathP (λ i → C.hom (⊗-idem i) (⊗-idem i))
            ((C.idn I) ⊗ₕ (C.idn I))
            (C.idn I)
  ⊗ₕ-idem =
    compHomP
      (⊗-comp-eq I I) tensor-post-idpt
      (⊗-comp-eq I I) tensor-post-idpt
      (⊗ₕ-comp-eq (C.idn I) (C.idn I))
      htensor-post-idpt
```

## Associator naturality

`htensor-emb-nest` is the morphism-level image of
`tensor-emb-nest`: two `⊗ₕ-comp-pt` displacements glued over the
concatenated object nest path. The first expands the outer
composite `(φ ⊗ₕ ψ) ⊗ₕ θ`; the second the inner `φ ⊗ₕ ψ`, with
`θ`'s action carried in the pre slot as `hpre θ β`.

```agda
  htensor-emb-nest
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        {z z'} (θ : C.hom z z')
        {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
    → PathP (λ i → C.hom (tensor-emb-nest x  y  z  l  r  i)
                         (tensor-emb-nest x' y' z' l' r' i))
            (htensor-emb ((φ ⊗ₕ ψ) ⊗ₕ θ) α β)
            (htensor-emb φ α (hpre ψ (hpre θ β)))
  htensor-emb-nest {x} {x'} φ {y} {y'} ψ {z} {z'} θ
                   {l} {l'} α {r} {r'} β =
    compHomP
      (tensor-emb-comp-pt (x ⊗ y) z l r)
      (tensor-emb-comp-pt x y l (pre z r))
      (tensor-emb-comp-pt (x' ⊗ y') z' l' r')
      (tensor-emb-comp-pt x' y' l' (pre z' r'))
      (⊗ₕ-comp-pt (φ ⊗ₕ ψ) θ α β)
      (⊗ₕ-comp-pt φ ψ α (hpre θ β))
```

`htensor-E₃-contr` is the displaced image of `tensor-E₃-contr`.
The fiber index `σ` has the object-dependent type
`C.hom ((x⊗y)⊗z) ((x'⊗y')⊗z')`, so the characterizing `PathP`
is displaced over `tensor-emb-nest` rather than a bare object
equation. Its center is `((φ ⊗ₕ ψ) ⊗ₕ θ , htensor-emb-nest)`,
mirroring `tensor-E₃-contr`'s `((x⊗y)⊗z , tensor-emb-nest)`.

Contractibility transports `htensor-compose-contr (φ ⊗ₕ ψ) θ`
along the family `Cell`, which appends the fixed
`⊗ₕ-comp-pt φ ψ α (hpre θ β)` link to each fiber `PathP`. `Cell`
is built from the object-level `cat.fill` filler exactly as
`tensor-E₃-contr` substs `tensor-composable-contr (x⊗y) z` along
its pointwise `tensor-emb-comp-pt`.

```agda
  htensor-E₃-contr
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        {z z'} (θ : C.hom z z')
    → is-contr
        (Σ λ (σ : C.hom ((x ⊗ y) ⊗ z) ((x' ⊗ y') ⊗ z'))
           → ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
           → PathP (λ i → C.hom (tensor-emb-nest x  y  z  l  r  i)
                                (tensor-emb-nest x' y' z' l' r' i))
                   (htensor-emb σ α β)
                   (htensor-emb φ α (hpre ψ (hpre θ β))))
  htensor-E₃-contr {x} {x'} φ {y} {y'} ψ {z} {z'} θ .center .fst =
    (φ ⊗ₕ ψ) ⊗ₕ θ
  htensor-E₃-contr {x} {x'} φ {y} {y'} ψ {z} {z'} θ .center .snd =
    htensor-emb-nest φ ψ θ
  htensor-E₃-contr {x} {x'} φ {y} {y'} ψ {z} {z'} θ .paths =
    is-contr→is-prop
      (transport
        (λ i → is-contr
          (Σ λ (σ : C.hom ((x ⊗ y) ⊗ z) ((x' ⊗ y') ⊗ z'))
             → ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
             → Cell σ α β i))
        (htensor-compose-contr (φ ⊗ₕ ψ) θ))
      _
    where
      Cell
        : ∀ (σ : C.hom ((x ⊗ y) ⊗ z) ((x' ⊗ y') ⊗ z'))
            {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
        → ( PathP (λ j → C.hom (tensor-emb-comp-pt (x ⊗ y) z l r j)
                               (tensor-emb-comp-pt (x' ⊗ y') z' l' r' j))
                  (htensor-emb σ α β)
                  (htensor-emb (φ ⊗ₕ ψ) α (hpre θ β)) )
        ≡ ( PathP (λ j → C.hom (tensor-emb-nest x  y  z  l  r  j)
                               (tensor-emb-nest x' y' z' l' r' j))
                  (htensor-emb σ α β)
                  (htensor-emb φ α (hpre ψ (hpre θ β))) )
      Cell σ {l} {l'} α {r} {r'} β i =
        PathP (λ j → C.hom (av i j) (bv i j))
              (htensor-emb σ α β)
              (⊗ₕ-comp-pt φ ψ α (hpre θ β) i)
        where
          av : (i j : _) → C.ob
          av i j =
            cat.fill (tensor-emb-comp-pt (x ⊗ y) z l r)
                     (tensor-emb-comp-pt x y l (pre z r)) j i
          bv : (i j : _) → C.ob
          bv i j =
            cat.fill (tensor-emb-comp-pt (x' ⊗ y') z' l' r')
                     (tensor-emb-comp-pt x' y' l' (pre z' r')) j i
```

`assoc-nat` is the morphism-level image of `⊗-assoc`,
displaced over the associator `PathP`. Both `(φ ⊗ₕ ψ) ⊗ₕ θ`
and `φ ⊗ₕ (ψ ⊗ₕ θ)` inhabit `htensor-E₃-contr φ ψ θ`, but the
fiber index has the fixed type `C.hom ((x⊗y)⊗z) ((x'⊗y')⊗z')`,
so the right-nested cell is transported back along `⊗-assoc` by
`inv-coe-filler`. The object-level fiber path `ofibπ`
reconstructs `⊗-assoc`'s own `is-contr→is-prop` witness; its
`snd` component `ofibπ i .snd` is the object square joining
`tensor-emb-nest` to the right-nested `tensor-emb-comp-pt`/
`tensor-pre-composite` path over `⊗-assoc`, which the `com`
below rides to displace `natChar` onto `tensor-emb-nest`.

```agda
  assoc-nat
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        {z z'} (θ : C.hom z z')
    → PathP (λ i → C.hom (⊗-assoc x y z i) (⊗-assoc x' y' z' i))
            ((φ ⊗ₕ ψ) ⊗ₕ θ)
            (φ ⊗ₕ (ψ ⊗ₕ θ))
  assoc-nat {x} {x'} φ {y} {y'} ψ {z} {z'} θ =
    pcom (sym (ap fst mfibπ)) filler refl
    where
      v : C.hom (x ⊗ (y ⊗ z)) (x' ⊗ (y' ⊗ z'))
      v = φ ⊗ₕ (ψ ⊗ₕ θ)

      filler = inv-coe-filler
        (λ i → C.hom (⊗-assoc x y z i) (⊗-assoc x' y' z' i)) v

      ofibπ = is-contr→is-prop (tensor-E₃-contr x y z)
        (tensor-E₃-contr x y z .center)
        ( (x ⊗ (y ⊗ z))
        , (λ l r → tensor-emb-comp-pt x (y ⊗ z) l r
                   ∙ ap (tensor-emb x l) (tensor-pre-composite y z r)) )

      ofibπ' = is-contr→is-prop (tensor-E₃-contr x' y' z')
        (tensor-E₃-contr x' y' z' .center)
        ( (x' ⊗ (y' ⊗ z'))
        , (λ l r → tensor-emb-comp-pt x' (y' ⊗ z') l r
                   ∙ ap (tensor-emb x' l) (tensor-pre-composite y' z' r)) )

      natChar
        : ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
        → PathP (λ i → C.hom
                  ((tensor-emb-comp-pt x (y ⊗ z) l r
                    ∙ ap (tensor-emb x l) (tensor-pre-composite y z r)) i)
                  ((tensor-emb-comp-pt x' (y' ⊗ z') l' r'
                    ∙ ap (tensor-emb x' l') (tensor-pre-composite y' z' r'))
                   i))
                (htensor-emb v α β)
                (htensor-emb φ α (hpre ψ (hpre θ β)))
      natChar {l} {l'} α {r} {r'} β =
        compHomP
          (tensor-emb-comp-pt x (y ⊗ z) l r)
          (ap (tensor-emb x l) (tensor-pre-composite y z r))
          (tensor-emb-comp-pt x' (y' ⊗ z') l' r')
          (ap (tensor-emb x' l') (tensor-pre-composite y' z' r'))
          (⊗ₕ-comp-pt φ (ψ ⊗ₕ θ) α β)
          (λ i → htensor-emb φ α (hpre-composite ψ θ β i))

      rhsSnd
        : ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
        → PathP (λ i → C.hom (tensor-emb-nest x  y  z  l  r  i)
                             (tensor-emb-nest x' y' z' l' r' i))
                (htensor-emb (filler i0) α β)
                (htensor-emb φ α (hpre ψ (hpre θ β)))
      rhsSnd {l} {l'} α {r} {r'} β i =
        com (λ k → C.hom (ofibπ  (~ k) .snd l  r  i)
                         (ofibπ' (~ k) .snd l' r' i)) (∂ i) λ where
          k (i = i0) → htensor-emb (filler (~ k)) α β
          k (i = i1) → htensor-emb φ α (hpre ψ (hpre θ β))
          k (k = i0) → natChar α β i

      mfibπ = is-contr→is-prop (htensor-E₃-contr φ ψ θ)
        (htensor-E₃-contr φ ψ θ .center)
        (filler i0 , rhsSnd)
```

## Unit absorption naturality

`fiber-map-transport-nat` is the transport-naturality of any
fibrewise map `F : C.hom a b → C.hom (g a)(g b)`: applying `F`
after transporting the source along `(p , q)` equals transporting
the result along `(ap g p , ap g q)`. A double `J` reduces it to
`transport-refl` on both slots.

```agda
  private
    fiber-map-transport-nat
      : ∀ {g : C.ob → C.ob}
          (F : ∀ {a b} → C.hom a b → C.hom (g a) (g b))
          {a n a' n'} (p : a ≡ n) (q : a' ≡ n') (z : C.hom a a')
      → F (transport (λ i → C.hom (p i) (q i)) z)
      ≡ transport (λ i → C.hom (g (p i)) (g (q i))) (F z)
    fiber-map-transport-nat {g} F {a} {n} {a'} {n'} p q z =
      J (λ n p → F (transport (λ i → C.hom (p i) (q i)) z)
               ≡ transport (λ i → C.hom (g (p i)) (g (q i))) (F z))
        (J (λ n' q → F (transport (λ i → C.hom a (q i)) z)
                   ≡ transport (λ i → C.hom (g a) (g (q i))) (F z))
           (ap F (transport-refl z) ∙ sym (transport-refl (F z)))
           q)
        p
```

`habsorb-l` is the morphism-level image of `absorb-l`: the unit
action `hpre (idn) χ` is displaced to `χ` over `absorb-l`. Since
`hpre (idn)` is an equivalence on 2-cells (`htensor-unit .fst`),
`to-pathp` reduces the goal to a homogeneous equation in
`C.hom (pre I m)(pre I m')`, then `equiv→lc` cancels the outer
`hpre (idn)`. The remaining equation glues three links: transport
naturality (`fiber-map-transport-nat`), the rewrite of
`ap (pre I)(absorb-l)` to `pre-I-idem` via `equiv→lc-section`, and
`morphism-pre-idn-idpt`, the PathP transcribing the object
`pre-I-idem` with `hpre-composite` displaced along `⊗ₕ-idem`.

```agda
  habsorb-l
    : ∀ {m m'} (χ : C.hom m m')
    → PathP (λ i → C.hom (absorb-l m i) (absorb-l m' i))
            (hpre (C.idn I) χ) χ
  habsorb-l {m} {m'} χ =
    Path-over.to-pathp (equiv→lc (htensor-unit .fst) F·Gχ≡Fχ)
    where
      nc  = tensor-pre-composite I I m
      nc' = tensor-pre-composite I I m'

      morphism-pre-idn-idpt
        : PathP (λ i → C.hom (pre-I-idem m i) (pre-I-idem m' i))
                (hpre (C.idn I) (hpre (C.idn I) χ))
                (hpre (C.idn I) χ)
      morphism-pre-idn-idpt = sym sub-mor
        where
          tf = transport-filler
                 (ap (λ t → pre t m ≡ pre I (pre I m)) ⊗-idem) nc
          tf' = transport-filler
                  (ap (λ t → pre t m' ≡ pre I (pre I m')) ⊗-idem) nc'

          sub-mor
            : PathP (λ j → C.hom (tf i1 j) (tf' i1 j))
                    (hpre (C.idn I) χ)
                    (hpre (C.idn I) (hpre (C.idn I) χ))
          sub-mor j = com (λ i → C.hom (tf i j) (tf' i j)) (∂ j) λ where
            i (j = i0) → hpre (⊗ₕ-idem i) χ
            i (j = i1) → hpre (C.idn I) (hpre (C.idn I) χ)
            i (i = i0) → hpre-composite (C.idn I) (C.idn I) χ j

      F·Gχ≡Fχ
        : hpre (C.idn I)
            (transport (λ i → C.hom (absorb-l m i) (absorb-l m' i))
              (hpre (C.idn I) χ))
        ≡ hpre (C.idn I) χ
      F·Gχ≡Fχ =
          fiber-map-transport-nat (hpre (C.idn I))
            (absorb-l m) (absorb-l m') (hpre (C.idn I) χ)
        ∙ (λ k → transport
                   (λ i → C.hom
                     (equiv→lc-section tensor-unit-eqvl (pre-I-idem m) k i)
                     (equiv→lc-section tensor-unit-eqvl (pre-I-idem m') k i))
                   (hpre (C.idn I) (hpre (C.idn I) χ)))
        ∙ Path-over.from-pathp morphism-pre-idn-idpt
```

`habsorb-r` is the `post`/`hpost`/`tensor-unit-eqvr`/`post-I-idem`
mirror of `habsorb-l`, displacing `hpost (idn) χ` to `χ` over
`absorb-r`. It transcribes `htensor-post-composite` along the same
`⊗ₕ-idem`.

```agda
  habsorb-r
    : ∀ {l l'} (χ : C.hom l l')
    → PathP (λ i → C.hom (absorb-r l i) (absorb-r l' i))
            (hpost (C.idn I) χ) χ
  habsorb-r {l} {l'} χ =
    Path-over.to-pathp (equiv→lc (htensor-unit .snd) F·Gχ≡Fχ)
    where
      yc  = tensor-post-composite I I l
      yc' = tensor-post-composite I I l'

      morphism-post-idn-idpt
        : PathP (λ i → C.hom (post-I-idem l i) (post-I-idem l' i))
                (hpost (C.idn I) (hpost (C.idn I) χ))
                (hpost (C.idn I) χ)
      morphism-post-idn-idpt = sym sub-mor
        where
          tf = transport-filler
                 (ap (λ t → post t l ≡ post I (post I l)) ⊗-idem) yc
          tf' = transport-filler
                  (ap (λ t → post t l' ≡ post I (post I l')) ⊗-idem) yc'

          sub-mor
            : PathP (λ j → C.hom (tf i1 j) (tf' i1 j))
                    (hpost (C.idn I) χ)
                    (hpost (C.idn I) (hpost (C.idn I) χ))
          sub-mor j = com (λ i → C.hom (tf i j) (tf' i j)) (∂ j) λ where
            i (j = i0) → hpost (⊗ₕ-idem i) χ
            i (j = i1) → hpost (C.idn I) (hpost (C.idn I) χ)
            i (i = i0) → htensor-post-composite (C.idn I) (C.idn I) χ j

      F·Gχ≡Fχ
        : hpost (C.idn I)
            (transport (λ i → C.hom (absorb-r l i) (absorb-r l' i))
              (hpost (C.idn I) χ))
        ≡ hpost (C.idn I) χ
      F·Gχ≡Fχ =
          fiber-map-transport-nat (hpost (C.idn I))
            (absorb-r l) (absorb-r l') (hpost (C.idn I) χ)
        ∙ (λ k → transport
                   (λ i → C.hom
                     (equiv→lc-section tensor-unit-eqvr (post-I-idem l) k i)
                     (equiv→lc-section tensor-unit-eqvr (post-I-idem l') k i))
                   (hpost (C.idn I) (hpost (C.idn I) χ)))
        ∙ Path-over.from-pathp morphism-post-idn-idpt
```

## Post and pre morphism decomposition

`htensor-emb-pre` and `htensor-emb-post` are the morphism-level
images of `tensor-emb-pre` and `tensor-emb-post`. Each glues two
displaced links over the object nest: an absorption whisker in the
untouched slot (`habsorb-r` for pre, `habsorb-l` for post) followed
by `htensor-interchange`. `htensor-emb-pre` supplies the second
inhabitant characterization for `unitl-nat`.

```agda
  htensor-emb-pre
    : ∀ {x x'} (φ : C.hom x x') {l l'} (α : C.hom l l')
        {r r'} (β : C.hom r r')
    → PathP (λ i → C.hom (tensor-emb-pre x  l  r  i)
                         (tensor-emb-pre x' l' r' i))
            (htensor-emb φ α β)
            (htensor-emb (C.idn I) α (hpre φ β))
  htensor-emb-pre {x} {x'} φ {l} {l'} α {r} {r'} β =
    compHomP
      (ap (λ t → tensor-emb x  t r ) (sym (absorb-r l )))
      (sym (tensor-interchange I x  l  r ))
      (ap (λ t → tensor-emb x' t r') (sym (absorb-r l')))
      (sym (tensor-interchange I x' l' r'))
      (λ i → htensor-emb φ (habsorb-r α (~ i)) β)
      (λ i → htensor-interchange (C.idn I) φ α β (~ i))

  htensor-emb-post
    : ∀ {x x'} (φ : C.hom x x') {l l'} (α : C.hom l l')
        {r r'} (β : C.hom r r')
    → PathP (λ i → C.hom (tensor-emb-post x  l  r  i)
                         (tensor-emb-post x' l' r' i))
            (htensor-emb φ α β)
            (htensor-emb (C.idn I) (hpost φ α) β)
  htensor-emb-post {x} {x'} φ {l} {l'} α {r} {r'} β =
    compHomP
      (ap (tensor-emb x  l ) (sym (absorb-l r )))
      (tensor-interchange x  I l  r )
      (ap (tensor-emb x' l') (sym (absorb-l r')))
      (tensor-interchange x' I l' r')
      (λ i → htensor-emb φ α (habsorb-l β (~ i)))
      (htensor-interchange φ (C.idn I) α β)
```

## Right-unit image fiber

`htensor-emb-image-contr` is the morphism-level image of
`tensor-emb-image-contr`, with the fixed fiber index
`σ : C.hom (x ⊗ I)(x' ⊗ I)`. It is built exactly as
`htensor-E₃-contr`: `htensor-compose-contr φ (idn)` is transported
along `Cell`, which appends the `absorb-l` whisker to the object
family (via `cat.fill`) and the `habsorb-l` displacement to the
target endpoint. The center's characterization is the same append,
gluing `⊗ₕ-comp-pt φ (idn)` to `habsorb-l` with `compHomP`. The
fiber object family matches `⊗-unitr`'s `lhs` characterization.

```agda
  htensor-emb-image-contr
    : ∀ {x x'} (φ : C.hom x x')
    → is-contr
        (Σ λ (σ : C.hom (x ⊗ I) (x' ⊗ I))
           → ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
           → PathP (λ i → C.hom
                     (( tensor-emb-comp-pt x  I l  r
                        ∙ ap (tensor-emb x  l ) (absorb-l r ) ) i)
                     (( tensor-emb-comp-pt x' I l' r'
                        ∙ ap (tensor-emb x' l') (absorb-l r') ) i))
                   (htensor-emb σ α β)
                   (htensor-emb φ α β))
  htensor-emb-image-contr {x} {x'} φ .center .fst = φ ⊗ₕ (C.idn I)
  htensor-emb-image-contr {x} {x'} φ .center .snd {l} {l'} α {r} {r'} β =
    compHomP
      (tensor-emb-comp-pt x  I l  r )
      (ap (tensor-emb x  l ) (absorb-l r ))
      (tensor-emb-comp-pt x' I l' r')
      (ap (tensor-emb x' l') (absorb-l r'))
      (⊗ₕ-comp-pt φ (C.idn I) α β)
      (λ i → htensor-emb φ α (habsorb-l β i))
  htensor-emb-image-contr {x} {x'} φ .paths =
    is-contr→is-prop
      (transport
        (λ i → is-contr
          (Σ λ (σ : C.hom (x ⊗ I) (x' ⊗ I))
             → ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
             → Cell σ α β i))
        (htensor-compose-contr φ (C.idn I)))
      _
    where
      Cell
        : ∀ (σ : C.hom (x ⊗ I) (x' ⊗ I))
            {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
        → ( PathP (λ j → C.hom (tensor-emb-comp-pt x  I l  r  j)
                               (tensor-emb-comp-pt x' I l' r' j))
                  (htensor-emb σ α β)
                  (htensor-emb φ α (hpre (C.idn I) β)) )
        ≡ ( PathP (λ j → C.hom
                    (( tensor-emb-comp-pt x  I l  r
                       ∙ ap (tensor-emb x  l ) (absorb-l r ) ) j)
                    (( tensor-emb-comp-pt x' I l' r'
                       ∙ ap (tensor-emb x' l') (absorb-l r') ) j))
                  (htensor-emb σ α β)
                  (htensor-emb φ α β) )
      Cell σ {l} {l'} α {r} {r'} β i =
        PathP (λ j → C.hom (av i j) (bv i j))
              (htensor-emb σ α β)
              (htensor-emb φ α (habsorb-l β i))
        where
          av : (i j : _) → C.ob
          av i j =
            cat.fill (tensor-emb-comp-pt x I l r)
                     (ap (tensor-emb x l) (absorb-l r)) j i
          bv : (i j : _) → C.ob
          bv i j =
            cat.fill (tensor-emb-comp-pt x' I l' r')
                     (ap (tensor-emb x' l') (absorb-l r')) j i
```

## Unitor naturality

`unitr-nat` is the morphism-level image of `⊗-unitr`, displaced
over its object path. It mirrors `assoc-nat`: `φ` is transported
back along `⊗-unitr` by `inv-coe-filler` to land in the fixed fiber
index `C.hom (x ⊗ I)(x' ⊗ I)`, and `mfibπ` identifies the center
`φ ⊗ₕ idn` of `htensor-emb-image-contr φ` with that transported
`filler i0`. Since `⊗-unitr`'s `rhs` characterization is `refl`,
the base of the displacing `com` is `htensor-emb φ α β` itself.

```agda
  unitr-nat
    : ∀ {x x'} (φ : C.hom x x')
    → PathP (λ i → C.hom (⊗-unitr x i) (⊗-unitr x' i))
            (φ ⊗ₕ (C.idn I))
            φ
  unitr-nat {x} {x'} φ =
    pcom (sym (ap fst mfibπ)) filler refl
    where
      filler = inv-coe-filler
        (λ i → C.hom (⊗-unitr x i) (⊗-unitr x' i)) φ

      ofibπ = is-contr→is-prop (tensor-emb-image-contr x)
        ( x ⊗ I
        , (λ l r → tensor-emb-comp-pt x I l r
                   ∙ ap (tensor-emb x l) (absorb-l r)) )
        ( x , (λ _ _ → refl) )

      ofibπ' = is-contr→is-prop (tensor-emb-image-contr x')
        ( x' ⊗ I
        , (λ l r → tensor-emb-comp-pt x' I l r
                   ∙ ap (tensor-emb x' l) (absorb-l r)) )
        ( x' , (λ _ _ → refl) )

      rhsSnd
        : ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
        → PathP (λ i → C.hom
                  (( tensor-emb-comp-pt x  I l  r
                     ∙ ap (tensor-emb x  l ) (absorb-l r ) ) i)
                  (( tensor-emb-comp-pt x' I l' r'
                     ∙ ap (tensor-emb x' l') (absorb-l r') ) i))
                (htensor-emb (filler i0) α β)
                (htensor-emb φ α β)
      rhsSnd {l} {l'} α {r} {r'} β i =
        com (λ k → C.hom (ofibπ  (~ k) .snd l  r  i)
                         (ofibπ' (~ k) .snd l' r' i)) (∂ i) λ where
          k (i = i0) → htensor-emb (filler (~ k)) α β
          k (i = i1) → htensor-emb φ α β
          k (k = i0) → htensor-emb φ α β

      mfibπ = is-contr→is-prop (htensor-emb-image-contr φ)
        (htensor-emb-image-contr φ .center)
        (filler i0 , rhsSnd)
```

`unitl-nat` is the morphism-level image of `⊗-unitl`. It reuses
the `htensor-compose-contr (idn) φ` field directly, whose center
is `idn ⊗ₕ φ`. The base of the displacing `com` is
`htensor-emb-pre φ α β`, the morphism transcription of `⊗-unitl`'s
`rhs = x , tensor-emb-pre x`.

```agda
  unitl-nat
    : ∀ {x x'} (φ : C.hom x x')
    → PathP (λ i → C.hom (⊗-unitl x i) (⊗-unitl x' i))
            ((C.idn I) ⊗ₕ φ)
            φ
  unitl-nat {x} {x'} φ =
    pcom (sym (ap fst mfibπ)) filler refl
    where
      filler = inv-coe-filler
        (λ i → C.hom (⊗-unitl x i) (⊗-unitl x' i)) φ

      ofibπ = is-contr→is-prop (tensor-composable-contr I x)
        ( I ⊗ x , tensor-emb-comp-pt I x )
        ( x , tensor-emb-pre x )

      ofibπ' = is-contr→is-prop (tensor-composable-contr I x')
        ( I ⊗ x' , tensor-emb-comp-pt I x' )
        ( x' , tensor-emb-pre x' )

      rhsSnd
        : ∀ {l l'} (α : C.hom l l') {r r'} (β : C.hom r r')
        → PathP (λ i → C.hom (tensor-emb-comp-pt I x  l  r  i)
                             (tensor-emb-comp-pt I x' l' r' i))
                (htensor-emb (filler i0) α β)
                (htensor-emb (C.idn I) α (hpre φ β))
      rhsSnd {l} {l'} α {r} {r'} β i =
        com (λ k → C.hom (ofibπ  (~ k) .snd l  r  i)
                         (ofibπ' (~ k) .snd l' r' i)) (∂ i) λ where
          k (i = i0) → htensor-emb (filler (~ k)) α β
          k (i = i1) → htensor-emb (C.idn I) α (hpre φ β)
          k (k = i0) → htensor-emb-pre φ α β i

      mfibπ = is-contr→is-prop (htensor-compose-contr (C.idn I) φ)
        (htensor-compose-contr (C.idn I) φ .center)
        (filler i0 , rhsSnd)
```
