Lane Biocini
July 2026

Monoidal categories, presented through representable tensor
embeddings and graded by the dimension of cell the tensor acts
on. `monoidal-axioms₀` is the object level, `monoidal-axioms₁`
the morphism level displayed over it, and `monoidal` the
coalescing bundle — mirroring the `structure`/`axioms`/
`category` spine of `Cat.Type`.

The object level is the `category-axioms` field list under the
dictionary hom ↦ ob, with the anonymous endpoints of the
`Cat.Type` context erased outright: the over-slot is a left
tensorand, the under-slot a right tensorand, and the unit plays
the role of the reflexive identity. `theory₀` is the
token-level transcription of `Cat.Base.theory` under the same
dictionary: every proof there factors through the
`virtual`/`representable` vocabulary, so its terms carry over
by renaming, with the `ov-ctr`/`un-ctr` packagings vanishing
and the congruences into the endpoint pairing erased. The
one-object bicategory is the moral picture only; nothing in
the formalization routes through it.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Monoidal where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base
open import Core.Transport.J using (J; subst)
open import Core.Equiv.Base using (is-equiv; iso→equiv; _≃_; id-equiv)
open import Core.Function.Embedding
  using (image-fibers-contr→is-embedding; equiv→lc)

open import Cat.Type
open import Cat.Base
```

## Level 0: the tensor context calculus

`virtual`, transcribed: the over-slot is a left tensorand, the
under-slot a right tensorand; `ov-idn` and `un-idn` both
collapse to the unit `I`. `⊗₀-res` is constant because the anonymous endpoints
of the arc have been erased.

```agda
module tensor-virtual {o h} (C : category o h) (I : category.ob C) where
  private module C = category C

  ⊗₀-ctx : Type o
  ⊗₀-ctx = C.ob × C.ob

  ⊗₀-emp : C.ob → C.ob → ⊗₀-ctx
  ⊗₀-emp l r = l , r

  ⊗₀-res : ⊗₀-ctx → Type o
  ⊗₀-res _ = C.ob

  ⊗₀-composite : Type o
  ⊗₀-composite = (γ : ⊗₀-ctx) → ⊗₀-res γ

  ⊗₀-ev : ⊗₀-composite → C.ob
  ⊗₀-ev F = F (I , I)
```

## The representable tensor

Token-for-token transcription of `Cat.Type.representable`
under the dictionary hom ↦ ob, idn ↦ I. `⊗₀-emb x (l , r)` is
the two-sided tensor action: the left factor `l`, the cell `x`
in the middle slot, the right factor `r`.

```agda
module tensor-representable {o h} (C : category o h) (I : category.ob C)
  (⊗₀-emb : category.ob C → tensor-virtual.⊗₀-composite C I) where

  open tensor-virtual C I
  private module C = category C

  is-⊗₀-representable : ⊗₀-composite → Type o
  is-⊗₀-representable = fiber ⊗₀-emb

  _⊨₀_ : ⊗₀-composite → C.ob → Type o
  F ⊨₀ s = ⊗₀-emb s ≡ F

  ⊗₀-pre : C.ob → C.ob → C.ob
  ⊗₀-pre y r = ⊗₀-emb y (I , r)

  ⊗₀-post : C.ob → C.ob → C.ob
  ⊗₀-post x l = ⊗₀-emb x (l , I)

  ⊗₀-sub : C.ob → ⊗₀-ctx → ⊗₀-ctx
  ⊗₀-sub y (l , r) = l , ⊗₀-pre y r

  ⊗₀-cosub : C.ob → ⊗₀-ctx → ⊗₀-ctx
  ⊗₀-cosub x (l , r) = ⊗₀-post x l , r

  ⊗₀-nrm : (x : C.ob) → is-⊗₀-representable (⊗₀-emb x)
  ⊗₀-nrm x = x , refl

  _▾₀_ : ⊗₀-composite → C.ob → ⊗₀-composite
  (F ▾₀ y) γ = F (⊗₀-sub y γ)
  infixl 30 _▾₀_

  _▴₀_ : C.ob → ⊗₀-composite → ⊗₀-composite
  (x ▴₀ G) γ = G (⊗₀-cosub x γ)
  infixl 30 _▴₀_

  _▿₀_ : ⊗₀-composite → ⊗₀-composite → ⊗₀-composite
  (F ▿₀ G) γ = F (γ .fst , G (I , γ .snd))
  infixl 30 _▿₀_

  _▵₀_ : ⊗₀-composite → ⊗₀-composite → ⊗₀-composite
  (F ▵₀ G) γ = G (F (γ .fst , I) , γ .snd)
  infixl 30 _▵₀_

  -- closure of the ternary interchange over the fibers of ⊗₀-emb;
  -- at ⊗₀-nrm endpoints it agrees with the input up to J-refl
  ⊗₀-interchange♭-from
    : ((x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y)
    → {A B : ⊗₀-composite}
    → is-⊗₀-representable A → is-⊗₀-representable B
    → A ▿₀ B ≡ A ▵₀ B
  ⊗₀-interchange♭-from ι {B = B} (m , p) (n , q) =
    J (λ F' _ → F' ▿₀ B ≡ F' ▵₀ B)
      (J (λ G' _ → ⊗₀-emb m ▿₀ G' ≡ ⊗₀-emb m ▵₀ G') (ι m n) q)
      p
```

## `monoidal-axioms₀`

The `category-axioms` field list under the dictionary:
`⊗₀-emb`, `⊗₀-interchange♭`, `⊗₀-spine-contr`, `⊗₀-unit`, with
`I` playing the role of `rx`. The record holds fields and bare
spine projections only — every `where`-using lemma lives in
`theory₀` — and the universe is `Type₊ o`: no hom-level data
appears at this level.

```agda
record monoidal-axioms₀ {o h} (C : category o h) : Type₊ o where
  private module C = category C

  field
    I      : C.ob
    ⊗₀-emb : C.ob → tensor-virtual.⊗₀-composite C I

  open tensor-virtual C I public
  open tensor-representable C I ⊗₀-emb public

  field
    ⊗₀-interchange♭
      : {A B : ⊗₀-composite}
      → is-⊗₀-representable A → is-⊗₀-representable B
      → A ▿₀ B ≡ A ▵₀ B

  ⊗₀-interchange : (x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y
  ⊗₀-interchange x y = ⊗₀-interchange♭ (⊗₀-nrm x) (⊗₀-nrm y)

  ⊗₀-spine : C.ob → C.ob → Type o
  ⊗₀-spine x y =
    Σ s ∶ C.ob ,
    Σ p ∶ (⊗₀-emb s ≡ ⊗₀-emb x ▾₀ y) ,
    Σ q ∶ (⊗₀-emb s ≡ x ▴₀ ⊗₀-emb y) ,
      PathP (λ i → ⊗₀-emb s ≡ ⊗₀-interchange x y i) p q

  field
    ⊗₀-spine-contr : (x y : C.ob) → is-contr (⊗₀-spine x y)
    ⊗₀-unit        : (x : C.ob) → ⊗₀-ev (⊗₀-emb x) ≡ x

  _⊗₀_ : C.ob → C.ob → C.ob
  x ⊗₀ y = ⊗₀-spine-contr x y .center .fst
  infixr 40 _⊗₀_

  ⊗₀-emb-comp : (x y : C.ob) → ⊗₀-emb (x ⊗₀ y) ≡ ⊗₀-emb x ▾₀ y
  ⊗₀-emb-comp x y = ⊗₀-spine-contr x y .center .snd .fst

  ⊗₀-emb-comp-op : (x y : C.ob) → ⊗₀-emb (x ⊗₀ y) ≡ x ▴₀ ⊗₀-emb y
  ⊗₀-emb-comp-op x y = ⊗₀-spine-contr x y .center .snd .snd .fst

  -- the spine's 2-cell: the two composite comparisons agree along
  -- the interchange
  ⊗₀-emb-comp-coh
    : (x y : C.ob)
    → PathP (λ i → ⊗₀-emb (x ⊗₀ y) ≡ ⊗₀-interchange x y i)
            (⊗₀-emb-comp x y) (⊗₀-emb-comp-op x y)
  ⊗₀-emb-comp-coh x y = ⊗₀-spine-contr x y .center .snd .snd .snd
```

## `theory₀`

The transcription of `Cat.Base.theory`. The contractible spine
makes `⊗₀-emb` an embedding with propositional fibers, so the
binary tensor is extracted from the spine's center, and
associativity and the unit laws are theorems rather than
axioms.

```agda
module theory₀ {o h} {C : category o h} (M₀ : monoidal-axioms₀ C) where
  open monoidal-axioms₀ M₀
  private module C = category C

  _⋉₀_ : ∀ {F G : ⊗₀-composite}
      → is-⊗₀-representable F → is-⊗₀-representable G
      → is-⊗₀-representable (F ▿₀ G)
  (m , p) ⋉₀ (n , q) = m ⊗₀ n , ⊗₀-emb-comp m n ∙ (λ i → p i ▿₀ q i)
  infixr 40 _⋉₀_

  _⋊₀_ : ∀ {F G : ⊗₀-composite}
        → is-⊗₀-representable F → is-⊗₀-representable G
        → is-⊗₀-representable (F ▵₀ G)
  (m , p) ⋊₀ (n , q) = m ⊗₀ n , ⊗₀-emb-comp-op m n ∙ (λ i → p i ▵₀ q i)

  private
    fwd : ∀ x y → fiber ⊗₀-emb (⊗₀-emb x ▾₀ y) → ⊗₀-spine x y
    fwd x y (k , r) =
      k , r , r ∙ ⊗₀-interchange x y , transpose (cat.fill r (⊗₀-interchange x y))

    bwd : ∀ x y → fiber ⊗₀-emb (x ▴₀ ⊗₀-emb y) → ⊗₀-spine x y
    bwd x y (k , r) =
      k , r ∙ sym ι , r , sym (transpose (cat.fill r (sym ι)))
      where ι = ⊗₀-interchange x y

  -- the pull and push fibers of ⊗₀-emb over the one-sided
  -- composites are contractible by projection from the spine
  ⊗₀-pull-contr : ∀ x y → is-contr (fiber ⊗₀-emb (⊗₀-emb x ▾₀ y))
  ⊗₀-pull-contr x y .center = x ⊗₀ y , ⊗₀-emb-comp x y
  ⊗₀-pull-contr x y .paths u i = φ i .fst , φ i .snd .fst where
    φ : ⊗₀-spine-contr x y .center ≡ fwd x y u
    φ = ⊗₀-spine-contr x y .paths (fwd x y u)

  ⊗₀-push-contr : ∀ x y → is-contr (fiber ⊗₀-emb (x ▴₀ ⊗₀-emb y))
  ⊗₀-push-contr x y .center = x ⊗₀ y , ⊗₀-emb-comp-op x y
  ⊗₀-push-contr x y .paths u i = φ i .fst , φ i .snd .snd .fst where
    φ : ⊗₀-spine-contr x y .center ≡ bwd x y u
    φ = ⊗₀-spine-contr x y .paths (bwd x y u)

  -- a composite witness: k represents the two-sided tensor of x and y
  ⊗₀-cast-path : ∀ {x y k} → (⊗₀-emb x ▾₀ y) ⊨₀ k → x ⊗₀ y ≡ k
  ⊗₀-cast-path {x} {y} {k} α = ap fst (⊗₀-pull-contr x y .paths (k , α))

  ⊗₀-cast-path⁻¹ : ∀ {x y k} → x ⊗₀ y ≡ k → (⊗₀-emb x ▾₀ y) ⊨₀ k
  ⊗₀-cast-path⁻¹ {x} {y} p = ap ⊗₀-emb (sym p) ∙ ⊗₀-emb-comp x y
```

### The unit laws at the identity context

```agda
  ⊗₀-comp-eq-ev : ∀ x y → x ⊗₀ y ≡ ⊗₀-ev (⊗₀-emb x ▾₀ y)
  ⊗₀-comp-eq-ev x y = sym (⊗₀-unit (x ⊗₀ y)) ∙ ap ⊗₀-ev (⊗₀-emb-comp x y)

  ⊗₀-comp-eq-pre : ∀ x y → x ⊗₀ y ≡ ⊗₀-pre x y
  ⊗₀-comp-eq-pre x y = ⊗₀-comp-eq-ev x y ∙ ap (⊗₀-pre x) (⊗₀-unit y)

  ⊗₀-comp-eq-post : ∀ x y → x ⊗₀ y ≡ ⊗₀-post y x
  ⊗₀-comp-eq-post x y =
    sym (⊗₀-unit (x ⊗₀ y)) ∙ ap ⊗₀-ev (⊗₀-emb-comp-op x y)
    ∙ ap (⊗₀-post y) (⊗₀-unit x)

  ⊗₀-idem : I ⊗₀ I ≡ I
  ⊗₀-idem = ⊗₀-comp-eq-pre I I ∙ ⊗₀-unit I

  ⊗₀-pre-is-post : ∀ x y → ⊗₀-pre x y ≡ ⊗₀-post y x
  ⊗₀-pre-is-post x y = sym (⊗₀-comp-eq-pre x y) ∙ ⊗₀-comp-eq-post x y

  -- absorption needs no equivalence hypothesis: it is read off the
  -- spine center and the unit
  ⊗₀-absorb-l : ∀ r → ⊗₀-pre I r ≡ r
  ⊗₀-absorb-l r = ⊗₀-pre-is-post I r ∙ ⊗₀-unit r

  ⊗₀-absorb-r : ∀ l → ⊗₀-post I l ≡ l
  ⊗₀-absorb-r l = sym (⊗₀-pre-is-post l I) ∙ ⊗₀-unit l

  ⊗₀-idn-▴ : ∀ (F : ⊗₀-composite) → I ▴₀ F ≡ F
  ⊗₀-idn-▴ F = funext λ (l , r) → ap (λ t → F (t , r)) (⊗₀-absorb-r l)

  ⊗₀-emb-image-contr : ∀ x → is-contr (fiber ⊗₀-emb (⊗₀-emb x))
  ⊗₀-emb-image-contr x =
    subst (λ F → is-contr (fiber ⊗₀-emb F))
      (⊗₀-idn-▴ (⊗₀-emb x)) (⊗₀-push-contr I x)

  ▾₀-idn : ∀ (F : ⊗₀-composite) → F ▾₀ I ≡ F
  ▾₀-idn F = funext λ (l , r) → ap (λ t → F (l , t)) (⊗₀-absorb-l r)

  ⊗₀-emb-idn-absorb : ∀ x → ⊗₀-emb I ▾₀ x ≡ ⊗₀-emb x
  ⊗₀-emb-idn-absorb x = ⊗₀-interchange I x ∙ ⊗₀-idn-▴ (⊗₀-emb x)
```

### Post and pre decomposition

```agda
  ⊗₀-emb-post : ∀ x l r → ⊗₀-emb x (l , r) ≡ ⊗₀-emb I (⊗₀-post x l , r)
  ⊗₀-emb-post x l r =
    ap (λ t → ⊗₀-emb x (l , t)) (sym (⊗₀-absorb-l r))
    ∙ happly (⊗₀-interchange x I) (l , r)

  ⊗₀-emb-pre : ∀ x l r → ⊗₀-emb x (l , r) ≡ ⊗₀-emb I (l , ⊗₀-pre x r)
  ⊗₀-emb-pre x l r =
    ap (λ t → ⊗₀-emb x (t , r)) (sym (⊗₀-absorb-r l))
    ∙ sym (happly (⊗₀-interchange I x) (l , r))

  -- the fully post-normal form of a tensor image
  ⊗₀-emb-normal : ∀ x l r → ⊗₀-emb x (l , r) ≡ ⊗₀-post r (⊗₀-post x l)
  ⊗₀-emb-normal x l r =
    ⊗₀-emb-post x l r
    ∙ ap (λ t → ⊗₀-emb I (⊗₀-post x l , t)) (sym (⊗₀-unit r))
    ∙ happly (⊗₀-interchange I r) (⊗₀-post x l , I)
    ∙ ap (λ t → ⊗₀-emb r (t , I)) (⊗₀-absorb-r (⊗₀-post x l))

  ⊗₀-pre-distr : ∀ x y r → ⊗₀-pre (x ⊗₀ y) r ≡ ⊗₀-pre x (⊗₀-pre y r)
  ⊗₀-pre-distr x y r = happly (⊗₀-emb-comp x y) (I , r)

  ⊗₀-post-distr : ∀ x y l → ⊗₀-post (x ⊗₀ y) l ≡ ⊗₀-post y (⊗₀-post x l)
  ⊗₀-post-distr x y l = happly (⊗₀-emb-comp-op x y) (l , I)
```

### The representability calculus

```agda
  is-⊗₀-representable-prop : ∀ F → is-prop (is-⊗₀-representable F)
  is-⊗₀-representable-prop =
    image-fibers-contr→is-embedding ⊗₀-emb-image-contr

  ⊗₀-rep-contr : ∀ {F} → is-⊗₀-representable F → is-contr (is-⊗₀-representable F)
  ⊗₀-rep-contr {F} u .center = u
  ⊗₀-rep-contr {F} u .paths = is-⊗₀-representable-prop F u

  ⊗₀-repr-unique : ∀ {F} (u v : is-⊗₀-representable F) → u .fst ≡ v .fst
  ⊗₀-repr-unique {F} u v = ap fst (is-⊗₀-representable-prop F u v)

  ⊗₀-repr-lc : ∀ {F} {U V : is-⊗₀-representable F}
            → (κ : U ≡ V) → ap fst κ ≡ ⊗₀-repr-unique U V
  ⊗₀-repr-lc {F} {U} {V} κ =
    ap (ap fst) (is-contr→is-set (⊗₀-rep-contr U) U V κ
      (is-⊗₀-representable-prop F U V))

  ⊗₀-repr-refl : ∀ {F} {m : C.ob} (p q : ⊗₀-emb m ≡ F)
              → p ≡ q → ⊗₀-repr-unique (m , p) (m , q) ≡ refl
  ⊗₀-repr-refl {F} {m} p q =
    J (λ q' _ → ⊗₀-repr-unique (m , p) (m , q') ≡ refl)
      (sym (⊗₀-repr-lc (refl {x = m , p})))

  ⊗₀-repr-cast : ∀ {F} {m : C.ob} {p q : ⊗₀-emb m ≡ F}
              → (V : is-⊗₀-representable F) → p ≡ q
              → ⊗₀-repr-unique (m , p) V ≡ ⊗₀-repr-unique (m , q) V
  ⊗₀-repr-cast {m = m} V e i = ⊗₀-repr-unique (m , e i) V

  ⊗₀-repr-ap : ∀ {F G} (Ĝ : is-⊗₀-representable F → is-⊗₀-representable G)
              (U V : is-⊗₀-representable F)
            → ⊗₀-repr-unique (Ĝ U) (Ĝ V)
            ≡ ap (λ u → Ĝ u .fst) (is-⊗₀-representable-prop F U V)
  ⊗₀-repr-ap Ĝ U V =
    sym (⊗₀-repr-lc (λ i → Ĝ (is-⊗₀-representable-prop _ U V i)))

  ⊗₀-repr-∙ : ∀ {F} (U V W : is-⊗₀-representable F)
           → ⊗₀-repr-unique U V ∙ ⊗₀-repr-unique V W ≡ ⊗₀-repr-unique U W
  ⊗₀-repr-∙ {F} U V W =
      sym (ap-comp fst (is-⊗₀-representable-prop F U V)
            (is-⊗₀-representable-prop F V W))
    ∙ ⊗₀-repr-lc
        (is-⊗₀-representable-prop F U V ∙ is-⊗₀-representable-prop F V W)

  _↝_ : ∀ {F G : ⊗₀-composite}
      → is-⊗₀-representable F → F ≡ G → is-⊗₀-representable G
  (m , p) ↝ e = m , p ∙ e

  ↝-repr : ∀ {F G} (U V : is-⊗₀-representable F) (e : F ≡ G)
         → ⊗₀-repr-unique (U ↝ e) (V ↝ e) ≡ ⊗₀-repr-unique U V
  ↝-repr (m , p) (n , q) =
    J (λ _ e' → ⊗₀-repr-unique ((m , p) ↝ e') ((n , q) ↝ e')
              ≡ ⊗₀-repr-unique (m , p) (n , q))
      (λ i → ⊗₀-repr-unique (m , Path.unitr p i) (n , Path.unitr q i))

  ap-⊗₀-emb-lc : ∀ {m n : C.ob} {r s : m ≡ n}
              → ap ⊗₀-emb r ≡ ap ⊗₀-emb s → r ≡ s
  ap-⊗₀-emb-lc {n = n} {r} {s} h =
    total-contr-unique (⊗₀-emb-image-contr n) r s (sq r)
      (subst (λ t → PathP (λ i → ⊗₀-emb (s i) ≡ ⊗₀-emb n) t refl)
        (sym h) (sq s))
    where
      sq : (t : _ ≡ n)
        → PathP (λ i → ⊗₀-emb (t i) ≡ ⊗₀-emb n) (ap ⊗₀-emb t) refl
      sq t i j = ⊗₀-emb (t (i ∨ j))

  ⊗₀-coh→∙ : ∀ x y → ⊗₀-emb-comp x y ∙ ⊗₀-interchange x y ≡ ⊗₀-emb-comp-op x y
  ⊗₀-coh→∙ x y =
      Path.commutes
        (⊗₀-emb-comp x y) (⊗₀-interchange x y) refl (⊗₀-emb-comp-op x y)
        (⊗₀-emb-comp-coh x y)
    ∙ Path.unitl (⊗₀-emb-comp-op x y)

  ▾₀-comp : ∀ (F : ⊗₀-composite) y z → F ▾₀ (y ⊗₀ z) ≡ (F ▾₀ y) ▾₀ z
  ▾₀-comp F y z = ap (F ▿₀_) (⊗₀-emb-comp y z)
```

### Associativity and the unit laws

Associativity is recovered through the strictness of composite
composition: the two bracketings of a threefold composite of
representations inhabit the one propositional representability
fiber.

```agda
  assoc-σ⋉₀ : ∀ {F G H : ⊗₀-composite}
           → (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
             (W : is-⊗₀-representable H)
           → U ⋉₀ (V ⋉₀ W) ≡ (U ⋉₀ V) ⋉₀ W
  assoc-σ⋉₀ U V W = is-⊗₀-representable-prop _ (U ⋉₀ (V ⋉₀ W)) ((U ⋉₀ V) ⋉₀ W)

  assoc⋉₀ : ∀ {F G H : ⊗₀-composite}
         → (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
           (W : is-⊗₀-representable H)
         → fst (U ⋉₀ (V ⋉₀ W)) ≡ fst ((U ⋉₀ V) ⋉₀ W)
  assoc⋉₀ U V W = ap fst (assoc-σ⋉₀ U V W)

  ⊗₀-assoc : ∀ x y z → x ⊗₀ (y ⊗₀ z) ≡ (x ⊗₀ y) ⊗₀ z
  ⊗₀-assoc x y z = assoc⋉₀ (⊗₀-nrm x) (⊗₀-nrm y) (⊗₀-nrm z)

  ⊗₀-unitr : ∀ x → x ⊗₀ I ≡ x
  ⊗₀-unitr x =
    ⊗₀-repr-unique ((⊗₀-nrm x ⋉₀ ⊗₀-nrm I) ↝ ▾₀-idn (⊗₀-emb x)) (⊗₀-nrm x)

  ⊗₀-unitl : ∀ x → I ⊗₀ x ≡ x
  ⊗₀-unitl x =
    ⊗₀-repr-unique ((⊗₀-nrm I ⋉₀ ⊗₀-nrm x) ↝ ⊗₀-emb-idn-absorb x) (⊗₀-nrm x)
```

### Unit uniqueness and the demoted equivalences

Any object whose middle-slot action at itself is an equivalence
and which is idempotent under `⊗₀-post` is uniquely the chosen
unit `I`. The argument is the Kraus chain: `⊗₀-post e` squares
to itself and is idempotent, so it absorbs, forcing `e ≡ I`.
The unit equivalences of the curried presentation are not
axioms: they are recovered from absorption.

```agda
  ⊗₀-unit-is-prop
    : (e : C.ob)
    → is-equiv (λ l → ⊗₀-emb e (l , e))
    → ⊗₀-post e e ≡ e
    → e ≡ I
  ⊗₀-unit-is-prop e re idpt =
    sym (⊗₀-unit e) ∙ post-e-absorb I
    where
      e-idem : e ⊗₀ e ≡ e
      e-idem = ⊗₀-comp-eq-post e e ∙ idpt

      post-e-idpt : ∀ l → ⊗₀-post e (⊗₀-post e l) ≡ ⊗₀-post e l
      post-e-idpt l =
        sym (⊗₀-post-distr e e l) ∙ ap (λ t → ⊗₀-post t l) e-idem

      post-e-absorb : ∀ l → ⊗₀-post e l ≡ l
      post-e-absorb l = equiv→lc re
        (⊗₀-emb-normal e (⊗₀-post e l) e
        ∙ post-e-idpt (⊗₀-post e l)
        ∙ sym (⊗₀-emb-normal e l e))

  ⊗₀-unit-eqvl : is-equiv (λ (r : C.ob) → ⊗₀-pre I r)
  ⊗₀-unit-eqvl =
    subst is-equiv (funext λ r → sym (⊗₀-absorb-l r)) id-equiv

  ⊗₀-unit-eqvr : is-equiv (λ (l : C.ob) → ⊗₀-post I l)
  ⊗₀-unit-eqvr =
    subst is-equiv (funext λ l → sym (⊗₀-absorb-r l)) id-equiv

  ⊗₀-ob≃total-representable
    : C.ob ≃ (Σ F ∶ ⊗₀-composite , is-⊗₀-representable F)
  ⊗₀-ob≃total-representable = iso→equiv to fro ob-ret rep-sec
    where
      to : C.ob → Σ F ∶ ⊗₀-composite , is-⊗₀-representable F
      to x = ⊗₀-emb x , ⊗₀-nrm x

      fro : (Σ F ∶ ⊗₀-composite , is-⊗₀-representable F) → C.ob
      fro (_ , a , _) = a

      ob-ret : ∀ x → fro (to x) ≡ x
      ob-ret x = refl

      rep-sec : ∀ s → to (fro s) ≡ s
      rep-sec (_ , a , p) = J (λ F' p' → to a ≡ (F' , a , p')) refl p
```

## 2-coherence

The coherence law identifying the two middle-unit absorptions of
a two-step composite. It is path-degree-2 data *about* level-0
structure, so it lives in an extension record over
`monoidal-axioms₀` rather than in either axiom level — the same
choice `Cat.Coherence` makes with `is-2-coherent` and
`category-axioms`.

```agda
record monoidal-2-coherent {o h} {C : category o h}
  (M₀ : monoidal-axioms₀ C) : Type o where
  open monoidal-axioms₀ M₀
  open theory₀ M₀
  private module C = category C

  field
    is-⊗₀-2-coherent
      : (x y : C.ob)
      → ap (_▿₀ ⊗₀-emb y) (▾₀-idn (⊗₀-emb x))
      ≡ ap (⊗₀-emb x ▿₀_) (⊗₀-emb-idn-absorb y)
```

## Level 1: the displayed context calculus

A morphism of tensor contexts is a left-flank map paired with a
right-flank map; a `⊗₁-composite` is a family of homs over all
such maps, displayed over a pair of object-composites. The 2-cell
boundary `(x , x')` fills the middle slots of the two frame
images inside the result type — the flanks themselves carry no
boundary. Frame-maps compose slotwise: the context category.

The frames are quantified *visibly*, as `Cat.Type` keeps the
anonymous endpoints inside the context: a hidden-Π-headed
composite type would have its inhabitants eta-expanded with
frame metas wherever they meet an inference-mode position (bare
`_≡_`, `fiber`, a Σ-bound operator variable), while a visible Π
is never expanded. `_$₁_` recovers application with the frames
read off the context argument's type.

```agda
module tensor-virtual₁ {o h} (C : category o h) (I : category.ob C) where
  private module C = category C
  private module Ct = theory C
  open tensor-virtual C I

  ⊗₁-ctx : ⊗₀-ctx → ⊗₀-ctx → Type h
  ⊗₁-ctx (l , r) (l' , r') = C.hom l l' × C.hom r r'

  ⊗₁-ov-idn : C.hom I I
  ⊗₁-ov-idn = C.idn I

  ⊗₁-un-idn : C.hom I I
  ⊗₁-un-idn = C.idn I

  ⊗₁-composite : ⊗₀-composite → ⊗₀-composite → Type (o ⊔ h)
  ⊗₁-composite F F' = ∀ γ γ' → ⊗₁-ctx γ γ' → C.hom (F γ) (F' γ')

  -- application, with the frames read off the context's type
  _$₁_ : ∀ {F F'} → ⊗₁-composite F F'
       → ∀ {γ γ'} → ⊗₁-ctx γ γ' → C.hom (F γ) (F' γ')
  _$₁_ η {γ} {γ'} δ = η γ γ' δ
  infixl 90 _$₁_

  -- evaluation at the identity context
  ⊗₁-ev : ∀ {F F'} → ⊗₁-composite F F' → C.hom (⊗₀-ev F) (⊗₀-ev F')
  ⊗₁-ev η = η $₁ (⊗₁-ov-idn , ⊗₁-un-idn)

  _⊗₁-ctx-⨾_ : ∀ {γ γ' γ''}
             → ⊗₁-ctx γ γ' → ⊗₁-ctx γ' γ'' → ⊗₁-ctx γ γ''
  (α , β) ⊗₁-ctx-⨾ (α' , β') = (α Ct.⨾ α') , (β Ct.⨾ β')
  infixr 40 _⊗₁-ctx-⨾_

  -- the context category's identity, at any frame
  ⊗₁-ctx-idn : ∀ {γ} → ⊗₁-ctx γ γ
  ⊗₁-ctx-idn {γ = (l , r)} = (C.idn l , C.idn r)
```

## The displayed representable layer

The representability predicate with its satisfaction relation
and normal form, the unit-slot actions `⊗₁-pre`/`⊗₁-post` and
the context substitutions `⊗₁-sub`/`⊗₁-cosub`, mirroring the
object layer; the two one-sided composite operators `▾₁`/`▴₁`,
the two ternary orders `▿₁`/`▵₁`, and the vertical composite
`_⨾₁_`.

```agda
module tensor-representable₁ {o h} (C : category o h) (I : category.ob C)
  (⊗₀-emb : category.ob C → tensor-virtual.⊗₀-composite C I)
  (⊗₁-emb : ∀ {x x'} → category.hom C x x'
          → tensor-virtual₁.⊗₁-composite C I (⊗₀-emb x) (⊗₀-emb x'))
  where

  open tensor-virtual C I
  open tensor-virtual₁ C I
  open tensor-representable C I ⊗₀-emb
  private module C = category C
  private module Ct = theory C

  is-⊗₁-representable
    : ∀ {x x'} → ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x') → Type (o ⊔ h)
  is-⊗₁-representable = fiber ⊗₁-emb

  _⊨₁_ : ∀ {x x'} → ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x')
       → C.hom x x' → Type (o ⊔ h)
  η ⊨₁ σ = ⊗₁-emb σ ≡ η

  ⊗₁-pre : ∀ {y y'} → C.hom y y' → ∀ {r r'} → C.hom r r'
        → C.hom (⊗₀-pre y r) (⊗₀-pre y' r')
  ⊗₁-pre ψ β = ⊗₁-emb ψ $₁ (⊗₁-ov-idn , β)

  ⊗₁-post : ∀ {x x'} → C.hom x x' → ∀ {l l'} → C.hom l l'
        → C.hom (⊗₀-post x l) (⊗₀-post x' l')
  ⊗₁-post φ α = ⊗₁-emb φ $₁ (α , ⊗₁-un-idn)

  ⊗₁-sub : ∀ {y y'} (ψ : C.hom y y') {γ γ'}
        → ⊗₁-ctx γ γ' → ⊗₁-ctx (⊗₀-sub y γ) (⊗₀-sub y' γ')
  ⊗₁-sub ψ (α , β) = α , ⊗₁-pre ψ β

  ⊗₁-cosub : ∀ {x x'} (φ : C.hom x x') {γ γ'}
          → ⊗₁-ctx γ γ' → ⊗₁-ctx (⊗₀-cosub x γ) (⊗₀-cosub x' γ')
  ⊗₁-cosub φ (α , β) = ⊗₁-post φ α , β

  ⊗₁-nrm : ∀ {x x'} (φ : C.hom x x') → is-⊗₁-representable (⊗₁-emb φ)
  ⊗₁-nrm φ = φ , refl

  _▾₁_ : ∀ {F F' : ⊗₀-composite} {y y'}
       → ⊗₁-composite F F' → C.hom y y'
       → ⊗₁-composite (F ▾₀ y) (F' ▾₀ y')
  (η ▾₁ ψ) γ γ' δ = η $₁ ⊗₁-sub ψ δ
  infixl 30 _▾₁_

  _▴₁_ : ∀ {x x'} {G G' : ⊗₀-composite}
         → C.hom x x' → ⊗₁-composite G G'
         → ⊗₁-composite (x ▴₀ G) (x' ▴₀ G')
  (φ ▴₁ η) γ γ' δ = η $₁ ⊗₁-cosub φ δ
  infixl 30 _▴₁_

  _▿₁_ : ∀ {F F' G G' : ⊗₀-composite}
        → ⊗₁-composite F F' → ⊗₁-composite G G'
        → ⊗₁-composite (F ▿₀ G) (F' ▿₀ G')
  (η ▿₁ ζ) γ γ' (α , β) = η $₁ (α , ζ $₁ (⊗₁-ov-idn , β))
  infixl 30 _▿₁_

  _▵₁_ : ∀ {F F' G G' : ⊗₀-composite}
         → ⊗₁-composite F F' → ⊗₁-composite G G'
         → ⊗₁-composite (F ▵₀ G) (F' ▵₀ G')
  (η ▵₁ ζ) γ γ' (α , β) = ζ $₁ (η $₁ (α , ⊗₁-un-idn) , β)
  infixl 30 _▵₁_

  -- vertical composite of hom-composites, with the second factor
  -- read at the identity frame: the normal form ⊗₁-emb-⨾ produces
  -- at δ ⊗₁-ctx-⨾ ⊗₁-ctx-idn and ⊗₁-pre-comp consumes
  _⨾₁_ : ∀ {F F' F''} → ⊗₁-composite F F' → ⊗₁-composite F' F''
       → ⊗₁-composite F F''
  (η ⨾₁ η') γ γ' δ = η $₁ δ Ct.⨾ η' $₁ ⊗₁-ctx-idn
  infixr 40 _⨾₁_
```

## `monoidal-axioms₁`

The displayed copy of the axiom shape, over a chosen
`monoidal-axioms₀`: `⊗₁-emb`, `⊗₁-interchange`, `⊗₁-spine-contr`,
`⊗₁-unit`, plus the one field with no object-level shadow — the
enrichment law `⊗₁-emb-⨾`, preserving the whole composition of
the context category. The characterizations are single `PathP`s
between morphism-composites, displaced over the object operator
paths.

```agda
record monoidal-axioms₁ {o h} {C : category o h}
  (M₀ : monoidal-axioms₀ C) : Type₊ (o ⊔ h) where
  open monoidal-axioms₀ M₀
  open tensor-virtual₁ C I public
  private module C = category C
  private module Ct = theory C

  field
    ⊗₁-emb : ∀ {x x'} → C.hom x x' → ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x')

  open tensor-representable₁ C I ⊗₀-emb ⊗₁-emb public

  field
    ⊗₁-interchange
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
      → PathP (λ i → ⊗₁-composite (⊗₀-interchange x y i)
                                   (⊗₀-interchange x' y' i))
              (⊗₁-emb φ ▾₁ ψ)
              (φ ▴₁ ⊗₁-emb ψ)

  ⊗₁-spine : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
          → Type (o ⊔ h)
  ⊗₁-spine {x} {x'} φ {y} {y'} ψ =
    Σ σ ∶ C.hom (x ⊗₀ y) (x' ⊗₀ y') ,
    Σ P ∶ PathP (λ i → ⊗₁-composite (⊗₀-emb-comp x y i)
                                     (⊗₀-emb-comp x' y' i))
                (⊗₁-emb σ) (⊗₁-emb φ ▾₁ ψ) ,
    Σ Q ∶ PathP (λ i → ⊗₁-composite (⊗₀-emb-comp-op x y i)
                                     (⊗₀-emb-comp-op x' y' i))
                (⊗₁-emb σ) (φ ▴₁ ⊗₁-emb ψ) ,
      PathP (λ i → PathP (λ j → ⊗₁-composite (⊗₀-emb-comp-coh x  y  i j)
                                              (⊗₀-emb-comp-coh x' y' i j))
                         (⊗₁-emb σ) (⊗₁-interchange φ ψ i))
            P Q

  field
    ⊗₁-spine-contr
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
      → is-contr (⊗₁-spine φ ψ)

    ⊗₁-unit
      : ∀ {x x'} (φ : C.hom x x')
      → PathP (λ i → C.hom (⊗₀-unit x i) (⊗₀-unit x' i))
              (⊗₁-ev (⊗₁-emb φ)) φ

    ⊗₁-emb-⨾
      : ∀ {x x' x''} (φ₁ : C.hom x x') (φ₂ : C.hom x' x'')
          {γ γ' γ''} (δ₁ : ⊗₁-ctx γ γ') (δ₂ : ⊗₁-ctx γ' γ'')
      → ⊗₁-emb (φ₁ Ct.⨾ φ₂) $₁ (δ₁ ⊗₁-ctx-⨾ δ₂)
      ≡ ⊗₁-emb φ₁ $₁ δ₁ Ct.⨾ ⊗₁-emb φ₂ $₁ δ₂

  _⊗₁_ : ∀ {x x'} → C.hom x x' → ∀ {y y'} → C.hom y y'
       → C.hom (x ⊗₀ y) (x' ⊗₀ y')
  φ ⊗₁ ψ = ⊗₁-spine-contr φ ψ .center .fst
  infixr 40 _⊗₁_

  ⊗₁-emb-comp : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
              → PathP (λ i → ⊗₁-composite (⊗₀-emb-comp x y i)
                                           (⊗₀-emb-comp x' y' i))
                      (⊗₁-emb (φ ⊗₁ ψ)) (⊗₁-emb φ ▾₁ ψ)
  ⊗₁-emb-comp φ ψ = ⊗₁-spine-contr φ ψ .center .snd .fst

  ⊗₁-emb-comp-op : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
                 → PathP (λ i → ⊗₁-composite (⊗₀-emb-comp-op x y i)
                                              (⊗₀-emb-comp-op x' y' i))
                         (⊗₁-emb (φ ⊗₁ ψ)) (φ ▴₁ ⊗₁-emb ψ)
  ⊗₁-emb-comp-op φ ψ = ⊗₁-spine-contr φ ψ .center .snd .snd .fst

  -- the spine's 2-cell
  ⊗₁-emb-comp-coh
    : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
    → PathP (λ i → PathP (λ j → ⊗₁-composite (⊗₀-emb-comp-coh x  y  i j)
                                              (⊗₀-emb-comp-coh x' y' i j))
                         (⊗₁-emb (φ ⊗₁ ψ)) (⊗₁-interchange φ ψ i))
            (⊗₁-emb-comp φ ψ) (⊗₁-emb-comp-op φ ψ)
  ⊗₁-emb-comp-coh φ ψ = ⊗₁-spine-contr φ ψ .center .snd .snd .snd
```

## The bundle

Mirroring `category = structure + axioms`.

```agda
record monoidal {o h} (C : category o h) : Type₊ (o ⊔ h) where
  field
    axioms₀ : monoidal-axioms₀ C
    axioms₁ : monoidal-axioms₁ axioms₀

  open monoidal-axioms₀ axioms₀ public
  open monoidal-axioms₁ axioms₁ public
  open theory₀ axioms₀ public
```
