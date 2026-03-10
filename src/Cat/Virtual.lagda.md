Lane Biocini
March 2026

Categories via ternary composition with interchange. The basic data
is a ternary sandwich embedding `emb f w g z h` representing the
composite `g . f . h`. Two binary compositions arise from
specializing the two outer slots to `idn`:

    yon f w g  =  emb f w g y idn    -- covariant face
    noy f z h  =  emb f x idn z h   -- contravariant face

These yield two a priori distinct compositions — `⨾₁` feeds `g`'s
contravariant face into `f`'s right slot, while `⨾₂` feeds `f`'s
covariant face into `g`'s left slot. Each has one free unit law and
free associativity. The interchange axiom equates them, supplying
the missing unit laws.

The embedding property of `emb` is derived, not assumed:
`composable-contr idn f` gives a contractible fiber over the
composite target, and interchange + absorption collapses that
target to `emb f`, making `fiber emb (emb f)` contractible for
every `f`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Virtual where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport
open import Core.Function.Base

record category o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    emb : ∀ {x y} → hom x y
        → ∀ w → hom w x → ∀ z → hom y z → hom w z
    idn-contr
      : ∀ {x}
      → is-contr
          (Σ e ∶ hom x x
          , (∀ {w} (g : hom w x) → emb e w g x e ≡ g)
          × (∀ {z} (h : hom x z) → emb e x e z h ≡ h))

  idn : ∀ {x} → hom x x
  idn = idn-contr .center .fst

  field
    composable-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr
          (fiber (emb {x} {z})
            (λ w a v b →
              emb f w a v (emb g _ idn v b)))
    interchange
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        w (a : hom w x) v (b : hom z v)
      → emb f w a v (emb g _ idn v b)
      ≡ emb g w (emb f w a _ idn) v b

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = composable-contr f g .center .fst
  infixr 40 _⨾_

  {-# INLINE emb #-}
  {-# INLINE _⨾_ #-}
```

## Derived operations

```agda
module Cat {o} {h} (C : category o h) where
  open category C public

  absorb-r
    : ∀ {x} {w : ob} (g : hom w x)
    → emb idn w g x idn ≡ g
  absorb-r = idn-contr .center .snd .fst

  absorb-l
    : ∀ {x} {z : ob} (h : hom x z)
    → emb idn x idn z h ≡ h
  absorb-l = idn-contr .center .snd .snd

  yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
  yon f w g = emb f w g _ idn

  noy : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  noy f z h = emb f _ idn z h
```

### Embedding property

`composable-contr idn f` gives `is-contr (fiber emb target)` where
`target w a v b = emb idn w a v (noy f v b)`. By interchange,
this equals `emb f w (yon idn w a) v b = emb f w a v b` via
right absorption. So `fiber emb (emb f)` is contractible for
every `f`, making `emb` an embedding.

```agda
  emb-image-contr
    : ∀ {x y} (f : hom x y)
    → is-contr (fiber emb (emb f))
  emb-image-contr f =
    subst (is-contr ∘ fiber emb) path (composable-contr idn f)
    where
      path
        : (λ w a v b → emb idn w a v (noy f v b))
        ≡ emb f
      path = funext λ w → funext λ a → funext λ v →
        funext λ b →
          interchange idn f w a v b
          ∙ ap (λ t → emb f w t v b) (absorb-r a)

  composable-yon
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-contr
        (fiber emb
          (λ w a v b → emb g w (yon f w a) v b))
  composable-yon f g =
    subst (is-contr ∘ fiber emb) path (composable-contr f g)
    where
      path
        : (λ w a v b → emb f w a v (noy g v b))
        ≡ (λ w a v b → emb g w (yon f w a) v b)
      path = funext λ w → funext λ a → funext λ v →
        funext λ b → interchange f g w a v b

  composable-swap
    : ∀ {x y}
      {target : ∀ w → hom w x → ∀ v → hom y v → hom w v}
    → is-contr (fiber emb target)
    → is-contr
        (fiber {B = ∀ w → hom y w → ∀ v → hom v x → hom v w}
          (λ s w a v b → emb s v b w a)
          (λ w a v b → target v b w a))
  composable-swap c .center .fst = c .center .fst
  composable-swap c .center .snd i w a v b =
    c .center .snd i v b w a
  composable-swap {target = target} c .paths (s' , q') i .fst =
    c .paths (s' , q'') i .fst
    where
      q'' : emb s' ≡ target
      q'' i w a v b = q' i v b w a
  composable-swap {target = target} c .paths (s' , q') i .snd j w a v b =
    c .paths (s' , q'') i .snd j v b w a
    where
      q'' : emb s' ≡ target
      q'' i w a v b = q' i v b w a
```

### Composite equations

```agda
  emb-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g) ≡ (λ w a v b → emb f w a v (noy g v b))
  emb-composite f g = composable-contr f g .center .snd

  emb-composite-pt
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x) v (b : hom z v)
    → emb (f ⨾ g) w a v b ≡ emb f w a v (noy g v b)
  emb-composite-pt f g w a v b i =
    emb-composite f g i w a v b

  emb-yon-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g)
    ≡ (λ w a v b → emb g w (yon f w a) v b)
  emb-yon-composite f g =
    emb-composite f g
    ∙ funext λ w → funext λ a → funext λ v →
      funext λ b → interchange f g w a v b
```

### Induction principles

Each contractible fiber yields an induction principle via
`contr-ind`: to prove something about all inhabitants of the
fiber, it suffices to prove it for the canonical center.

The identity is the unique endomorphism absorbing from both
sides. `idn-ind` eliminates any `(e, r, l)` satisfying the
absorption laws back to the canonical triple
`(idn, absorb-r, absorb-l)`.

```agda
  private
    idn-fiber : ∀ {x} → Type _
    idn-fiber {x} = Σ e ∶ hom x x ,
        (∀ {w} (g : hom w x) → emb e w g x e ≡ g)
      × (∀ {z} (h : hom x z) → emb e x e z h ≡ h)

  idn-ind
    : ∀ {u} {x}
    → (P : (e : hom x x)
         → (∀ {w} (g : hom w x) → emb e w g x e ≡ g)
         → (∀ {z} (h : hom x z) → emb e x e z h ≡ h)
         → Type u)
    → P idn absorb-r absorb-l
    → (a : idn-fiber) → P (a .fst) (a .snd .fst) (a .snd .snd)
  idn-ind P base a =
    coe01 (λ i → P (p i .fst) (p i .snd .fst) (p i .snd .snd)) base
    where p = idn-contr .paths a

  idn-unique
    : ∀ {x} (e : hom x x)
    → (∀ {w} (g : hom w x) → emb e w g x e ≡ g)
    → (∀ {z} (h : hom x z) → emb e x e z h ≡ h)
    → idn ≡ e
  idn-unique e r l = idn-ind (λ e _ _ → idn ≡ e) refl (e , r , l)
```

Composition is the unique morphism whose embedding equals the
composite target. `emb-ind` eliminates any `(s, q)` in the
composable fiber back to `(f ⨾ g, emb-composite f g)`.

```agda
  emb-ind
    : ∀ {u} {x y z} (f : hom x y) (g : hom y z)
    → (P : (s : hom x z)
         → emb s
           ≡ (λ w a v b → emb f w a v (noy g v b))
         → Type u)
    → P (f ⨾ g) (emb-composite f g)
    → ∀ s q → P s q
  emb-ind f g P base s q =
    contr-ind (composable-contr f g)
      (λ where (s , q) → P s q)
      base (s , q)

  ⨾-η
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → (s : hom x z)
    → emb s
      ≡ (λ w a v b → emb f w a v (noy g v b))
    → f ⨾ g ≡ s
  ⨾-η f g = emb-ind f g (λ s _ → f ⨾ g ≡ s) refl
```

The embedding is faithful: `emb n ≡ emb m` implies `n ≡ m`.
`emb-image-ind` eliminates any `(n, q)` in the image fiber back
to `(m, refl)`.

```agda
  emb-image-ind
    : ∀ {u} {x y} (m : hom x y)
    → (P : (n : hom x y) → emb n ≡ emb m → Type u)
    → P m refl
    → ∀ n q → P n q
  emb-image-ind m P base n q =
    coe01 (λ i → P (path i .fst) (path i .snd)) base
    where
      path : (m , refl) ≡ (n , q)
      path = sym (emb-image-contr m .paths (m , refl))
           ∙ emb-image-contr m .paths (n , q)

  emb-inj
    : ∀ {x y} {f g : hom x y}
    → emb f ≡ emb g → f ≡ g
  emb-inj {f = f} {g} p =
    emb-image-ind f (λ n _ → f ≡ n) refl g (sym p)
```

The yon-characterized composite: interchange swaps `noy` for `yon`
in the composite target, giving a dual fiber with the same center.
`emb-yon-ind` eliminates over this alternative characterization.

```agda
  emb-yon-ind
    : ∀ {u} {x y z} (f : hom x y) (g : hom y z)
    → (P : (s : hom x z)
         → emb s
           ≡ (λ w a v b → emb g w (yon f w a) v b)
         → Type u)
    → P (f ⨾ g) (emb-yon-composite f g)
    → ∀ s q → P s q
  emb-yon-ind f g P base s q =
    coe01 (λ i → P (path i .fst) (path i .snd)) base
    where
      path : (f ⨾ g , emb-yon-composite f g) ≡ (s , q)
      path = sym (composable-yon f g .paths _)
           ∙ composable-yon f g .paths (s , q)
```

### Distribution and decomposition

`noy` and `yon` distribute over composition. `noy-composite`
follows from the composite equation at `a = idn`;
`yon-composite` uses the composite equation and interchange.
Both `yon` and `noy` are injective, following from interchange
and `emb-inj`. The `emb-yon` and `emb-noy` lemmas express
`emb f` in terms of `yon` and `noy`.

```agda
  noy-composite
    : ∀ {x y z} (g : hom x y) (h : hom y z)
      {v : ob} (b : hom z v)
    → noy (g ⨾ h) v b ≡ noy g v (noy h v b)
  noy-composite g h {v} b i =
    emb-composite g h i _ idn v b

  yon-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x)
    → yon (f ⨾ g) w a ≡ yon g w (yon f w a)
  yon-composite f g w a =
    emb-composite-pt f g w a _ idn
    ∙ interchange f g w a _ idn

  yon-inj
    : ∀ {x y} {f g : hom x y}
    → yon f ≡ yon g → f ≡ g
  yon-inj {f = f} {g} p = emb-inj
    (funext λ w → funext λ a → funext λ v → funext λ b →
      ap (emb f w a v) (sym (absorb-l b))
      ∙ interchange f idn w a v b
      ∙ ap (λ t → emb idn w t v b) (λ i → p i w a)
      ∙ sym (interchange g idn w a v b)
      ∙ ap (emb g w a v) (absorb-l b))

  noy-inj
    : ∀ {x y} {f g : hom x y}
    → noy f ≡ noy g → f ≡ g
  noy-inj {f = f} {g} p = emb-inj
    (funext λ w → funext λ a → funext λ v → funext λ b →
      ap (λ t → emb f w t v b) (sym (absorb-r a))
      ∙ sym (interchange idn f w a v b)
      ∙ ap (λ t → emb idn w a v t) (λ i → p i v b)
      ∙ interchange idn g w a v b
      ∙ ap (λ t → emb g w t v b) (absorb-r a))

  emb-yon
    : ∀ {x y} (f : hom x y) w (a : hom w x) v (b : hom y v)
    → emb f w a v b ≡ emb idn w (yon f w a) v b
  emb-yon f w a v b =
    ap (emb f w a v) (sym (absorb-l b))
    ∙ interchange f idn w a v b

  emb-noy
    : ∀ {x y} (f : hom x y) w (a : hom w x) v (b : hom y v)
    → emb f w a v b ≡ emb idn w a v (noy f v b)
  emb-noy f w a v b =
    ap (λ t → emb f w t v b) (sym (absorb-r a))
    ∙ sym (interchange idn f w a v b)
```

### Coherent unit laws and associativity

The unit laws and associativity are defined as projections from
contractible fibers rather than via `emb-inj` / `⨾-η`. Each
law is `ap fst` of the unique path between two points in a
contractible fiber of `emb`. This gives control over the
emb-image at every intermediate point along the path, which is
needed for pentagon and triangle coherences.

```agda
  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn ≡ f
  unitr f =
    ap fst (is-contr→is-prop (emb-image-contr f) lhs rhs)
    where
      lhs : fiber emb (emb f)
      lhs = f ⨾ idn
          , emb-composite f idn
          ∙ funext λ w → funext λ a → funext λ v →
            funext λ b →
              ap (emb f w a v) (absorb-l b)

      rhs : fiber emb (emb f)
      rhs = f , refl

  unitl : ∀ {x y} (f : hom x y) → idn ⨾ f ≡ f
  unitl f =
    ap fst (is-contr→is-prop (emb-image-contr f) lhs rhs)
    where
      lhs : fiber emb (emb f)
      lhs = idn ⨾ f
          , emb-composite idn f
          ∙ sym (funext λ w → funext λ a → funext λ v →
              funext λ b → emb-noy f w a v b)

      rhs : fiber emb (emb f)
      rhs = f , refl

  private
    E₃ : ∀ {x y z w} (f : hom x y) (g : hom y z)
        (h : hom z w)
      → ∀ w' → hom w' x → ∀ v → hom w v → hom w' v
    E₃ f g h =
      λ w a v b → emb f w a v (noy g v (noy h v b))

  E₃-contr
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → is-contr (fiber emb (E₃ f g h))
  E₃-contr f g h =
    subst (is-contr ∘ fiber emb) path
      (composable-contr (f ⨾ g) h)
    where
      path
        : (λ w a v b →
            emb (f ⨾ g) w a v (noy h v b))
        ≡ E₃ f g h
      path = funext λ w → funext λ a →
        funext λ v → funext λ b →
          emb-composite-pt f g w a v (noy h v b)

  assoc
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h =
    ap fst (is-contr→is-prop (E₃-contr f g h) lhs rhs)
    where
      lhs : fiber emb (E₃ f g h)
      lhs = (f ⨾ g) ⨾ h
          , emb-composite (f ⨾ g) h
          ∙ funext λ w → funext λ a → funext λ v →
            funext λ b →
              emb-composite-pt f g w a v (noy h v b)

      rhs : fiber emb (E₃ f g h)
      rhs = f ⨾ (g ⨾ h)
          , emb-composite f (g ⨾ h)
          ∙ funext λ w → funext λ a → funext λ v →
            funext λ b →
              ap (emb f w a v) (noy-composite g h b)
```

## Opposite category

The opposite category swaps morphism direction. For the ternary
embedding, `op.emb f w a v b = C.emb f v b w a` — the two
(object, morphism) pairs are exchanged.

The identity is the same `C.idn`, with the two absorption
conditions swapped. For composition, `op`'s composable fiber at
`(f, g)` corresponds to C's composable fiber at `(g, f)` after
applying interchange and swapping the four bound variables.

```agda
module _ {o h} (C : category o h) where
  private module C = Cat C

  op : category o h
  op .category.ob = C.ob
  op .category.hom x y = C.hom y x
  op .category.emb f w a v b = C.emb f v b w a
  op .category.idn-contr .center =
    C.idn , C.absorb-l , C.absorb-r
  op .category.idn-contr .paths (e' , l' , r') i =
    let q = C.idn-contr .paths (e' , r' , l') i
    in q .fst , q .snd .snd , q .snd .fst
  op .category.composable-contr {x} {y} {z} f g =
    C.composable-swap {x = z} {y = x} (C.composable-yon g f)
  op .category.interchange f g w a v b =
    sym (C.interchange g f v b w a)
```

### Opposite involution

`op (op C) .idn-contr` and `C.idn-contr` agree definitionally on both
`.center` and `.paths` — the double swap on `(absorb-r, absorb-l)` in
`.center` cancels, and the double swap of argument order in `.paths`
cancels. This lets us define the `idn-contr` path by constant
copatterns, keeping `idn` definitionally constant along the path and
making all downstream fields (`composable-contr`, `interchange`)
straightforward.

```agda
module _ {o h} (C : category o h) where
  private module C = Cat C

  -- The double swap on idn-contr is definitionally the identity:
  -- op swaps (absorb-r, absorb-l) in .center, and swaps
  -- argument order in .paths. Doing this twice cancels out.
  -- We define ic by constant copatterns rather than is-prop→PathP
  -- so that ic i .center .fst = C.idn definitionally for all i.
  private
    ic : ∀ {x}
      → category.idn-contr (op (op C)) {x}
      ≡ C.idn-contr {x}
    ic i .center = C.idn-contr .center
    ic i .paths = C.idn-contr .paths

  op-invol : op (op C) ≡ C
  op-invol i .category.ob = C.ob
  op-invol i .category.hom = C.hom
  op-invol i .category.emb = C.emb
  op-invol i .category.idn-contr {x} = ic {x} i
  op-invol i .category.composable-contr
    {x} {y} {z} f g =
    is-prop→PathP
      {A = λ _ → is-contr
        (fiber (C.emb {x} {z})
          (λ w a v b →
            C.emb f w a v
              (C.emb g _ C.idn v b)))}
      (λ _ → is-contr-is-prop _)
      (category.composable-contr (op (op C)) f g)
      (C.composable-contr f g) i
  op-invol i .category.interchange f g w a v b =
    C.interchange f g w a v b
```

## Ternary functors

A functor between ternary categories preserves the embedding
operation. The primitive field `emb-natural` says that `hmap`
commutes with the ternary embedding: applying `hmap` to each
argument of `D.emb` equals applying `hmap` to the result of
`C.emb`.

```agda
module _
  {o h o' h'}
  (C : category o h)
  (D : category o' h')
  where
  private
    module C = Cat C
    module D = Cat D

  record functor : Type (o ⊔ h ⊔ o' ⊔ h') where
    no-eta-equality

    field
      map  : C.ob → D.ob
      hmap : ∀ {x y}
        → C.hom x y → D.hom (map x) (map y)
      emb-natural
        : ∀ {x y} (f : C.hom x y)
          w (a : C.hom w x) v (b : C.hom y v)
        → D.emb (hmap f) (map w) (hmap a)
            (map v) (hmap b)
        ≡ hmap (C.emb f w a v b)

  {-# INLINE functor.constructor #-}
```

Derived naturality conditions arise from specializing the outer
slots of `emb-natural`. Since `C.yon f w a = C.emb f w a _ C.idn`
and `C.noy f v b = C.emb f _ C.idn v b` hold definitionally, the
right-hand sides simplify directly.

```agda
  module Functor (F : functor) where
    open functor F public

    yon-natural-F
      : ∀ {x y} (f : C.hom x y)
        w (a : C.hom w x)
      → D.emb (hmap f) (map w) (hmap a)
          (map y) (hmap C.idn)
      ≡ hmap (C.yon f w a)
    yon-natural-F f w a =
      emb-natural f w a _ C.idn

    noy-natural-F
      : ∀ {x y} (f : C.hom x y)
        v (b : C.hom y v)
      → D.emb (hmap f) (map x) (hmap C.idn)
          (map v) (hmap b)
      ≡ hmap (C.noy f v b)
    noy-natural-F f v b =
      emb-natural f _ C.idn v b

    absorb-r-F
      : ∀ {x} {w : C.ob} (a : C.hom w x)
      → D.emb (hmap C.idn) (map w) (hmap a)
          (map x) (hmap C.idn)
      ≡ hmap a
    absorb-r-F a =
      emb-natural C.idn _ a _ C.idn
      ∙ ap hmap (C.absorb-r a)

    absorb-l-F
      : ∀ {x} {v : C.ob} (b : C.hom x v)
      → D.emb (hmap C.idn) (map x) (hmap C.idn)
          (map v) (hmap b)
      ≡ hmap b
    absorb-l-F b =
      emb-natural C.idn _ C.idn _ b
      ∙ ap hmap (C.absorb-l b)
```

### Identity functor

Both `map` and `hmap` are the identity, so `emb-natural` holds by
`refl` — the two sides are definitionally equal.

```agda
idn-functor
  : ∀ {o h} (C : category o h)
  → functor C C
idn-functor C .functor.map  = id
idn-functor C .functor.hmap = id
idn-functor C .functor.emb-natural _ _ _ _ _ = refl
```

### Functor composition

The `emb-natural` proof for `G ∘F F` applies `G.emb-natural` to
reduce the outer embedding in `E`, then `ap G.hmap` of
`F.emb-natural` to reduce the inner one.

```agda
module _
  {o h o' h' o'' h''}
  {C : category o h}
  {D : category o' h'}
  {E : category o'' h''}
  (F : functor C D)
  (G : functor D E)
  where
  private
    module F = Functor C D F
    module G = Functor D E G

  _∘F_ : functor C E
  _∘F_ .functor.map  = G.map ∘ F.map
  _∘F_ .functor.hmap = G.hmap ∘ F.hmap
  _∘F_ .functor.emb-natural f w a v b =
    G.emb-natural (F.hmap f)
      (F.map w) (F.hmap a) (F.map v) (F.hmap b)
    ∙ ap G.hmap (F.emb-natural f w a v b)
```
