Graded monad on `LiftM` via the `(Nat, max, 0)` monoid.

Following Katsumata (2014) on parametric effect monads: a graded monad
over `(Nat, max, 0)` tracks h-level bounds through monadic composition.

This module uses `--cubical` (not `--erased-cubical`) because the monad
laws construct paths between `LiftM` values via Glue types, which
require full cubical for computational univalence.

The unit has grade 0 and Kleisli extension at grades `n`, `m` produces
grade `max n m`, reflecting that the conjunction of definedness
predicates at levels `n` and `m` lives at level `max n m`.

```agda
{-# OPTIONS --safe --cubical --no-guardedness --no-sized-types #-}

module Core.Function.Partial.Graded where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat using (Nat; Z; S)
open import Core.Data.Nat.Base using (max; _≤_)
import Core.Data.Nat.Properties as Nat
open import Core.HLevel
  using ( is-hlevel; Σ-is-hlevel; is-hlevel-≤
        ; is-hlevel-is-prop; nType )
open import Core.Function.Partial
  using (LiftM; LiftM-map; is-defined; value; definedness-trunc; η; ⊥ₗ)

open nType
open import Core.Equiv using (_≃_; iso→equiv; aut; equiv-path; is-equiv)
open import Core.Glue using (Glue; unglue)
open import Core.Kan using (hcom; _∙_; hfil)
open import Core.Transport
  using (is-prop→PathP; is-prop→SquareP; subst)
open import Core.Equiv using (_∙e_; ∙e-unitl)
open import Core.Univalence using (ua; ua-∙e; ua-equiv)

private variable
  u v w x : Level
  n m k l : Nat
  A B C : Type v
```


## Type former

A graded partial element bundles a grade with a `LiftM` value.

```agda
LiftG : (u : Level) → Type v → Type (u ₊ ⊔ v)
LiftG u A = Σ n ∶ Nat , LiftM u A n
```


## PathP for LiftM

Build a `PathP` between `LiftM` values at different grades by Glue/unglue.
Given an equivalence `e` between the definedness types and a coherence
proof relating the value functions through `e`, the construction glues
the definedness types along `e` and corrects the value boundary via
`hcomp`. When the coherence is `refl` (definitional equality), the
`hcomp` reduces away. (These techniques derive from Escardo's Lifting.*
modules on TypeTopology)

```agda
LiftM-pathp
  : ∀ {u v} {X : Type v} {n m : Nat}
  → (p : n ≡ m)
  → (l : LiftM u X n) (r : LiftM u X m)
  → (e : ∣ is-defined l ∣ ≃ ∣ is-defined r ∣)
  → (∀ d → value l d ≡ value r (e .fst d))
  → PathP (λ i → LiftM u X (p i)) l r
LiftM-pathp {u} {X = X} {n} {m} p l r e coh = path where
  D = ∣ is-defined r ∣

  Te : (i : I) → Partial (∂ i) (Σ T ∶ Type _ , T ≃ D)
  Te i (i = i0) = ∣ is-defined l ∣ , e
  Te i (i = i1) = D , aut

  path : PathP (λ i → LiftM u X (p i)) l r
  path i .is-defined .∣_∣ = Glue D (Te i)
  path i .is-defined .is-tr =
    is-prop→PathP
      (λ i → is-hlevel-is-prop {A = Glue D (Te i)} (p i))
      (definedness-trunc l)
      (definedness-trunc r)
      i
  path i .value d = hcom (∂ i) λ where
    j (i = i0) → coh d (~ j)
    j (i = i1) → value r d
    j (j = i0) → value r (unglue (∂ i) {Te = Te i} d)
```

Two `LiftM-pathp` calls with the same underlying function and coherence
are equal when the base Nat paths are equal. The two equivalences share
a common forward map and may differ only in their `is-equiv` proofs;
since `is-equiv` is propositional, `equiv-path` connects them. The
proof builds a dependent square in `LiftM u X (sq i j)` field-by-field:
Glue types vary continuously via `equiv-path`, the h-level field is
automatic by `is-prop→SquareP`, and the value `hcom` has the same
system at both `i`-boundaries because both equivalences share the
same forward function.

```agda
LiftM-pathp-ext
  : ∀ {u v} {X : Type v} {n m : Nat}
  → {p q : n ≡ m} (sq : p ≡ q)
  → (l : LiftM u X n) (r : LiftM u X m)
  → {f : ∣ is-defined l ∣ → ∣ is-defined r ∣}
  → (e₁ e₂ : is-equiv f)
  → (coh : ∀ d → value l d ≡ value r (f d))
  → PathP (λ i → PathP (λ j → LiftM u X (sq i j)) l r)
      (LiftM-pathp p l r (f , e₁) coh)
      (LiftM-pathp q l r (f , e₂) coh)
LiftM-pathp-ext {u} {X = X} {n} {m} {p} {q} sq l r {f} e₁ e₂ coh =
  ext
  where
  D = ∣ is-defined r ∣
  ep : (f , e₁) ≡ (f , e₂)
  ep = equiv-path (f , e₁) (f , e₂) refl

  Te-sq : (i j : I) → Partial (∂ j) (Σ T ∶ Type _ , T ≃ D)
  Te-sq i j (j = i0) = ∣ is-defined l ∣ , ep i
  Te-sq i j (j = i1) = D , aut

  ext : PathP (λ i → PathP (λ j → LiftM u X (sq i j)) l r)
    (LiftM-pathp p l r (f , e₁) coh)
    (LiftM-pathp q l r (f , e₂) coh)
  ext i j .is-defined .∣_∣ = Glue D (Te-sq i j)
  ext i j .is-defined .is-tr =
    is-prop→SquareP
      (λ i j → is-hlevel-is-prop {A = Glue D (Te-sq i j)} (sq i j))
      (λ j → LiftM-pathp p l r (f , e₁) coh j .is-defined .is-tr)
      (λ _ → definedness-trunc l)
      (λ j → LiftM-pathp q l r (f , e₂) coh j .is-defined .is-tr)
      (λ _ → definedness-trunc r)
      i j
  ext i j .value d = hcom (∂ j) λ where
    k (j = i0) → coh d (~ k)
    k (j = i1) → value r d
    k (k = i0) → value r (unglue (∂ j) {Te = Te-sq i j} d)
```


## Graded unit

The graded unit pins at grade `Z`. It is `η` specialized to the
identity grade of `(Nat, max, 0)`.

```agda
ηᵍ : A → LiftM u A Z
ηᵍ = η
```


## Graded Kleisli extension

Given `f : A → LiftM u B m`, extend over `a : LiftM u A n` to get a
result at grade `max n m`. Definedness of the composite requires both
`a` and `f (value a p)` to be defined. The h-level of the product
definedness type is bounded by `max n m` since each factor is bounded
by one of `n` or `m`.

```agda
_♯ᵍ
  : (A → LiftM u B m) → LiftM u A n → LiftM u B (max n m)
_♯ᵍ {m = m} {n = n} f a .is-defined .∣_∣ =
  Σ p ∶ ∣ is-defined a ∣ , ∣ is-defined (f (value a p)) ∣
_♯ᵍ {m = m} {n = n} f a .is-defined .is-tr =
  Σ-is-hlevel (max n m)
    (is-hlevel-≤ (Nat.max.≤l n m) (definedness-trunc a))
    (λ p → is-hlevel-≤ (Nat.max.≤r n m)
      (definedness-trunc (f (value a p))))
_♯ᵍ {m = m} {n = n} f a .value (p , d) =
  value (f (value a p)) d
```


## Graded join

Flatten a nested lifting by extending the identity.

```agda
μᵍ : LiftM u (LiftM u A m) n → LiftM u A (max n m)
μᵍ = _♯ᵍ id
```


## Monad laws

The left unit law has a definitional grade equality (`max Z m`
reduces to `m`), so its result type is a homogeneous path. The
right unit law and associativity require `PathP` over
`Nat.max.unitr` and `Nat.max.assoc` respectively, since
`max n Z` and `max (max n m) k` do not reduce for variable `n`.

Each law uses `LiftM-pathp` with an equivalence between the
definedness types. The value functions agree definitionally in
every case, so the coherence argument is always `lambda _ -> refl`.

### Left unit

Extending `f` over a fully-defined `ηᵍ a` yields `f a`. The
definedness type contracts from `Σ (Lift ⊤) (λ _ → D)` to `D`.

```agda
♯ᵍ-unitl
  : ∀ {u v w} {A : Type v} {B : Type w} {m : Nat}
  → (f : A → LiftM u B m) (a : A)
  → _♯ᵍ f (ηᵍ a) ≡ f a
♯ᵍ-unitl {u} {m = m} f a =
  LiftM-pathp refl (_♯ᵍ f (ηᵍ a)) (f a) e (λ _ → refl)
  where
  e : (Σ p ∶ Lift u ⊤ , ∣ is-defined (f a) ∣)
    ≃ ∣ is-defined (f a) ∣
  e = iso→equiv
    (λ (_ , d) → d) (λ d → liftℓ tt , d)
    (λ _ → refl) (λ _ → refl)
```

### Right unit

Extending `η` over `a` yields `a` back. The definedness type contracts
from `Σ D (λ _ → Lift ⊤)` to `D`.

```agda
♯ᵍ-unitr
  : ∀ {u v} {A : Type v} {n : Nat}
  → (a : LiftM u A n)
  → PathP (λ i → LiftM u A (Nat.max.unitr {n = n} i))
      (_♯ᵍ {m = Z} η a) a
♯ᵍ-unitr {u} {n = n} a =
  LiftM-pathp Nat.max.unitr (_♯ᵍ {m = Z} η a) a e (λ _ → refl)
  where
  e : (Σ p ∶ ∣ is-defined a ∣ , Lift u ⊤)
    ≃ ∣ is-defined a ∣
  e = iso→equiv
    (λ (p , _) → p) (λ p → p , liftℓ tt)
    (λ _ → refl) (λ _ → refl)
```

### Associativity

Composing extensions `♯ᵍ g ∘ ♯ᵍ f` is the same as extending with
the composite `λ x → ♯ᵍ g (f x)`. The grades re-associate via
`Nat.max.assoc`, so this is a `PathP`. The definedness types
re-associate from left-nested to right-nested Σ.

```agda
♯ᵍ-assoc
  : ∀ {u v w x} {A : Type v} {B : Type w} {C : Type x}
    {n m k : Nat}
  → (a : LiftM u A n)
    (f : A → LiftM u B m)
    (g : B → LiftM u C k)
  → PathP (λ i → LiftM u C (Nat.max.assoc n m k i))
      (_♯ᵍ g (_♯ᵍ f a))
      (_♯ᵍ (λ x → _♯ᵍ g (f x)) a)
♯ᵍ-assoc {u} {n = n} {m} {k} a f g =
  LiftM-pathp (Nat.max.assoc n m k)
    (_♯ᵍ g (_♯ᵍ f a))
    (_♯ᵍ (λ x → _♯ᵍ g (f x)) a)
    e (λ _ → refl)
  where
  Da = ∣ is-defined a ∣
  Df : Da → Type u
  Df p = ∣ is-defined (f (value a p)) ∣
  Dg : (p : Da) → Df p → Type u
  Dg p d = ∣ is-defined (g (value (f (value a p)) d)) ∣

  e : (Σ q ∶ (Σ p ∶ Da , Df p) , Dg (q .fst) (q .snd))
    ≃ (Σ p ∶ Da , Σ d ∶ Df p , Dg p d)
  e = iso→equiv
    (λ ((p , d) , gd) → p , d , gd)
    (λ (p , d , gd) → (p , d) , gd)
    (λ _ → refl) (λ _ → refl)
```


## LiftG operations

`LiftG u A = Σ n , LiftM u A n` bundles a grade with a partial
element. The following operations package the graded `LiftM`
operations with their grade witnesses as Sigma pairs.

The continuation `f` in `_♯G` has a fixed grade `m` — this is the
standard graded monad formulation where the grade tracks h-level
bounds through composition.

```agda
embedG : LiftM u A m → LiftG u A
embedG {m = m} la = m , la

ηG : A → LiftG u A
ηG = embedG ∘ ηᵍ

_♯G
  : (A → LiftM u B m) → LiftG u A → LiftG u B
_♯G f (n , la) = max n _ , _♯ᵍ f la

mapG : (A → B) → LiftG u A → LiftG u B
mapG f (n , la) = n , LiftM-map f la
```


## LiftG monad laws

Each law is a Σ-path pairing the Nat component path (grade
reassociation) with the `LiftM` `PathP` (definedness-type
reassociation).

### Left unit

`_♯G f (ηG a) ≡ embedG (f a)` holds because `max Z m` reduces
definitionally to `m`, so the Nat component is `refl` and the
`LiftM` component is `♯ᵍ-unitl`.

```agda
♯G-unitl
  : ∀ {u v w} {A : Type v} {B : Type w} {m : Nat}
  → (f : A → LiftM u B m) (a : A)
  → _♯G f (ηG a) ≡ embedG (f a)
♯G-unitl f a i = _ , ♯ᵍ-unitl f a i
```

### Right unit

The Nat component is `Nat.max.unitr` and the `LiftM` component
is `♯ᵍ-unitr`.

```agda
♯G-unitr
  : ∀ {u v} {A : Type v}
  → (ga : LiftG u A) → _♯G ηᵍ ga ≡ ga
♯G-unitr (n , la) i =
  Nat.max.unitr {n = n} i , ♯ᵍ-unitr la i
```

### Associativity

The Nat component is `Nat.max.assoc` and the `LiftM` component
is `♯ᵍ-assoc`.

```agda
♯G-assoc
  : ∀ {u v w x} {A : Type v} {B : Type w} {C : Type x}
    {m k : Nat}
  → (ga : LiftG u A)
    (f : A → LiftM u B m)
    (g : B → LiftM u C k)
  → _♯G g (_♯G f ga) ≡ _♯G (λ x → _♯ᵍ g (f x)) ga
♯G-assoc (n , la) f g i =
  Nat.max.assoc n _ _ i , ♯ᵍ-assoc la f g i
```

### Pentagon coherence

The two ways of fully reassociating a four-fold Kleisli composition
produce the same `PathP`. This is the Mac Lane pentagon for the graded
monad. The proof is straightforward because both routes perform the
same reassociation of nested Σ-types, and the underlying value
functions agree definitionally.

The grade path is `max-assoc4`, the composition of two `max.assoc`
steps.

```agda
max-assoc4
  : ∀ n m k l
  → max (max (max n m) k) l ≡ max n (max m (max k l))
max-assoc4 n m k l =
  Nat.max.assoc (max n m) k l ∙ Nat.max.assoc n m (max k l)
```

The direct 4-fold reassociation PathP between the fully left-associated
and fully right-associated compositions. The definedness types
reassociate from `Σ (Σ (Σ Da Df) Dg) Dh` to `Σ Da (Σ Df (Σ Dg Dh))`,
and the value functions are definitionally equal on both sides.

```agda
♯ᵍ-assoc4
  : ∀ {u v w x y} {A : Type v} {B : Type w} {C : Type x}
      {D : Type y} {n m k l : Nat}
  → (a : LiftM u A n)
    (f : A → LiftM u B m)
    (g : B → LiftM u C k)
    (h : C → LiftM u D l)
  → PathP (λ i → LiftM u D (max-assoc4 n m k l i))
      (_♯ᵍ h (_♯ᵍ g (_♯ᵍ f a)))
      (_♯ᵍ (λ x → _♯ᵍ (λ y → _♯ᵍ h (g y)) (f x)) a)
♯ᵍ-assoc4 {u} {n = n} {m} {k} {l} a f g h =
  LiftM-pathp (max-assoc4 n m k l)
    (_♯ᵍ h (_♯ᵍ g (_♯ᵍ f a)))
    (_♯ᵍ (λ x → _♯ᵍ (λ y → _♯ᵍ h (g y)) (f x)) a)
    e (λ _ → refl)
  where
  Da = ∣ is-defined a ∣
  Df : Da → Type u
  Df p = ∣ is-defined (f (value a p)) ∣
  Dg : (p : Da) → Df p → Type u
  Dg p d = ∣ is-defined (g (value (f (value a p)) d)) ∣
  Dh : (p : Da) (d : Df p) (gd : Dg p d) → Type u
  Dh p d gd =
    ∣ is-defined (h (value (g (value (f (value a p)) d)) gd)) ∣

  e : (Σ q ∶ (Σ r ∶ (Σ p ∶ Da , Df p) , Dg (r .fst) (r .snd))
      , Dh (q .fst .fst) (q .fst .snd) (q .snd))
    ≃ (Σ p ∶ Da , Σ d ∶ Df p , Σ gd ∶ Dg p d , Dh p d gd)
  e = iso→equiv
    (λ (((p , d) , gd) , hd) → p , d , gd , hd)
    (λ (p , d , gd , hd) → ((p , d) , gd) , hd)
    (λ _ → refl) (λ _ → refl)
```

The pentagon states that the two factorizations of the 4-fold
Sigma reassociation yield the same `LiftM` path. Instead of
composing `LiftG` paths with `_∙_` (which produces opaque `com`
terms), we compose the underlying definedness-type equivalences
with `_∙e_`. Both routes beta-reduce to the same forward function
`(((p,d),gd),hd) -> (p,d,gd,hd)`, so `equiv-path` gives
equivalence equality, and `ap` on `LiftM-pathp` lifts this to
`LiftM` path equality.

The five vertices in `LiftG u D` arise from the four-fold Kleisli
composition with all possible parenthesizations. The five edges
are the individual `♯ᵍ-assoc` steps, each packaged as a `LiftG`
path.

```agda
module pentagon
  {u v' w' x' y'} {A' : Type v'} {B' : Type w'}
  {C' : Type x'} {D' : Type y'}
  {n' m' k' l' : Nat}
  (a : LiftM u A' n')
  (f : A' → LiftM u B' m')
  (g : B' → LiftM u C' k')
  (h : C' → LiftM u D' l')
  where

  private
    Da = ∣ is-defined a ∣
    Df : Da → Type u
    Df p = ∣ is-defined (f (value a p)) ∣
    Dg : (p : Da) → Df p → Type u
    Dg p d = ∣ is-defined (g (value (f (value a p)) d)) ∣
    Dh : (p : Da) (d : Df p) (gd : Dg p d) → Type u
    Dh p d gd =
      ∣ is-defined (h (value (g (value (f (value a p)) d)) gd)) ∣
```

The five vertices, labeled by their parenthesization. Grade
components are determined by `max` associativity.

```agda
  v1 v2 v3 v4 v5 : LiftG u D'

  v1 = max (max (max n' m') k') l'
     , _♯ᵍ h (_♯ᵍ g (_♯ᵍ f a))

  v2 = max (max n' (max m' k')) l'
     , _♯ᵍ h (_♯ᵍ (λ x → _♯ᵍ g (f x)) a)

  v3 = max (max n' m') (max k' l')
     , _♯ᵍ (λ y → _♯ᵍ h (g y)) (_♯ᵍ f a)

  v4 = max n' (max m' (max k' l'))
     , _♯ᵍ (λ x → _♯ᵍ (λ y → _♯ᵍ h (g y)) (f x)) a

  v5 = max n' (max (max m' k') l')
     , _♯ᵍ (λ x → _♯ᵍ h (_♯ᵍ g (f x))) a
```

Each edge is a `LiftG` path built from the corresponding
`♯ᵍ-assoc` step. The Nat component is the `max` associativity
path and the `LiftM` component is the `♯ᵍ-assoc` `PathP`.

```agda
  e13 : v1 ≡ v3
  e13 i = Nat.max.assoc (max n' m') k' l' i
        , ♯ᵍ-assoc (_♯ᵍ f a) g h i

  e34 : v3 ≡ v4
  e34 i = Nat.max.assoc n' m' (max k' l') i
        , ♯ᵍ-assoc a f (λ y → _♯ᵍ h (g y)) i

  e12 : v1 ≡ v2
  e12 i = max (Nat.max.assoc n' m' k' i) l'
        , _♯ᵍ h (♯ᵍ-assoc a f g i)

  e25 : v2 ≡ v5
  e25 i = Nat.max.assoc n' (max m' k') l' i
        , ♯ᵍ-assoc a (λ x → _♯ᵍ g (f x)) h i

  e54 : v5 ≡ v4
  e54 i = max n' (Nat.max.assoc m' k' l' i)
        , _♯ᵍ (λ x → ♯ᵍ-assoc (f x) g h i) a
```

The edge equivalences at the definedness-type level. Each is the
Sigma reassociation underlying the corresponding `♯ᵍ-assoc` step.

```agda
  private
    e₁₃ᵉ : ∣ is-defined (snd v1) ∣ ≃ ∣ is-defined (snd v3) ∣
    e₁₃ᵉ = iso→equiv
      (λ (((p , d) , gd) , hd) → (p , d) , gd , hd)
      (λ ((p , d) , gd , hd) → ((p , d) , gd) , hd)
      (λ _ → refl) (λ _ → refl)

    e₃₄ᵉ : ∣ is-defined (snd v3) ∣ ≃ ∣ is-defined (snd v4) ∣
    e₃₄ᵉ = iso→equiv
      (λ ((p , d) , gd , hd) → p , d , gd , hd)
      (λ (p , d , gd , hd) → (p , d) , gd , hd)
      (λ _ → refl) (λ _ → refl)

    e₁₂ᵉ : ∣ is-defined (snd v1) ∣ ≃ ∣ is-defined (snd v2) ∣
    e₁₂ᵉ = iso→equiv
      (λ (((p , d) , gd) , hd) → (p , d , gd) , hd)
      (λ ((p , d , gd) , hd) → ((p , d) , gd) , hd)
      (λ _ → refl) (λ _ → refl)

    e₂₅ᵉ : ∣ is-defined (snd v2) ∣ ≃ ∣ is-defined (snd v5) ∣
    e₂₅ᵉ = iso→equiv
      (λ ((p , dgd) , hd) → p , dgd , hd)
      (λ (p , dgd , hd) → (p , dgd) , hd)
      (λ _ → refl) (λ _ → refl)

    e₅₄ᵉ : ∣ is-defined (snd v5) ∣ ≃ ∣ is-defined (snd v4) ∣
    e₅₄ᵉ = iso→equiv
      (λ (p , (d , gd) , hd) → p , d , gd , hd)
      (λ (p , d , gd , hd) → p , (d , gd) , hd)
      (λ _ → refl) (λ _ → refl)
```

Both routes have the same underlying forward function on
definedness types: `(((p,d),gd),hd) -> (p,d,gd,hd)`. We
factor this out as `fwd` and transport the `is-equiv` proofs
from the route compositions to `fwd`. Then `LiftM-pathp-ext`
(with `sq = refl`) connects the two `LiftM-pathp` calls, since
they share `fwd` and the coherence `(lambda _ -> refl)`.

```agda
  route-A-eqv
    : ∣ is-defined (snd v1) ∣ ≃ ∣ is-defined (snd v4) ∣
  route-A-eqv = e₁₃ᵉ ∙e e₃₄ᵉ

  route-B-eqv
    : ∣ is-defined (snd v1) ∣ ≃ ∣ is-defined (snd v4) ∣
  route-B-eqv = e₁₂ᵉ ∙e e₂₅ᵉ ∙e e₅₄ᵉ

  private
    fwd : ∣ is-defined (snd v1) ∣ → ∣ is-defined (snd v4) ∣
    fwd (((p , d) , gd) , hd) = p , d , gd , hd

    fwd-A : route-A-eqv .fst ≡ fwd
    fwd-A i (((p , d) , gd) , hd) = p , d , gd , hd

    fwd-B : route-B-eqv .fst ≡ fwd
    fwd-B i (((p , d) , gd) , hd) = p , d , gd , hd

    eqv-A : is-equiv fwd
    eqv-A = subst is-equiv fwd-A (route-A-eqv .snd)

    eqv-B : is-equiv fwd
    eqv-B = subst is-equiv fwd-B (route-B-eqv .snd)

  pentagon
    : LiftM-pathp (max-assoc4 n' m' k' l') (snd v1) (snd v4)
        (fwd , eqv-A) (λ _ → refl)
    ≡ LiftM-pathp (max-assoc4 n' m' k' l') (snd v1) (snd v4)
        (fwd , eqv-B) (λ _ → refl)
  pentagon = LiftM-pathp-ext refl (snd v1) (snd v4)
    eqv-A eqv-B (λ _ → refl)
```


## LiftG 4-fold reassociation

```agda
♯G-assoc4
  : ∀ {u v w x y} {A : Type v} {B : Type w} {C : Type x}
      {D : Type y} {m k l : Nat}
  → (ga : LiftG u A)
    (f : A → LiftM u B m)
    (g : B → LiftM u C k)
    (h : C → LiftM u D l)
  → _♯G h (_♯G g (_♯G f ga))
    ≡ _♯G (λ x → _♯ᵍ (λ y → _♯ᵍ h (g y)) (f x)) ga
♯G-assoc4 (n , la) f g h i =
  max-assoc4 n _ _ _ i , ♯ᵍ-assoc4 la f g h i
```


## LiftG projections and bottom

Extract the grade from a graded partial element, and define the
everywhere-undefined element at grade 1.

```agda
gradeG : LiftG u A → Nat
gradeG = fst

⊥G : ∀ {u v} {A : Type v} → LiftG u A
⊥G = S Z , ⊥ₗ
```


## Graded Kleisli composition

The Kleisli composite of two graded partial functions extends the
second over the first, combining their grades via `max`.

```agda
_>=>ᵍ_
  : (A → LiftM u B m) → (B → LiftM u C k)
  → (A → LiftM u C (max m k))
(f >=>ᵍ g) a = _♯ᵍ g (f a)

infixr 5 _>=>ᵍ_
```


## Kleisli composition laws

The monad laws restated as composition laws for the Kleisli
category. Each is the pointwise lift of the corresponding monad law.

Left unit: composing with `ηᵍ` on the left is identity. Since
`max Z m` reduces definitionally, this is a homogeneous path.

```agda
>=>ᵍ-unitl
  : ∀ {u v w} {A : Type v} {B : Type w} {m : Nat}
  → (f : A → LiftM u B m)
  → (ηᵍ >=>ᵍ f) ≡ f
>=>ᵍ-unitl f i a = ♯ᵍ-unitl f a i
```

Right unit: composing with `ηᵍ` on the right is identity up to
`max.unitr`. This is a `PathP` because `max m Z` does not reduce
for variable `m`.

```agda
>=>ᵍ-unitr
  : ∀ {u v w} {A : Type v} {B : Type w} {m : Nat}
  → (f : A → LiftM u B m)
  → PathP (λ i → A → LiftM u B (Nat.max.unitr {n = m} i))
      (f >=>ᵍ ηᵍ) f
>=>ᵍ-unitr f i a = ♯ᵍ-unitr (f a) i
```

Associativity: Kleisli composition is associative up to `max.assoc`.

```agda
>=>ᵍ-assoc
  : ∀ {u v w x y} {A : Type v} {B : Type w} {C : Type x} {D : Type y}
    {m k l : Nat}
  → (f : A → LiftM u B m)
    (g : B → LiftM u C k)
    (h : C → LiftM u D l)
  → PathP (λ i → A → LiftM u D (Nat.max.assoc m k l i))
      ((f >=>ᵍ g) >=>ᵍ h) (f >=>ᵍ (g >=>ᵍ h))
>=>ᵍ-assoc f g h i a = ♯ᵍ-assoc (f a) g h i
```


## Functor laws for mapG

`mapG` is the functorial action on `LiftG`. It preserves identity
and composition. Because `LiftM` has `no-eta-equality`, paths
through `LiftM` must be constructed field-by-field via copatterns.

```agda
mapG-id : (ga : LiftG u A) → mapG id ga ≡ ga
mapG-id (n , la) i = n , p i where
  p : LiftM-map id la ≡ la
  p i .is-defined = is-defined la
  p i .value = value la

mapG-∘
  : ∀ {u v w x} {A : Type v} {B : Type w} {C : Type x}
  → (f : B → C) (g : A → B)
  → (ga : LiftG u A) → mapG f (mapG g ga) ≡ mapG (f ∘ g) ga
mapG-∘ f g (n , la) i = n , p i where
  p : LiftM-map f (LiftM-map g la) ≡ LiftM-map (f ∘ g) la
  p i .is-defined = is-defined la
  p i .value = f ∘ g ∘ value la
```


## Naturality of unit

`ηG` is natural: mapping before or after unit gives the same result.

```agda
η-natural
  : ∀ {u v w} {A : Type v} {B : Type w}
  → (f : A → B) (a : A)
  → mapG {u = u} f (ηG a) ≡ ηG (f a)
η-natural f a i = Z , LiftM-pathp refl
  (LiftM-map f (ηᵍ a)) (ηᵍ (f a)) aut (λ _ → refl) i
```


## Tensorial strength

Pair a pure value with a graded partial value. `strG` is
`mapG (a ,_)` and `strG'` is the symmetric version.

```agda
strG
  : ∀ {u v w} {A : Type v} {B : Type w}
  → A → LiftG u B → LiftG u (A × B)
strG a = mapG (a ,_)

strG'
  : ∀ {u v w} {A : Type v} {B : Type w}
  → LiftG u A → B → LiftG u (A × B)
strG' ga b = mapG (_, b) ga
```
