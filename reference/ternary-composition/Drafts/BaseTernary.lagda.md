Lane Biocini
March 2026

Categories via ternary composition, inspired by virtual double
category composites and Sterling's virtual bicategories. Instead
of the binary Yoneda embedding `yon : hom x y -> forall w -> hom w x
-> hom w y`, we use a ternary "sandwich" embedding

    emb f w g z h = g . f . h

representing the ternary composite of `g`, `f`, and `h`. Identity
and composition are both characterized by contractible fibers of
`emb`, avoiding primitive identity data: the identity morphism is
the unique `e : hom x x` such that `emb e` acts as pass-through
binary composition, and the composite `f . g` is the unique
morphism whose `emb` agrees with chaining `emb f` and `emb g`.

The identity condition requires a unique `e : hom x x` satisfying
two absorption laws:

- Right absorption: `emb e w g x e = g` for all `g : hom w x`
- Left absorption: `emb e x e z h = h` for all `h : hom x z`

The first says sandwiching `g` on the right by `e` recovers `g`.
The second says sandwiching `h` on the left by `e` recovers `h`.
Together these give the ternary identity its full neutral character.

The derived binary composition `emb idn w a y f = a . f`
(identity-sandwich) lets us express the composition condition
uniformly: given `f : hom x y` and `g : hom y z`, there is a
unique `s : hom x z` whose ternary action agrees with
`emb idn w (emb idn w a y f) v (emb idn y g v b)`, i.e.
`(a . f) . (g . b)`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.BaseTernary where

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
              emb idn w (emb idn w a y f) v
                (emb idn y g v b)))

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

  unitr-emb
    : ∀ {x} {w : ob} (g : hom w x)
    → emb idn w g x idn ≡ g
  unitr-emb = idn-contr .center .snd .fst

  unitl-emb
    : ∀ {x} {z : ob} (h : hom x z)
    → emb idn x idn z h ≡ h
  unitl-emb = idn-contr .center .snd .snd

  emb-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g)
    ≡ (λ w a v b →
        emb idn w (emb idn w a y f) v
          (emb idn y g v b))
  emb-composite f g = composable-contr f g .center .snd

  emb-composite-pt
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      (w : ob) (a : hom w x) (v : ob) (b : hom z v)
    → emb (f ⨾ g) w a v b
    ≡ emb idn w (emb idn w a y f) v
        (emb idn y g v b)
  emb-composite-pt f g w a v b i =
    emb-composite f g i w a v b


  composite
    : ∀ {x y z} → hom x y → hom y z → hom x z
    → Type (o ⊔ h)
  composite f g s =
    emb s ≡ λ w a v b →
      emb idn w (emb idn w a _ f) v
        (emb idn _ g v b)
  syntax composite f g s = f ⨾ g => s

  is-composable
    : ∀ {x y z} → hom x y → hom y z → Type (o ⊔ h)
  is-composable f g =
    fiber (emb {_} {_})
      (λ w a v b →
        emb idn w (emb idn w a _ f) v
          (emb idn _ g v b))

  composite-contr
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-contr (is-composable f g)
  composite-contr = composable-contr

  cast-path
    : ∀ {x y z} {f : hom x y} {g : hom y z}
      {s : hom x z}
    → f ⨾ g => s → f ⨾ g ≡ s
  cast-path {f = f} {g} α =
    ap fst (composite-contr f g .paths (_ , α))

  cast-pathp
    : ∀ {x y z} {f : hom x y} {g : hom y z}
      {s : hom x z}
    → (α : f ⨾ g => s)
    → PathP (λ i → f ⨾ g => (cast-path α i))
        (emb-composite f g) α
  cast-pathp {f = f} {g} α =
    ap snd (composite-contr f g .paths (_ , α))

  is-composable-is-prop
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-prop (is-composable f g)
  is-composable-is-prop f g =
    is-contr→is-prop (composite-contr f g)
```

### Obstruction to unit laws and associativity

Deriving the binary unit laws from the ternary absorption
conditions requires reducing `emb idn w X v Y` when neither
`X` nor `Y` is `idn`. The absorption laws only handle the
degenerate cases (`Y = idn` for right absorption, `X = idn`
for left absorption). Concretely, for `unitr : f . idn = f`,
the composite witness `f . idn => f` demands:

    emb f = lam w a v b ->
      emb idn w (emb idn w a y f) v (emb idn y idn v b)

Left absorption simplifies the innermost term: `emb idn y
idn v b = b`. But the remaining `emb idn w (emb idn w a y f)
v b` cannot be reduced to `emb f w a v b` using absorption
alone, since neither argument position holds `idn`.

This gap is structural: bridging ternary absorption to binary
neutrality requires either a stronger identity axiom (e.g.
one that directly relates `emb idn` to pointwise application)
or an indirect argument via the composition fiber that
establishes the factoring property `emb idn w X v b = X . b`
for the appropriate notion of binary composition.
