The Yoneda lemma for categories: natural transformations
from the representable `hom(a, -)` to a covariant family `P` are
equivalent to `P.Fib a`.

The forward map (evaluation at `idn`) and backward map (extension
by the covariant action) form a quasi-inverse at the component
level. The forward-backward round-trip uses `act-id`; the
backward-forward round-trip uses `naturality` and `post-eval`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Depreciated.Type

module Cat.Depreciated.Yoneda {o h} (C : category o h) where

open category C
open import Cat.Depreciated.Covariant C

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan

private variable
  o' o'' : Level
```


## Natural transformations

A natural transformation between covariant families consists of
a component map at each object, commuting with the actions.

```agda
record nat-trans
    (P : covariant o') (Q : covariant o'')
    : Type (o ⊔ h ⊔ o' ⊔ o'') where
  no-eta-equality
  field
    component
      : ∀ x → P .covariant.Fib x → Q .covariant.Fib x
    naturality
      : ∀ {x y} (f : hom x y) (p : P .covariant.Fib x)
      → component y (P .covariant.act f p)
        ≡ Q .covariant.act f (component x p)

open nat-trans
```


## The Yoneda maps

Evaluation: apply the natural transformation at `a` to the
identity morphism.

```agda
yoneda-fwd
  : (P : covariant o') (a : ob)
  → nat-trans (hom-cov a) P → P .covariant.Fib a
yoneda-fwd P a η = η .component a (idn a)
```

Extension: transport the element along each morphism. The
naturality for `yoneda-bwd` uses `comp-eq` to rewrite
`yon f _ g` as `g ⨾ f`, then `act-comp`.

```agda
yoneda-bwd
  : (P : covariant o') (a : ob)
  → P .covariant.Fib a → nat-trans (hom-cov a) P
yoneda-bwd P a pa .component x f =
  P .covariant.act f pa
yoneda-bwd P a pa .naturality {x} {y} f g =
  ap (λ k → P .covariant.act k pa) (sym (comp-eq g f))
  ∙ P .covariant.act-comp g f pa
```


## Round-trips

The forward-backward composite evaluates `P.act idn pa`,
which equals `pa` by `act-id`.

```agda
yoneda-eval
  : (P : covariant o') (a : ob)
  → (pa : P .covariant.Fib a)
  → yoneda-fwd P a (yoneda-bwd P a pa) ≡ pa
yoneda-eval P a pa = P .covariant.act-id pa
```

The backward-forward composite on the component level:
`P.act f (η.component a idn) ≡ η.component x f` follows
from naturality at `(f, idn)` and `post-eval`.

```agda
yoneda-ext
  : (P : covariant o') (a : ob)
  → (η : nat-trans (hom-cov a) P)
  → ∀ x (f : hom a x)
  → yoneda-bwd P a (yoneda-fwd P a η) .component x f
    ≡ η .component x f
yoneda-ext P a η x f =
  sym (η .naturality f (idn a))
  ∙ ap (η .component x) (post-eval f)
```
