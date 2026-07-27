Lane Biocini
February 2026

Product of virtual graphs. Given two virtual graphs V and W, the product
has pairs of objects, pairs of morphisms, and componentwise Yoneda action.
The embedding property follows from extracting component fibers using the
other component's identity as a dummy morphism.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Data.Magmoid

module Cat.Data.Prod (V W : virtual-graphs) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Function.Embedding
  using ( is-embedding; is-embedding→contr-fibers
        ; is-embedding→injective )
open import Core.Transport.J using (subst)
open import Core.Transport.Properties
  using (is-contr-×)
import Cat.Data.Base

private
  module V = virtual-graphs V
  module W = virtual-graphs W
```

## Product yon

```agda
private
  yon-prod
    : ∀ {x y : V.ob × W.ob}
    → V.hom (fst x) (fst y) × W.hom (snd x) (snd y)
    → ∀ (w : V.ob × W.ob)
    → V.hom (fst w) (fst x) × W.hom (snd w) (snd x)
    → V.hom (fst w) (fst y) × W.hom (snd w) (snd y)
  yon-prod (f₁ , f₂) (w₁ , w₂) (k₁ , k₂) =
    V.yon f₁ w₁ k₁ , W.yon f₂ w₂ k₂
```

## Product embedding

We show `yon-prod` is an embedding (i.e. has propositional fibers) by
retracting each fiber onto the product of component fibers.

Given a fiber element `((g₁, g₂), β) : fiber yon-prod t`, we extract
component fibers using the other component's identity as a dummy. The
product of the two component fibers is contractible (since each
component yon is an embedding and the fiber is inhabited), and the
retraction from product-fibers to product yon-prod fibers followed by
the section back is the identity — which gives contractibility of the
product fiber when inhabited, hence propositional fibers.

```agda
private
  yon-prod-image-contr
    : ∀ {x y : V.ob × W.ob}
      (m : V.hom (fst x) (fst y)
         × W.hom (snd x) (snd y))
    → is-contr (fiber yon-prod (yon-prod m))
  yon-prod-image-contr
    {x₁ , x₂} {y₁ , y₂} (m₁ , m₂) = Contr c₀ c₁
    where
      fc : is-contr (fiber V.yon (V.yon m₁))
      fc = is-embedding→contr-fibers V.yon-emb
        (m₁ , refl)

      sc : is-contr (fiber W.yon (W.yon m₂))
      sc = is-embedding→contr-fibers W.yon-emb
        (m₂ , refl)

      c₀ : fiber yon-prod (yon-prod (m₁ , m₂))
      c₀ = (m₁ , m₂) , refl

      c₁ : (fb : fiber yon-prod (yon-prod (m₁ , m₂)))
         → c₀ ≡ fb
      c₁ ((g₁ , g₂) , β) = goal where
```

From the product path `β : yon-prod (g₁,g₂) ≡ yon-prod (m₁,m₂)`,
extract component yon-paths. Plugging in the other component's
identity as a dummy produces a fiber element for each component.

```agda
        v-fib : fiber V.yon (V.yon m₁)
        v-fib =
          g₁ , λ j w₁ k₁ →
            fst (β j (w₁ , x₂) (k₁ , W.idn))

        w-fib : fiber W.yon (W.yon m₂)
        w-fib =
          g₂ , λ j w₂ k₂ →
            snd (β j (x₁ , w₂) (V.idn , k₂))
```

Since each component fiber is contractible, we get canonical paths
from `(m₁, refl)` to each component fiber via the contractibility
center. The morphism paths `p₁ : m₁ ≡ g₁` and `p₂ : m₂ ≡ g₂`
are the first projections of these.

```agda
        ev : fc .center ≡ v-fib
        ev = fc .paths v-fib

        ew : sc .center ≡ w-fib
        ew = sc .paths w-fib

        p₁ : m₁ ≡ g₁
        p₁ i = ev i .fst

        p₂ : m₂ ≡ g₂
        p₂ i = ew i .fst
```

For the witness path, we need to show that at each point `(w, k)`,
the product components agree. For each choice of `(w₂, k₂)`,
the fiber `(g₁, λ j w₁ k₁ → fst (β j (w₁, w₂) (k₁, k₂)))` is
a V-fiber at `V.yon m₁`. Since `fc` is contractible, the path from
`fc .center` to this fiber agrees with `ev` on the first component
(both are paths `m₁ ≡ g₁`). We use this to fill in the witness.

```agda
        v-fib-gen
          : ∀ w₂ k₂ → fiber V.yon (V.yon m₁)
        v-fib-gen w₂ k₂ =
          g₁ , λ j w₁ k₁ →
            fst (β j (w₁ , w₂) (k₁ , k₂))

        w-fib-gen
          : ∀ w₁ k₁ → fiber W.yon (W.yon m₂)
        w-fib-gen w₁ k₁ =
          g₂ , λ j w₂ k₂ →
            snd (β j (w₁ , w₂) (k₁ , k₂))

        ev-gen
          : ∀ w₂ k₂ → fc .center ≡ v-fib-gen w₂ k₂
        ev-gen w₂ k₂ = fc .paths (v-fib-gen w₂ k₂)

        ew-gen
          : ∀ w₁ k₁ → sc .center ≡ w-fib-gen w₁ k₁
        ew-gen w₁ k₁ = sc .paths (w-fib-gen w₁ k₁)
```

The fiber `fc` is contractible, hence a proposition, so all paths
in it between any two points are equal. The path
`ev-gen w₂ k₂ : fc.center ≡ v-fib-gen w₂ k₂` and
`ev : fc.center ≡ v-fib` both start at `fc.center`, and their
targets have the same first component `g₁`. Since `fc` is
contractible, we can build a square filling the two paths.

We construct the goal directly using the generalized fiber paths.
At each point `(i, j, w, k)`, the fst component comes from
`ev-gen (snd w) (snd k) i .snd j (fst w) (fst k)`. The catch is
that at `j = i0`, this gives `V.yon (ev-gen w₂ k₂ i .fst) w₁ k₁`,
which may differ from `V.yon (p₁ i) w₁ k₁` when `(w₂, k₂)` differs
from `(x₂, W.idn)`. To handle this, we use the fact that the
contractible fiber forces all first-component paths to agree, by
routing through the contractibility.

The key: instead of using `p₁` from `ev` and then separately using
`ev-gen`, build a single coherent path. We use the contractibility
of the component product fiber.

```agda
        prod-fib
          : is-contr
              (fiber V.yon (V.yon m₁)
              × fiber W.yon (W.yon m₂))
        prod-fib = is-contr-× fc sc

        bwd
          : fiber V.yon (V.yon m₁)
          × fiber W.yon (W.yon m₂)
          → fiber yon-prod (yon-prod (m₁ , m₂))
        bwd ((h₁ , α₁) , (h₂ , α₂)) =
          (h₁ , h₂) , λ j w k →
            α₁ j (fst w) (fst k)
            , α₂ j (snd w) (snd k)

        fwd
          : fiber yon-prod (yon-prod (m₁ , m₂))
          → fiber V.yon (V.yon m₁)
          × fiber W.yon (W.yon m₂)
        fwd ((h₁ , h₂) , γ) =
          ( h₁ , λ j w₁ k₁ →
              fst (γ j (w₁ , x₂) (k₁ , W.idn)) )
          , ( h₂ , λ j w₂ k₂ →
              snd (γ j (x₁ , w₂) (V.idn , k₂)) )
```

The product fiber is contractible, so the composition
`bwd ∘ fwd` maps any product-yon fiber to one that factors
through the component fibers. To show `c₀ ≡ fb`, we go through
the product fiber center: `c₀ = bwd (fc.center, sc.center)`,
and `bwd (fwd fb)` is connected to `fb` by the section.

We actually just need that both `c₀` and `fb` equal `bwd (fwd fb)`.
The path `c₀ → bwd (prod-fib .center) → bwd (fwd fb) → fb`.

The first two steps use contractibility of `prod-fib`:
`bwd` applied to the path `prod-fib .center ≡ fwd fb`.

```agda
        step₁ : c₀ ≡ bwd (fwd c₀)
        step₁ = refl

        pair-path : prod-fib .center ≡ fwd ((g₁ , g₂) , β)
        pair-path = prod-fib .paths (fwd ((g₁ , g₂) , β))

        step₂ : c₀ ≡ bwd (fwd ((g₁ , g₂) , β))
        step₂ i = bwd (pair-path i)
```

For the final step, we need `bwd (fwd fb) ≡ fb`. The issue is
that `bwd (fwd fb)` reconstructs `β` using only the dummy-projected
components, which may lose information. Specifically,
`bwd (fwd ((g₁,g₂), β))` produces a `β'` where:
- `fst (β' j w k) = fst (β j (fst w, x₂) (fst k, W.idn))`
- `snd (β' j w k) = snd (β j (x₁, snd w) (V.idn, snd k))`

This may not equal `β`. To bridge the gap, we use the fact that
each component of `β` at any dummy choice produces the same fiber
element (up to the contractible fiber's propness). The squeezing
is precisely what the contractible fiber gives us.

For each `(w, k)`, the V-fiber element
`(g₁, λ j w₁ k₁ → fst (β j (w₁, snd w) (k₁, snd k)))`
equals `v-fib = (g₁, λ j w₁ k₁ → fst (β j (w₁, x₂) (k₁, W.idn)))`
since both lie in the contractible fiber `fc`. So
`fst (β j (fst w, snd w) (fst k, snd k))` and
`fst (β j (fst w, x₂) (fst k, W.idn))` are related by the fiber
path. Similarly for the W component.

Concretely, we construct a square using the contractible paths:

```agda
        v-sq
          : ∀ w₂ k₂ → v-fib ≡ v-fib-gen w₂ k₂
        v-sq w₂ k₂ =
          is-contr→is-prop fc v-fib (v-fib-gen w₂ k₂)

        w-sq
          : ∀ w₁ k₁ → w-fib ≡ w-fib-gen w₁ k₁
        w-sq w₁ k₁ =
          is-contr→is-prop sc w-fib (w-fib-gen w₁ k₁)

        step₃
          : bwd (fwd ((g₁ , g₂) , β))
          ≡ ((g₁ , g₂) , β)
        step₃ i =
          (v-sq x₂ W.idn i .fst
          , w-sq x₁ V.idn i .fst)
          , λ j w k →
              v-sq (snd w) (snd k) i .snd
                j (fst w) (fst k)
              , w-sq (fst w) (fst k) i .snd
                j (snd w) (snd k)

        goal : c₀ ≡ ((g₁ , g₂) , β)
        goal = step₂ ∙ step₃

  yon-prod-emb
    : ∀ {x y : V.ob × W.ob}
    → is-embedding (yon-prod {x} {y})
  yon-prod-emb t (n , p) =
    is-contr→is-prop
      (subst (is-contr ∘ fiber yon-prod) p
        (yon-prod-image-contr n))
      (n , p)
```

## Product magmoid

```agda
prod : magmoids
prod = str
  (V.ob × W.ob)
  (λ x y →
    V.hom (fst x) (fst y) × W.hom (snd x) (snd y))
  yon-prod
  yon-prod-emb
```

```agda
open Cat.Data.Base prod public
```
