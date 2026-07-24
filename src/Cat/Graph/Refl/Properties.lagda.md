Characterisations of the univalence condition. Under univalence the edge
relation is an identity system — edges coincide with identifications — and the
inward and outward fans are propositions together. The `po` interface collects
these for a fixed graph: `module P = po G` names its whole univalence calculus,
reached as `P.edge≃path`, `P.is-univalent→op`, and so on.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Graph.Refl.Properties where

open import Core.Type
open import Core.Data.Sigma
open import Core.Base
open import Core.Kan using (is-contr→is-prop)
open import Core.Equiv
open import Core.IdSys using (Ids→equiv)
open import Core.Transport.Properties
  using (is-identity-system; fundamental-theorem-id; prop-inhabited→is-contr; is-prop-is-prop)
open import Core.Groupoid using (Singl-contr-cofan)
open import Core.Transport.Base using (Singl-contr; transport)
open import Core.HLevel.Base using (Σ-is-prop; ⊤-is-prop; Π-is-prop; retract→is-hlevel; is-prop-equiv)
open import Cat.Graph.Refl.Type
open import Cat.Graph.Refl.Base

module po {v e} (G : reflexive-graph v e) where
  private module G = reflexive-graph G
  open rx G
```

## Edges are identifications

When every fan is a proposition it is contractible, so the edge relation is an
identity system: identifications out of `x` coincide with edges out of `x`.

```agda

  edge-idsys : is-univalent → is-identity-system G.edge G.rx
  edge-idsys univ = fundamental-theorem-id (λ x → prop-inhabited→is-contr (univ x) (fan-center x))

  edge≃path : is-univalent → ∀ {x y} → (x ≡ y) ≃ G.edge x y
  edge≃path univ = Ids→equiv (edge-idsys univ)
```

The forward direction of that equivalence is `to-edge`, so univalence is exactly
the statement that transporting reflexivity along an identification of vertices
exhausts the edges.

```agda

  is-univalent→to-edge-equiv : is-univalent → ∀ {x y} → is-equiv (to-edge {x} {y})
  is-univalent→to-edge-equiv univ = edge≃path univ .snd

  to-edge-equiv→is-univalent : (∀ {x y} → is-equiv (to-edge {x} {y})) → is-univalent
  to-edge-equiv→is-univalent te x =
    is-contr→is-prop
      (is-contr-equiv (esym (Σ-equiv-snd (λ y → to-edge {x} {y} , te {x} {y})))
                      (Singl-contr x))
```

## Inward and outward fans

Univalence and its opposite coincide. Each co-fan at `y` is equivalent to the
identifications ending at `y`, which are contractible; the outward direction is
dual through the flipped edge relation.

```agda

  is-univalent→op : is-univalent → is-univalent-op
  is-univalent→op univ y =
    is-contr→is-prop
      (is-contr-equiv (Σ-equiv-snd (λ x → esym (edge≃path univ {x} {y})))
                      (Singl-contr-cofan y))

  cofan-idsys : is-univalent-op → is-identity-system (λ y x → G.edge x y) G.rx
  cofan-idsys univ = fundamental-theorem-id (λ y → prop-inhabited→is-contr (univ y) (cofan-center y))

  is-univalent-op→ : is-univalent-op → is-univalent
  is-univalent-op→ univ x =
    is-contr→is-prop
      (is-contr-equiv (Σ-equiv-snd (λ y → esym (Ids→equiv (cofan-idsys univ) {y} {x})))
                      (Singl-contr-cofan x))

  op-path-object : is-univalent → rx.is-univalent (rx.op G)
  op-path-object = is-univalent→op

  is-univalent-is-prop : is-prop is-univalent
  is-univalent-is-prop = Π-is-prop λ _ → is-prop-is-prop _
```

Being a path object is itself a property, of a reflexive graph and of a displayed
one alike: a fan is a proposition in at most one way.

```agda

is-displayed-univalent-is-prop : ∀ {v v' e e'} {G : reflexive-graph v e}
                                 (D : rx.disp G v' e')
                               → is-prop (is-displayed-univalent D)
is-displayed-univalent-is-prop D = Π-is-prop λ _ → Π-is-prop λ _ → is-prop-is-prop _
```

## Total of a displayed path object

The total reflexive graph of a displayed path object over a path object is a
path object. Its fan at `(x , u)` reassociates to a sum over the base fan of the
displayed fans; the base fan is contractible, so the sum collapses to the
component fan of `D` at `x`, which is a proposition.

```agda

module _ {v e v' e'} {G : reflexive-graph v e} (D : rx.disp G v' e') where
  private
    module G = reflexive-graph G
    module D = reflexive-graphᴰ D
  open rx G

  total-path-object : is-univalent → is-displayed-univalent D → rx.is-univalent (rx.total G D)
  total-path-object G-univ D-univ (x , u) = is-contr→is-prop (is-contr-equiv chain component-contr)
    where
    B : fan x → Type (v' ⊔ e')
    B yp = Σ w ∶ D.vtx (fst yp) , D.edge x (fst yp) (snd yp) u w

    reassoc : rx.fan (rx.total G D) (x , u) ≃ (Σ z ∶ fan x , B z)
    reassoc = iso→equiv
      (λ ((y , w) , (p , d)) → (y , p) , (w , d))
      (λ ((y , p) , (w , d)) → (y , w) , (p , d))
      (λ _ → refl) (λ _ → refl)

    chain : rx.fan (rx.total G D) (x , u) ≃ B (fan-center x)
    chain = reassoc ∙e Σ-contr-fst (prop-inhabited→is-contr (G-univ x) (fan-center x))

    component-contr : is-contr (B (fan-center x))
    component-contr = prop-inhabited→is-contr (D-univ x u) (u , D.rx u)
```

## Discrete and codiscrete

The discrete graph is a path object — its fan at `x` is the contractible
singleton. The codiscrete graph is a path object exactly when its vertices form
a proposition.

```agda

disc-path-object : ∀ {ℓ} (A : Type ℓ) → rx.is-univalent (discrete A)
disc-path-object A x = is-contr→is-prop (Singl-contr x)

codisc-path-object : ∀ {ℓ} (A : Type ℓ) → is-prop A → rx.is-univalent (codiscrete A)
codisc-path-object A A-prop x = Σ-is-prop A-prop (λ _ → ⊤-is-prop)
```

## Constant, binary product

The component of a constant displayed graph is the fibre itself, so it is
univalent when the fibre is; the binary product is the total of the constant
displayed graph, so its univalence follows.

```agda

const-disp-path-object : ∀ {v e w z} (G : reflexive-graph v e) (S : reflexive-graph w z)
                       → rx.is-univalent S → is-displayed-univalent (rx.constant G S)
const-disp-path-object G S S-univ _ = S-univ

bin-prod-path-object : ∀ {v e w z} (G : reflexive-graph v e) (H : reflexive-graph w z)
                     → rx.is-univalent G → rx.is-univalent H
                     → rx.is-univalent (rx.binary-product G H)
bin-prod-path-object G H G-univ H-univ =
  total-path-object (rx.constant G H) G-univ (const-disp-path-object G H H-univ)
```

## Product and coproduct of a family

The fan of a product is the pointwise product of the fibre fans — a proposition
by function extensionality when each fibre is univalent. The coproduct's fan
sums an index identification with a fibre fan; the base singleton is
contractible, leaving the fibre fan at the transported vertex.

```agda

prod-path-object : ∀ {ℓ w z} (A : Type ℓ) (B : dep-rx w z A)
                 → is-path-objects B → rx.is-univalent (product A B)
prod-path-object A B B-univ f =
  retract→is-hlevel 1 bwd fwd (λ _ → refl) (Π-is-prop (λ x → B-univ x (f x)))
  where
  fwd : rx.fan (product A B) f → (∀ x → rx.fan (B x) (f x))
  fwd (g , e) x = g x , e x
  bwd : (∀ x → rx.fan (B x) (f x)) → rx.fan (product A B) f
  bwd h = (λ x → fst (h x)) , (λ x → snd (h x))

coprod-path-object : ∀ {ℓ w z} (A : Type ℓ) (B : dep-rx w z A)
                   → is-path-objects B → rx.is-univalent (coproduct A B)
coprod-path-object {w = w} {z = z} A B B-univ (a₀ , b₀) = is-contr→is-prop (is-contr-equiv chain fibre-contr)
  where
  module B x = reflexive-graph (B x)
  b₀' : B.vtx a₀
  b₀' = transport (λ i → B.vtx a₀) b₀

  F : (Σ a₁ ∶ A , a₀ ≡ a₁) → Type (w ⊔ z)
  F ap = Σ b₁ ∶ B.vtx (fst ap) , B.edge (fst ap) (transport (λ i → B.vtx (snd ap i)) b₀) b₁

  reassoc : rx.fan (coproduct A B) (a₀ , b₀) ≃ (Σ z ∶ (Σ a₁ ∶ A , a₀ ≡ a₁) , F z)
  reassoc = iso→equiv
    (λ ((a₁ , b₁) , (p , d)) → (a₁ , p) , (b₁ , d))
    (λ ((a₁ , p) , (b₁ , d)) → (a₁ , b₁) , (p , d))
    (λ _ → refl) (λ _ → refl)

  chain : rx.fan (coproduct A B) (a₀ , b₀) ≃ F (a₀ , refl)
  chain = reassoc ∙e Σ-contr-fst (Singl-contr a₀)

  fibre-contr : is-contr (F (a₀ , refl))
  fibre-contr = prop-inhabited→is-contr (B-univ a₀ b₀') (b₀' , B.rx a₀ b₀')

cotensor-path-object : ∀ {v e ℓ} (G : reflexive-graph v e) (A : Type ℓ)
                     → rx.is-univalent G → rx.is-univalent (rx.cotensor G A)
cotensor-path-object G A G-univ = prod-path-object A (λ _ → G) (λ _ → G-univ)

tensor-path-object : ∀ {v e ℓ} (G : reflexive-graph v e) (A : Type ℓ)
                   → rx.is-univalent G → rx.is-univalent (rx.tensor G A)
tensor-path-object G A G-univ = coprod-path-object A (λ _ → G) (λ _ → G-univ)
```

## Comprehension

When each `P x` is a proposition, the comprehension of a path object is a path
object: its fan reassociates to a sum over the base fan of the predicate, and the
contractible base fan collapses it to `P x`.

```agda

compr-path-object : ∀ {ℓ v e} (G : reflexive-graph v e) (P : reflexive-graph.vtx G → Type ℓ)
                  → rx.is-univalent G → (∀ x → is-prop (P x))
                  → rx.is-univalent (rx.comprehension G P)
compr-path-object G P G-univ P-prop (x , px) = is-prop-equiv chain (P-prop x)
  where
  reassoc : rx.fan (rx.comprehension G P) (x , px) ≃ (Σ w ∶ rx.fan G x , P (fst w))
  reassoc = iso→equiv
    (λ ((y , py) , e) → (y , e) , py)
    (λ ((y , e) , py) → (y , py) , e)
    (λ _ → refl) (λ _ → refl)

  chain : rx.fan (rx.comprehension G P) (x , px) ≃ P x
  chain = reassoc ∙e Σ-contr-fst (prop-inhabited→is-contr (G-univ x) (rx.fan-center G x))
```

## Univalent families

Univalence of the image is by construction the propositionality of each sum
`Σ y , B x ≃ B y`, that sum being the fan of the image at `x`. It is inhabited by
the identity equivalence, so it is equally a contractibility condition; and by
the fundamental theorem it is equally the statement that transport takes
identifications of indices to equivalences of fibres.

```agda

is-univalent-family→contr : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ')
                          → is-univalent-family B
                          → ∀ x → is-contr (Σ y ∶ A , B x ≃ B y)
is-univalent-family→contr B univ x = prop-inhabited→is-contr (univ x) (x , aut)

contr→is-univalent-family : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ')
                          → (∀ x → is-contr (Σ y ∶ A , B x ≃ B y))
                          → is-univalent-family B
contr→is-univalent-family B c x = is-contr→is-prop (c x)

is-univalent-family→path : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ')
                         → is-univalent-family B
                         → ∀ {x y} → (x ≡ y) ≃ (B x ≃ B y)
is-univalent-family→path B = po.edge≃path (image B)

to-edge-equiv→is-univalent-family
  : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ')
  → (∀ {x y} → is-equiv (rx.to-edge (image B) {x} {y}))
  → is-univalent-family B
to-edge-equiv→is-univalent-family B = po.to-edge-equiv→is-univalent (image B)
```
