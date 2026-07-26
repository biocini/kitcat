Spike: the framed virtual graph

A virtual graph carries no identity — `reflect`, `judgment` and the two
argument halves are built from objects and edges alone. What it carries
instead is a *framing*: a negative twist at the term half and a positive
one at the coterm half. The axiom pairs them, and where they meet they
cancel.

Read asynchronously, a term is a future and a coterm a buffer: the
negative twist is the pending read, the positive the pending write, and
their cancellation is one synchronous transmission — a ready value
fulfilling an expected delivery. Nothing in the structure lets that
transmission be named as an edge; it exists only as the operation of
performing it.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.SpikeFramedVirtual where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; module pcom; module Path; is-contr→is-prop)
open import Core.Path.Base
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (is-prop→is-set; is-prop-is-prop; prop-inhabited→is-contr)
open import Core.Equiv.Base using (_≃_; is-equiv; eqv-fibers; iso→equiv)
open import Core.HLevel.Base using (Π-is-prop; Πi-is-prop; is-prop-equiv)
open import Core.Equiv.Properties using (_∙e_; Π-contr-dom)
open import Core.Groupoid.Virtual using (module yon-unbiased)
```

## The carrier

```agda
record framed-virtual-graph o h : Type₊ (o ⊔ h) where
  field
    ob  : Type o
    hom : ob → ob → Type h

  term : ob → Type (o ⊔ h)
  term x = Σ w ∶ ob , hom w x

  coterm : ob → Type (o ⊔ h)
  coterm y = Σ v ∶ ob , hom y v

  argument : ob → ob → Type (o ⊔ h)
  argument x y = term x × coterm y

  conclusion : ∀ {x y} → argument x y → Type h
  conclusion γ = hom (γ .fst .fst) (γ .snd .fst)

  judgment : ob → ob → Type (o ⊔ h)
  judgment x y = (γ : argument x y) → conclusion γ

  field
    reflect : ∀ {x y} → hom x y → judgment x y
    twist⁺  : (x : ob) → hom x x
    twist⁻  : (x : ob) → hom x x

  var : (x : ob) → term x
  var x = x , twist⁻ x

  covar : (y : ob) → coterm y
  covar y = y , twist⁺ y

  axiom : (x : ob) → argument x x
  axiom x .fst = var x
  axiom x .snd = covar x

  eval : ∀ {x y} → judgment x y → hom x y
  eval {x} {y} α = α (var x , covar y)

  coact-π : ∀ {x y} → hom x y → (γ : coterm y) → hom x (γ .fst)
  coact-π {x} f γ = reflect f (var x , γ)

  act-π : ∀ {x y} → hom x y → (t : term x) → hom (t .fst) y
  act-π {y = y} f t = reflect f (t , covar y)

  coact : ∀ {x y} → hom x y → coterm y → coterm x
  coact f γ = γ .fst , coact-π f γ

  act : ∀ {x y} → hom x y → term x → term y
  act f t = t .fst , act-π f t
```

## The opposite is strict

Reversing edges exchanges the two argument halves, hence the two
twists — both fields, so the exchange is a swap. Doing it twice returns
the record on the nose, and evaluation at the axiom is unmoved: a
transmission looks the same from either end.

```agda
opᶠ : ∀ {o h} → framed-virtual-graph o h → framed-virtual-graph o h
opᶠ G .framed-virtual-graph.ob        = framed-virtual-graph.ob G
opᶠ G .framed-virtual-graph.hom x y   = framed-virtual-graph.hom G y x
opᶠ G .framed-virtual-graph.reflect f γ =
  framed-virtual-graph.reflect G f (γ .snd , γ .fst)
opᶠ G .framed-virtual-graph.twist⁺    = framed-virtual-graph.twist⁻ G
opᶠ G .framed-virtual-graph.twist⁻    = framed-virtual-graph.twist⁺ G

opᶠ-invol : ∀ {o h} (G : framed-virtual-graph o h) → opᶠ (opᶠ G) ≡ G
opᶠ-invol G = refl

op-eval : ∀ {o h} (G : framed-virtual-graph o h) {x y}
        → (f : framed-virtual-graph.hom G y x)
        → framed-virtual-graph.eval (opᶠ G)
            (framed-virtual-graph.reflect (opᶠ G) f)
        ≡ framed-virtual-graph.eval G (framed-virtual-graph.reflect G f)
op-eval G f = refl
```

## One transmission

Each hand's target is its own twist read through the *other* hand, so a
pending read meets a pending write. Counting: the target carries the
argument half's edge and one twist of each sign, so it is
winding-neutral — the edge with a transmission performed, and the
transmission never named as an edge of its own. The second projection
carries no twist at all, and a unit sitting over it would be a bare
twist for which a winding costs nothing.

```agda
module _ {o h} (G : framed-virtual-graph o h) where
  open framed-virtual-graph G

  cell⁻ : (x : ob) (γ : coterm x) → hom x (γ .fst)
  cell⁻ x γ = act-π (twist⁻ (γ .fst)) (x , γ .snd)

  cell⁺ : (x : ob) (t : term x) → hom (t .fst) x
  cell⁺ x t = coact-π (twist⁺ (t .fst)) (x , t .snd)

  is-unital⁻ : Type (o ⊔ h)
  is-unital⁻ = ∀ x → is-contr (fiber (coact-π {x} {x}) (cell⁻ x))

  is-unital⁺ : Type (o ⊔ h)
  is-unital⁺ = ∀ x → is-contr (fiber (act-π {x} {x}) (cell⁺ x))
```

## Stability

Representation is unique where it occurs. The statement names no twist
and touches no argument half, so it is winding-neutral — a condition on
`reflect` alone, unmoved by the framing — and it is a proposition
because being a proposition is.

```agda
  is-stable : Type (o ⊔ h)
  is-stable = ∀ {x y} (α : judgment x y) → is-prop (fiber (reflect {x} {y}) α)

  is-stable-is-prop : is-prop is-stable
  is-stable-is-prop =
    Πi-is-prop λ _ → Πi-is-prop λ _ → Π-is-prop λ _ → is-prop-is-prop _

  reflect-lc : is-stable → ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
  reflect-lc S {n = n} p = ap fst (S (reflect n) (_ , p) (n , refl))
```

Under it the composability tiers keep only their existence content:
uniqueness has moved to one place and stopped being repeated at every
composite.

```agda
  contr-from-stable
    : is-stable → ∀ {x y} (α : judgment x y)
    → fiber (reflect {x} {y}) α → is-contr (fiber (reflect {x} {y}) α)
  contr-from-stable S α = prop-inhabited→is-contr (S α)
```

The opposite exchanges the hands and the twists, hence the targets,
hence the tiers.

```agda
op-unital : ∀ {o h} (G : framed-virtual-graph o h)
          → is-unital⁻ (opᶠ G) ≡ is-unital⁺ G
op-unital G = refl

op-unital' : ∀ {o h} (G : framed-virtual-graph o h)
           → is-unital⁺ (opᶠ G) ≡ is-unital⁻ G
op-unital' G = refl
```

Stability crosses too, though not on the nose: the opposite reindexes a
judgment along the exchange of argument halves, and reindexing along a
bijection is an equivalence on fibers.

```agda
op-stable : ∀ {o h} (G : framed-virtual-graph o h)
          → is-stable G → is-stable (opᶠ G)
op-stable G S α =
  is-prop-equiv
    (iso→equiv (λ w → w .fst , λ i δ → w .snd i (δ .snd , δ .fst))
               (λ w → w .fst , λ i γ → w .snd i (γ .snd , γ .fst))
               (λ _ → refl) (λ _ → refl))
    (S (λ δ → α (δ .snd , δ .fst)))
```

## The two cuts

Composing terms with terms is the term hand, closing with the buffer;
composing coterms with coterms is the coterm hand, closing with the
future. The composite judgments are these carried into one slot of a
reflected head, so the term-hand cut goes through a pending write and
the coterm-hand cut through a pending read. Their windings are opposite,
and identifying them would be the synchronous coherence this fragment
forgets.

```agda
module cut {o h} (G : framed-virtual-graph o h) where
  open framed-virtual-graph G

  composite⁻ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁻ f g γ = reflect f (γ .fst , coact g (γ .snd))

  composite⁺ : ∀ {x y z} → hom x y → hom y z → judgment x z
  composite⁺ f g γ = reflect g (act f (γ .fst) , γ .snd)

  is-composable⁻ : Type (o ⊔ h)
  is-composable⁻ = ∀ {x y z} (f : hom x y) (g : hom y z)
                 → fiber (reflect {x} {z}) (composite⁻ f g)

  is-composable⁺ : Type (o ⊔ h)
  is-composable⁺ = ∀ {x y z} (f : hom x y) (g : hom y z)
                 → fiber (reflect {x} {z}) (composite⁺ f g)
```

Existence only: uniqueness sits in stability and is not restated here.
Where it is wanted back it is one application away.

```agda
  composable⁻-contr : is-stable G → is-composable⁻
                    → ∀ {x y z} (f : hom x y) (g : hom y z)
                    → is-contr (fiber (reflect {x} {z}) (composite⁻ f g))
  composable⁻-contr S C f g = contr-from-stable G S (composite⁻ f g) (C f g)

  composable⁺-contr : is-stable G → is-composable⁺
                    → ∀ {x y z} (f : hom x y) (g : hom y z)
                    → is-contr (fiber (reflect {x} {z}) (composite⁺ f g))
  composable⁺-contr S C f g = contr-from-stable G S (composite⁺ f g) (C f g)
```

## What a bare twist does to a cut

Given each twist standing in the other hand's fiber, its action is the
transmission. Carried into a cut, composing with a bare twist appends a
transmission to the argument half — it does not leave the head alone.

```agda
  module framed (pin⁻ : ∀ x → coact-π (twist⁺ x) ≡ cell⁻ G x)
                (pin⁺ : ∀ x → act-π   (twist⁻ x) ≡ cell⁺ G x) where

    transmit⁻ : ∀ {y} (γ : coterm y) → coact (twist⁺ y) γ ≡ (γ .fst , cell⁻ G y γ)
    transmit⁻ {y} γ i = γ .fst , pin⁻ y i γ

    transmit⁺ : ∀ {x} (t : term x) → act (twist⁻ x) t ≡ (t .fst , cell⁺ G x t)
    transmit⁺ {x} t i = t .fst , pin⁺ x i t

    cut-twist⁻ : ∀ {x y} (f : hom x y)
               → composite⁻ f (twist⁺ y)
               ≡ λ γ → reflect f (γ .fst , (γ .snd .fst , cell⁻ G y (γ .snd)))
    cut-twist⁻ f i γ = reflect f (γ .fst , transmit⁻ (γ .snd) i)

    cut-twist⁺ : ∀ {x y} (g : hom x y)
               → composite⁺ (twist⁻ x) g
               ≡ λ γ → reflect g ((γ .fst .fst , cell⁺ G x (γ .fst)) , γ .snd)
    cut-twist⁺ g i γ = reflect g (transmit⁺ (γ .fst) i , γ .snd)
```

A bare twist is a unit exactly where the transmission is the identity —
a hypothesis about the framing, never a consequence of the tiers.

```agda
    trivial⁻ : Type (o ⊔ h)
    trivial⁻ = ∀ x → cell⁻ G x ≡ snd

    trivial⁺ : Type (o ⊔ h)
    trivial⁺ = ∀ x → cell⁺ G x ≡ snd

    unit-if-trivial⁻ : trivial⁻ → ∀ {x y} (f : hom x y)
                     → composite⁻ f (twist⁺ y) ≡ reflect f
    unit-if-trivial⁻ T {y = y} f i γ =
      reflect f (γ .fst , (γ .snd .fst , (pin⁻ y ∙ T y) i (γ .snd)))

    unit-if-trivial⁺ : trivial⁺ → ∀ {x y} (g : hom x y)
                     → composite⁺ (twist⁻ x) g ≡ reflect g
    unit-if-trivial⁺ T {x} g i γ =
      reflect g ((γ .fst .fst , (pin⁺ x ∙ T x) i (γ .fst)) , γ .snd)
```

## The two towers

Each hand's composition is the representative of its own cut; stability
makes it well defined without composability restating uniqueness. Each
action distributes over its own hand's composition — the witness read
at that hand's axiom half — and associativity follows.

```agda
    module tower (S : is-stable G) (C⁻ : is-composable⁻) (C⁺ : is-composable⁺) where

      lc : ∀ {x y} {m n : hom x y} → reflect m ≡ reflect n → m ≡ n
      lc = reflect-lc G S

      _⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
      f ⨾⁻ g = C⁻ f g .fst

      _⨾⁺_ : ∀ {x y z} → hom x y → hom y z → hom x z
      f ⨾⁺ g = C⁺ f g .fst

      reflect-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
                 → reflect (f ⨾⁻ g) ≡ composite⁻ f g
      reflect-⨾⁻ f g = C⁻ f g .snd

      reflect-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z)
                 → reflect (f ⨾⁺ g) ≡ composite⁺ f g
      reflect-⨾⁺ f g = C⁺ f g .snd

      coact-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z) (k : coterm z)
               → coact (f ⨾⁻ g) k ≡ coact f (coact g k)
      coact-⨾⁻ f g k i = k .fst , reflect-⨾⁻ f g i (var _ , k)

      act-⨾⁺ : ∀ {x y z} (f : hom x y) (g : hom y z) (t : term x)
             → act (f ⨾⁺ g) t ≡ act g (act f t)
      act-⨾⁺ f g t i = t .fst , reflect-⨾⁺ f g i (t , covar _)

      module tri⁻ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z) where
        E : judgment w z
        E γ = reflect f (γ .fst , coact g (coact h (γ .snd)))

        a₁ a₂ : fiber (reflect {w} {z}) E
        a₁ = (f ⨾⁻ g) ⨾⁻ h
           , reflect-⨾⁻ (f ⨾⁻ g) h
           ∙ (λ i γ → reflect-⨾⁻ f g i (γ .fst , coact h (γ .snd)))
        a₂ = f ⨾⁻ (g ⨾⁻ h)
           , reflect-⨾⁻ f (g ⨾⁻ h)
           ∙ (λ i γ → reflect f (γ .fst , coact-⨾⁻ g h (γ .snd) i))

        σ : a₁ ≡ a₂
        σ = S E a₁ a₂

      assoc⁻ : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
             → (f ⨾⁻ g) ⨾⁻ h ≡ f ⨾⁻ (g ⨾⁻ h)
      assoc⁻ f g h = ap fst (tri⁻.σ f g h)

      assoc⁺ : ∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
             → (f ⨾⁺ g) ⨾⁺ h ≡ f ⨾⁺ (g ⨾⁺ h)
      assoc⁺ f g h = lc
        ( reflect-⨾⁺ (f ⨾⁺ g) h
        ∙ (λ i γ → reflect h (act-⨾⁺ f g (γ .fst) i , γ .snd))
        ∙ sym ( reflect-⨾⁺ f (g ⨾⁺ h)
              ∙ (λ i γ → reflect-⨾⁺ g h i (act f (γ .fst) , γ .snd)) ) )
```

## The unit laws for the composed pair

Where the transmission is the identity — the twists mutually inverse,
the framing itself still free — each hand gains exactly one unit law,
and the edge it gains is the *other* hand's composite of the pair.

```agda
      module _ (K⁻ : trivial⁻) (K⁺ : trivial⁺) where

        absorb⁻ : ∀ {y} (k : coterm y) → coact (twist⁺ y) k ≡ k
        absorb⁻ {y} k i = k .fst , (pin⁻ y ∙ K⁻ y) i k

        absorb⁺ : ∀ {x} (t : term x) → act (twist⁻ x) t ≡ t
        absorb⁺ {x} t i = t .fst , (pin⁺ x ∙ K⁺ x) i t

        unitr⁻ : ∀ {x y} (f : hom x y) → f ⨾⁻ twist⁺ y ≡ f
        unitr⁻ f = lc
          ( reflect-⨾⁻ f (twist⁺ _)
          ∙ (λ i γ → reflect f (γ .fst , absorb⁻ (γ .snd) i)) )

        unitl⁺ : ∀ {x y} (g : hom x y) → twist⁻ x ⨾⁺ g ≡ g
        unitl⁺ g = lc
          ( reflect-⨾⁺ (twist⁻ _) g
          ∙ (λ i γ → reflect g (absorb⁺ (γ .fst) i , γ .snd)) )

        pair⁺ : ∀ x → twist⁻ x ⨾⁺ twist⁺ x ≡ twist⁺ x
        pair⁺ x = unitl⁺ (twist⁺ x)

        pair⁻ : ∀ x → twist⁻ x ⨾⁻ twist⁺ x ≡ twist⁻ x
        pair⁻ x = unitr⁻ (twist⁻ x)
```

## The pentagon, one hand

The five bracketings of a four-fold coterm-hand cut are five points of
one fiber of `reflect`. Stability makes that fiber a proposition, hence
a set, so any two paths between two of its points agree — the pentagon
identity is that, and the classical form is its projection.

```agda
      module pentagon⁻ {w x y z v}
        (f : hom w x) (g : hom x y) (h : hom y z) (k : hom z v) where

        E : judgment w v
        E γ = reflect f (γ .fst , coact g (coact h (coact k (γ .snd))))

        b₁ b₂ b₃ b₄ b₅ : fiber (reflect {w} {v}) E
        b₁ = ((f ⨾⁻ g) ⨾⁻ h) ⨾⁻ k
           , reflect-⨾⁻ ((f ⨾⁻ g) ⨾⁻ h) k
           ∙ (λ i γ → reflect-⨾⁻ (f ⨾⁻ g) h i (γ .fst , coact k (γ .snd)))
           ∙ (λ i γ → reflect-⨾⁻ f g i (γ .fst , coact h (coact k (γ .snd))))
        b₂ = (f ⨾⁻ (g ⨾⁻ h)) ⨾⁻ k
           , reflect-⨾⁻ (f ⨾⁻ (g ⨾⁻ h)) k
           ∙ (λ i γ → reflect-⨾⁻ f (g ⨾⁻ h) i (γ .fst , coact k (γ .snd)))
           ∙ (λ i γ → reflect f (γ .fst , coact-⨾⁻ g h (coact k (γ .snd)) i))
        b₃ = f ⨾⁻ ((g ⨾⁻ h) ⨾⁻ k)
           , reflect-⨾⁻ f ((g ⨾⁻ h) ⨾⁻ k)
           ∙ (λ j γ → reflect f
               (γ .fst , (γ .snd .fst , tri⁻.a₁ g h k .snd j (var _ , γ .snd))))
        b₄ = (f ⨾⁻ g) ⨾⁻ (h ⨾⁻ k)
           , reflect-⨾⁻ (f ⨾⁻ g) (h ⨾⁻ k)
           ∙ (λ i γ → reflect-⨾⁻ f g i (γ .fst , coact (h ⨾⁻ k) (γ .snd)))
           ∙ (λ i γ → reflect f (γ .fst , coact g (coact-⨾⁻ h k (γ .snd) i)))
        b₅ = f ⨾⁻ (g ⨾⁻ (h ⨾⁻ k))
           , reflect-⨾⁻ f (g ⨾⁻ (h ⨾⁻ k))
           ∙ (λ j γ → reflect f
               (γ .fst , (γ .snd .fst , tri⁻.a₂ g h k .snd j (var _ , γ .snd))))

        pth : (a b : fiber (reflect {w} {v}) E) → a ≡ b
        pth = S E

        identity : pth b₁ b₄ ∙ pth b₄ b₅ ≡ pth b₁ b₂ ∙ (pth b₂ b₃ ∙ pth b₃ b₅)
        identity = is-prop→is-set (S E) b₁ b₅ _ _

        α₁₂ = ap fst (pth b₁ b₂)
        α₂₃ = ap fst (pth b₂ b₃)
        α₃₅ = ap fst (pth b₃ b₅)
        α₁₄ = ap fst (pth b₁ b₄)
        α₄₅ = ap fst (pth b₄ b₅)

        hom-identity : α₁₄ ∙ α₄₅ ≡ α₁₂ ∙ (α₂₃ ∙ α₃₅)
        hom-identity =
          sym (ap-comp fst (pth b₁ b₄) (pth b₄ b₅))
          ∙ ap (ap fst) identity
          ∙ ap-comp fst (pth b₁ b₂) (pth b₂ b₃ ∙ pth b₃ b₅)
          ∙ ap (α₁₂ ∙_) (ap-comp fst (pth b₂ b₃) (pth b₃ b₅))
```

Each classical edge lifts back into this fiber: whisker the triple's own
fiber path by whatever the fourth factor contributes, and the endpoints
land on two of the five points. The fiber being a proposition then
identifies the lift with `pth`, so the face is one application.

```agda
        γ₁₂ : b₁ ≡ b₂
        γ₁₂ i = tri⁻.σ f g h i .fst ⨾⁻ k
              , reflect-⨾⁻ (tri⁻.σ f g h i .fst) k
              ∙ (λ j γ → tri⁻.σ f g h i .snd j (γ .fst , coact k (γ .snd)))

        face₁₂ : α₁₂ ≡ ap (_⨾⁻ k) (assoc⁻ f g h)
        face₁₂ = ap (ap fst) (is-prop→is-set (S E) b₁ b₂ (pth b₁ b₂) γ₁₂)

        γ₃₅ : b₃ ≡ b₅
        γ₃₅ i = f ⨾⁻ tri⁻.σ g h k i .fst
              , reflect-⨾⁻ f (tri⁻.σ g h k i .fst)
              ∙ (λ j γ → reflect f
                  (γ .fst , (γ .snd .fst , tri⁻.σ g h k i .snd j (var _ , γ .snd))))

        face₃₅ : α₃₅ ≡ ap (f ⨾⁻_) (assoc⁻ g h k)
        face₃₅ = ap (ap fst) (is-prop→is-set (S E) b₃ b₅ (pth b₃ b₅) γ₃₅)
```

The three plain associator edges lift the same way with the fourth
factor's rewriting appended instead of whiskered. Appending lands on the
other side of the concatenation, so each end carries one reassociation;
where the head of one lift wraps the triple's own step, the wrapping
also has to be distributed. Every such correction holds the first
component fixed, so the projection is untouched.

```agda
        wrap : judgment x v → judgment w v
        wrap α γ = reflect f (γ .fst , (γ .snd .fst , α (var _ , γ .snd)))

        γ₂₃-pt : (i : I) → fiber (reflect {w} {v}) E
        γ₂₃-pt i = tri⁻.σ f (g ⨾⁻ h) k i .fst
                 , tri⁻.σ f (g ⨾⁻ h) k i .snd
                 ∙ (λ j γ → reflect f (γ .fst , coact-⨾⁻ g h (coact k (γ .snd)) j))

        l₂₃ : γ₂₃-pt i0 ≡ γ₂₃-pt i1
        l₂₃ i = γ₂₃-pt i

        c₂₃⁰ : b₂ ≡ γ₂₃-pt i0
        c₂₃⁰ i = b₂ .fst
               , Path.assoc (reflect-⨾⁻ (f ⨾⁻ (g ⨾⁻ h)) k)
                   (λ j γ → reflect-⨾⁻ f (g ⨾⁻ h) j (γ .fst , coact k (γ .snd)))
                   (λ j γ → reflect f (γ .fst , coact-⨾⁻ g h (coact k (γ .snd)) j)) i

        c₂₃¹ : γ₂₃-pt i1 ≡ b₃
        c₂₃¹ i = b₃ .fst
               , ( sym (Path.assoc (reflect-⨾⁻ f ((g ⨾⁻ h) ⨾⁻ k))
                     (λ j γ → reflect f (γ .fst , coact-⨾⁻ (g ⨾⁻ h) k (γ .snd) j))
                     (λ j γ → reflect f (γ .fst , coact-⨾⁻ g h (coact k (γ .snd)) j)))
                 ∙ ap (reflect-⨾⁻ f ((g ⨾⁻ h) ⨾⁻ k) ∙_)
                     (sym (ap-comp wrap (reflect-⨾⁻ (g ⨾⁻ h) k)
                             (λ j δ → reflect-⨾⁻ g h j (δ .fst , coact k (δ .snd)))))
                 ) i

        γ₂₃ : b₂ ≡ b₃
        γ₂₃ = c₂₃⁰ ∙ (l₂₃ ∙ c₂₃¹)

        face₂₃ : α₂₃ ≡ assoc⁻ f (g ⨾⁻ h) k
        face₂₃ =
          ap (ap fst) (is-prop→is-set (S E) b₂ b₃ (pth b₂ b₃) γ₂₃)
          ∙ ap-comp fst c₂₃⁰ (l₂₃ ∙ c₂₃¹)
          ∙ ap (refl ∙_) ( ap-comp fst l₂₃ c₂₃¹
                         ∙ Path.unitr (assoc⁻ f (g ⨾⁻ h) k) )
          ∙ Path.unitl (assoc⁻ f (g ⨾⁻ h) k)

        γ₄₅-pt : (i : I) → fiber (reflect {w} {v}) E
        γ₄₅-pt i = tri⁻.σ f g (h ⨾⁻ k) i .fst
                 , tri⁻.σ f g (h ⨾⁻ k) i .snd
                 ∙ (λ j γ → reflect f (γ .fst , coact g (coact-⨾⁻ h k (γ .snd) j)))

        l₄₅ : γ₄₅-pt i0 ≡ γ₄₅-pt i1
        l₄₅ i = γ₄₅-pt i

        c₄₅⁰ : b₄ ≡ γ₄₅-pt i0
        c₄₅⁰ i = b₄ .fst
               , Path.assoc (reflect-⨾⁻ (f ⨾⁻ g) (h ⨾⁻ k))
                   (λ j γ → reflect-⨾⁻ f g j (γ .fst , coact (h ⨾⁻ k) (γ .snd)))
                   (λ j γ → reflect f (γ .fst , coact g (coact-⨾⁻ h k (γ .snd) j))) i

        c₄₅¹ : γ₄₅-pt i1 ≡ b₅
        c₄₅¹ i = b₅ .fst
               , ( sym (Path.assoc (reflect-⨾⁻ f (g ⨾⁻ (h ⨾⁻ k)))
                     (λ j γ → reflect f (γ .fst , coact-⨾⁻ g (h ⨾⁻ k) (γ .snd) j))
                     (λ j γ → reflect f (γ .fst , coact g (coact-⨾⁻ h k (γ .snd) j))))
                 ∙ ap (reflect-⨾⁻ f (g ⨾⁻ (h ⨾⁻ k)) ∙_)
                     (sym (ap-comp wrap (reflect-⨾⁻ g (h ⨾⁻ k))
                             (λ j δ → reflect g (δ .fst , coact-⨾⁻ h k (δ .snd) j))))
                 ) i

        γ₄₅ : b₄ ≡ b₅
        γ₄₅ = c₄₅⁰ ∙ (l₄₅ ∙ c₄₅¹)

        face₄₅ : α₄₅ ≡ assoc⁻ f g (h ⨾⁻ k)
        face₄₅ =
          ap (ap fst) (is-prop→is-set (S E) b₄ b₅ (pth b₄ b₅) γ₄₅)
          ∙ ap-comp fst c₄₅⁰ (l₄₅ ∙ c₄₅¹)
          ∙ ap (refl ∙_) ( ap-comp fst l₄₅ c₄₅¹
                         ∙ Path.unitr (assoc⁻ f g (h ⨾⁻ k)) )
          ∙ Path.unitl (assoc⁻ f g (h ⨾⁻ k))
```

The last edge is the one where two appended steps commute rather than
reassociate: the fourth factor's rewriting and the head's cross, and
their square is `reflect-⨾⁻` read at a moving coterm.

```agda
        exch : (i j : I) → judgment w v
        exch i j γ = reflect-⨾⁻ f g i (γ .fst , coact-⨾⁻ h k (γ .snd) j)

        γ₁₄-pt : (i : I) → fiber (reflect {w} {v}) E
        γ₁₄-pt i = tri⁻.σ (f ⨾⁻ g) h k i .fst
                 , tri⁻.σ (f ⨾⁻ g) h k i .snd
                 ∙ (λ j γ → reflect-⨾⁻ f g j (γ .fst , coact h (coact k (γ .snd))))

        l₁₄ : γ₁₄-pt i0 ≡ γ₁₄-pt i1
        l₁₄ i = γ₁₄-pt i

        c₁₄⁰ : b₁ ≡ γ₁₄-pt i0
        c₁₄⁰ i = b₁ .fst
               , Path.assoc (reflect-⨾⁻ ((f ⨾⁻ g) ⨾⁻ h) k)
                   (λ j γ → reflect-⨾⁻ (f ⨾⁻ g) h j (γ .fst , coact k (γ .snd)))
                   (λ j γ → reflect-⨾⁻ f g j (γ .fst , coact h (coact k (γ .snd)))) i

        c₁₄¹ : γ₁₄-pt i1 ≡ b₄
        c₁₄¹ i = b₄ .fst
               , ( sym (Path.assoc (reflect-⨾⁻ (f ⨾⁻ g) (h ⨾⁻ k))
                     (λ j → exch i0 j)
                     (λ j γ → reflect-⨾⁻ f g j (γ .fst , coact h (coact k (γ .snd)))))
                 ∙ ap (reflect-⨾⁻ (f ⨾⁻ g) (h ⨾⁻ k) ∙_)
                     (Path.commutes (λ j → exch i0 j) (λ j → exch j i1)
                                    (λ j → exch j i0) (λ j → exch i1 j)
                                    (λ i j → exch i j))
                 ) i

        γ₁₄ : b₁ ≡ b₄
        γ₁₄ = c₁₄⁰ ∙ (l₁₄ ∙ c₁₄¹)

        face₁₄ : α₁₄ ≡ assoc⁻ (f ⨾⁻ g) h k
        face₁₄ =
          ap (ap fst) (is-prop→is-set (S E) b₁ b₄ (pth b₁ b₄) γ₁₄)
          ∙ ap-comp fst c₁₄⁰ (l₁₄ ∙ c₁₄¹)
          ∙ ap (refl ∙_) ( ap-comp fst l₁₄ c₁₄¹
                         ∙ Path.unitr (assoc⁻ (f ⨾⁻ g) h k) )
          ∙ Path.unitl (assoc⁻ (f ⨾⁻ g) h k)
```

Together they turn `hom-identity` into the pentagon on the classical
edges.

```agda
        pentagon : assoc⁻ (f ⨾⁻ g) h k ∙ assoc⁻ f g (h ⨾⁻ k)
                 ≡ ap (_⨾⁻ k) (assoc⁻ f g h)
                 ∙ (assoc⁻ f (g ⨾⁻ h) k ∙ ap (f ⨾⁻_) (assoc⁻ g h k))
        pentagon =
          sym ( ap (α₁₄ ∙_) face₄₅
              ∙ ap (_∙ assoc⁻ f g (h ⨾⁻ k)) face₁₄ )
          ∙ hom-identity
          ∙ ap (_∙ (α₂₃ ∙ α₃₅)) face₁₂
          ∙ ap (ap (_⨾⁻ k) (assoc⁻ f g h) ∙_)
              (ap (_∙ α₃₅) face₂₃ ∙ ap (assoc⁻ f (g ⨾⁻ h) k ∙_) face₃₅)
```

## What the spike settles

The framing is carried and the identity is not. Both tiers and both
composabilities hold at *any* framing over an arbitrary carrier, with no
h-level hypothesis, so none of them says which framing was chosen. The
opposite swaps the two twist fields, so it is strictly involutive, the
two tiers exchange definitionally, and evaluation at the axiom is fixed.

The twists are the centres, and nothing is assumed to place them:
`pcom.lr` is the flank exchange, and the argument half's contractibility
carries it everywhere. Each twist is the unique edge sitting in the
other hand's fiber — a pending read is what a pending write fulfils, and
each is the only thing that fulfils the other.

What the target buys is that no bare twist is a unit. `cut-twist⁻` and
`cut-twist⁺` say what a bare twist does to a cut: it appends a
transmission to the argument half rather than leaving the head alone.
`unit-if-trivial⁻` and `unit-if-trivial⁺` isolate the one case where it
would be a unit — where the transmission is the identity — and that is a
hypothesis about the framing, not a consequence of the tiers.

The two cuts stay apart. The coterm hand composes through a pending read
and the term hand through a pending write; their windings are opposite
and no tier
relates them. Identifying them is a synchronous cut, which is the
coherence this fragment is defined by forgetting, so each hand carries
its own tower.

Faithfulness of `reflect` is where the third tier sits. It cannot be
derived here: the old route ran a composite judgment down to its head,
which needed a twist whose action was the identity — exactly what the
targets refuse. So `is-stable` states it, and the statement earns its
place three ways. It names no twist and touches no argument half, so it
is winding-neutral and the framing cannot move it. It is a proposition
because being a proposition is. And it crosses the opposite, by
reindexing along the exchange of halves.

What it buys is that uniqueness stops being repeated. The composability
tiers keep only their existence content, `reflect-lc` is the
cancellation the towers run on, and each hand's fiber of `reflect` is a
proposition — hence a set, so every coherence between paths in it holds
outright.

The towers then run per hand. Each action distributes over its own
hand's composition, read off that hand's axiom half; associativity
follows for both; and where the transmission is the identity each hand
gains exactly one unit law, whose edge is the *other* hand's composite
of the twist pair. The missing unit law per hand is the one interchange
would supply, so its absence is the fragment working as intended rather
than a gap.

The pentagon is `identity` — five bracketings as five points of one
fiber, and any two paths between two points of a proposition agree.
`hom-identity` is its projection along `fst`.

Identifying those projected edges with the classical ones is a lift: put
the triple's own fiber path into the four-fold fiber, and stability
identifies the lift with `pth` in one application. The two whiskered
edges need nothing else. The three plain ones append the fourth factor's
rewriting rather than whiskering it, so each end carries a
reassociation; one of them also has to distribute a wrapping, and one
has two appended steps that commute rather than reassociate, its square
being `reflect-⨾⁻` read at a moving coterm. Every correction holds the
first component fixed, so none of them touches the projection.

With the five faces in hand `pentagon` is the classical identity on the
associators. Nothing in it is a truncation: the fiber is a proposition
because representation is unique, and that is the whole of the
coherence.
