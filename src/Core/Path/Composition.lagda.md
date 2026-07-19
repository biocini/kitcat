Lane Biocini
March 2026

Canonical path composition from the contractible center.

`repr-singl-contr` gives
`is-contr (Σ y ∶ A i1 , ∀ w → w ≡ x → ∀ z → y ≡ z → PathP A w z)`.
The center is `(coe₀₁ x, repr.emb (coe-filler x))`. At constant
type family, the second projection is `repr.emb refl`, which IS
binary composition:
`repr.emb refl _ a _ b = pcom (sym a) refl b : w ≡ z`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Path.Composition where

open import Core.Base
open import Core.Type using (Level; Type; _∘_)
open import Core.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Core.Kan
open import Core.Groupoid.Virtual
open import Core.Transport.Properties using (SinglP-contr)

private variable
  u : Level
  A : Type u
```

## Binary composition from the center

`repr.emb refl` at the center of the contractible fiber gives
the canonical composition: `pcom (sym a) refl b`. The center
point `x` is inferred from the argument types.

```agda

_⊙_ : {w x z : A} → w ≡ x → x ≡ z → w ≡ z
_⊙_ {x = x} a b = repr.emb (refl {x = x}) _ a _ b
infixr 9 _⊙_

```

## Dependent composition from the center

For a non-constant type family, the center gives dependent
composition through the canonical filler.

```agda

module DepComp (A : I → Type u) (x : A i0) where

  comp-target : A i1
  comp-target = repr-singl-contr {A = A} {x} .center .fst

  comp-op : ∀ w → w ≡ x → ∀ z → comp-target ≡ z → PathP A w z
  comp-op = repr-singl-contr {A = A} {x} .center .snd

```

## Recentering contractible types

Given a contractible type and any element, produce a new
contractibility proof centered at that element. The paths from the
new center to any point factor through the original center.

```agda

recenter
  : ∀ {u} {A : Type u}
  → is-contr A → (c : A) → is-contr A
recenter cc c .center = c
recenter cc c .paths a =
  sym (cc .paths c) ∙ cc .paths a

```

## Representable fiber type

The representable fiber `Repr A x` bundles a target point
`y : A i1` with the ternary composition operation
`∀ w → w ≡ x → ∀ z → y ≡ z → PathP A w z`. The contractibility
of `Repr A x` (via `repr-singl-contr`) expresses that the path
groupoid has a unique composition operation.

```agda

Repr : ∀ {u} (A : I → Type u) (x : A i0) → Type u
Repr A x =
  Σ y ∶ A i1
  , ∀ w → w ≡ x → ∀ z → y ≡ z → PathP A w z

```

## Composition-centered contractibility

`repr-singl-contr` gives `is-contr (Repr A x)` with center
`(coe₀₁ x, repr.emb filler₀)` where `filler₀ : PathP A x y₀`
is the canonical coercion filler. The ternary operation at the
center is `repr.emb filler₀ w a z b = pcom (sym a) filler₀ b`.

We recenter at the element `(y₀, F)` where the ternary operation
factors through `pcom refl` (= `_∙_` / `cat.composite`):

    F w a z b = pcom refl (pcom (sym a) filler₀ refl) b

The inner `pcom (sym a) filler₀ refl` builds a dependent path
from `w` to `y₀`, and the outer `pcom refl` composes it with `b`.
At constant type family, `filler₀` is propositionally `refl`, so
`F w a z b` reduces propositionally to `pcom refl a b = a ∙ b`.

```agda

module ∙-repr {A : I → Type u} {x : A i0} where

  private
    singlP : is-contr (Σ y ∶ A i1 , PathP A x y)
    singlP = SinglP-contr x

    y₀ : A i1
    y₀ = singlP .center .fst

    filler₀ : PathP A x y₀
    filler₀ = singlP .center .snd

  ∙-op : ∀ w → w ≡ x → ∀ z → y₀ ≡ z → PathP A w z
  ∙-op w a z b =
    cat.composite (repr.emb filler₀ w a y₀ refl) b

  ∙-repr-center : Repr A x
  ∙-repr-center = y₀ , ∙-op

  ∙-repr-contr : is-contr (Repr A x)
  ∙-repr-contr = recenter repr-singl-contr ∙-repr-center

```

## Unit laws

Left unit: `refl ⊙ b = pcom (sym refl) refl b = pcom refl refl b`
since `sym refl` reduces to `refl`. This is `refl ∙ b`,
and `Path.unitl` gives `refl ∙ b ≡ b`.

Right unit: `a ⊙ refl = pcom (sym a) refl refl ≡ a`.
The connection `a (~ j ∨ i)` fills `HCell (sym a) refl refl a`,
and `pcom.unique` gives the path.

```agda

unitl : {x y : A} (b : x ≡ y) → refl ⊙ b ≡ b
unitl = Path.unitl

unitr : {x y : A} (a : x ≡ y) → a ⊙ refl ≡ a
unitr a = pcom.unique (sym a) refl refl (a , λ i j → a (~ j ∨ i))

idem : {x : A} → refl ⊙ refl ≡ refl {x = x}
idem = unitl refl

```

## Comparison with existing composition

`_⊙_` computes as `pcom (sym a) refl b`.
`_∙_` computes as `pcom refl a b`.
Both fill `HComposite (sym a) refl b`: the canonical fill gives
`a ⊙ b`, and an hcom pasting the connection `a (~ j ∨ i)` with
`pfil refl a b` gives `a ∙ b`. Then `pcom.unique` bridges them.

```agda

⊙-vs-∙ : {w x z : A} (a : w ≡ x) (b : x ≡ z)
  → a ⊙ b ≡ a ∙ b
⊙-vs-∙ {x = x} a b = pcom.unique (sym a) refl b (a ∙ b , cell) where
  cell : HCell (sym a) refl b (a ∙ b)
  cell i j = hcom (∂ i ∨ ∂ j) λ where
    k (i = i0) → a (~ j)
    k (i = i1) → b (j ∧ k)
    k (j = i0) → x
    k (j = i1) → pfil refl a b i k
    k (k = i0) → a (~ j ∨ i)

```

## Associativity

Both `(a ⊙ b) ⊙ c` and `a ⊙ (b ⊙ c)` fill
`HComposite (sym a) b c`, so `HComposite.unique` gives the path.
The two HCells are built by pasting fillers of the inner
compositions with connections.

```agda

assoc : {v w x y : A} (a : v ≡ w) (b : w ≡ x) (c : x ≡ y)
  → (a ⊙ b) ⊙ c ≡ a ⊙ (b ⊙ c)
assoc a b c = ap fst (HComposite.unique (sym a) b c
    (((a ⊙ b) ⊙ c) , rcoh⊙)
    ((a ⊙ (b ⊙ c)) , lcoh⊙))
  where
  -- The filler of b ⊙ c expands the i=1 face from refl to c,
  -- while the connection a(~k ∨ ~j) collapses the base to b(i ∧ ~j).
  -- The system at j=1 recovers pcom.sys (sym a) refl (b ⊙ c).
  lcoh⊙ : HCell (sym a) b c (a ⊙ (b ⊙ c))
  lcoh⊙ i j = hcom (∂ i ∨ ~ j) λ where
    k (i = i0) → a (~ k ∨ ~ j)
    k (i = i1) → pfil (sym b) refl c k j
    k (j = i0) → b i
    k (k = i0) → b (i ∧ ~ j)

  -- The reversed filler of a ⊙ b expands the i=0 face
  -- from b(j) to a(~j), while c(j ∧ k) fills the i=1 face.
  -- The system at j=1 recovers pcom.sys (sym(a ⊙ b)) refl c.
  rcoh⊙ : HCell (sym a) b c ((a ⊙ b) ⊙ c)
  rcoh⊙ i j = hcom (∂ i ∨ ~ j) λ where
    k (i = i0) → pfil (sym a) refl b (~ k) j
    k (i = i1) → c (j ∧ k)
    k (j = i0) → b i
    k (k = i0) → b (i ∨ j)

```

## Inverse laws

`sym a ⊙ a` reduces to `pcom a refl a`. The pair `(refl, refl)`
fills `HComposite a refl a` since `HCell a refl a refl` is just
`a ≡ a`, which `refl` inhabits.

Symmetrically, `a ⊙ sym a` reduces to `pcom (sym a) refl (sym a)`,
and `HCell (sym a) refl (sym a) refl` is `sym a ≡ sym a`.

```agda

invl : {x y : A} (a : x ≡ y) → sym a ⊙ a ≡ refl
invl a = pcom.unique a refl a (refl , refl)

invr : {x y : A} (a : x ≡ y) → a ⊙ sym a ≡ refl
invr a = pcom.unique (sym a) refl (sym a) (refl , refl)

```

## Normal form comparison

Concrete tests checking whether `_⊙_` laws agree with `_∙_` laws
definitionally or only propositionally.

```agda

module NormalForms {A : Type u} where

```

Composition itself: `refl ⊙ refl` reduces to `pcom refl refl refl`,
the same as `refl ∙ refl`. Both agree with `refl` propositionally
via `idem` / `Path.idem`.

```agda

  test-refl-⊙ : {x : A} → refl ⊙ refl ≡ refl {x = x}
  test-refl-⊙ = idem

  test-refl-∙ : {x : A} → refl ∙ refl ≡ refl {x = x}
  test-refl-∙ {x = x} = Path.idem {A = A} x

```

Unit law agreement: `unitl` IS `Path.unitl` by definition, so
they agree definitionally.

```agda

  test-unitl : {x y : A} (b : x ≡ y) → unitl b ≡ Path.unitl b
  test-unitl b = refl -- definitional

```

The right unit laws prove different statements (`a ⊙ refl ≡ a`
vs `a ∙ refl ≡ a`), so direct comparison is not meaningful.
Instead we verify each has the correct type.

```agda

  test-unitr-⊙ : {x y : A} (a : x ≡ y) → a ⊙ refl ≡ a
  test-unitr-⊙ = unitr

  test-unitr-∙ : {x y : A} (a : x ≡ y) → a ∙ refl ≡ a
  test-unitr-∙ = Path.unitr

```

Associativity: same situation — the statements involve different
composition operators, so we verify each has the correct type.

```agda

  test-assoc-⊙
    : {v w x y : A} (a : v ≡ w) (b : w ≡ x) (c : x ≡ y)
    → (a ⊙ b) ⊙ c ≡ a ⊙ (b ⊙ c)
  test-assoc-⊙ = assoc

  test-assoc-∙
    : {v w x y : A} (a : v ≡ w) (b : w ≡ x) (c : x ≡ y)
    → a ∙ (b ∙ c) ≡ (a ∙ b) ∙ c
  test-assoc-∙ = Path.assoc

```

Inverse law agreement: `invl`/`invr` for `_⊙_` are defined above.
`Path.invl`/`Path.invr` use `_∙_`. The statements differ in which
composition appears, so we verify type correctness.

```agda

  test-invl-⊙ : {x y : A} (a : x ≡ y) → sym a ⊙ a ≡ refl
  test-invl-⊙ = invl

  test-invl-∙ : {x y : A} (a : x ≡ y) → sym a ∙ a ≡ refl
  test-invl-∙ = Path.invl

```

## Open questions

- HIT interaction tests
- Higher-dimensional normal form comparison
- `⊙-vs-∙ refl refl ≡ refl` (loop triviality from contractible fiber)
- Assoc coherence at refl (Mac Lane coherence for the path groupoid)

## Normal form tests from Cat.Coherence

Cat.Coherence defines `pcom→∙ : pcom (sym p) q r ≡ p ∙ q ∙ r`
via `pcom.unique`. Since `a ⊙ b = pcom (sym a) refl b`, specializing
at `q = refl` gives `a ⊙ b ≡ a ∙ refl ∙ b`. Composing with
`ap (a ∙_) (Path.unitl b)` recovers `⊙-vs-∙`.

```agda

module NormalFormTests {A : Type u} where

```

### pcom→∙ relationship

`pcom (sym p) q r ≡ p ∙ q ∙ r` is exactly `cat.lcoh p q r` as
the HCell witness. At `q = refl`, `pcom (sym a) refl b = a ⊙ b`
and the right side is `a ∙ refl ∙ b`. This is NOT `a ∙ b` — the
`refl` in the middle doesn't vanish definitionally.

```agda

  ⊙-via-pcom→∙ : {w x z : A}
    (a : w ≡ x) (b : x ≡ z)
    → a ⊙ b ≡ a ∙ refl ∙ b
  ⊙-via-pcom→∙ a b = pcom→∙ a refl b

```

### ap-comp for ⊙

The `_∙_` version in Core.Path.Base is
`ap-comp : ap f (p ∙ q) ≡ ap f p ∙ ap f q`.
Both sides of the `_⊙_` analog unfold to pcom expressions.
`ap f (a ⊙ b) = ap f (pcom (sym a) refl b)` and
`ap f a ⊙ ap f b = pcom (sym (ap f a)) refl (ap f b)`.
The bridge is `pcom.ap` which converts `ap f ∘ pcom` to
`pcom ∘ ap f` on each face.

```agda

  ap-comp-⊙ : ∀ {v} {B : Type v} (f : A → B)
    {w x z : A} (a : w ≡ x) (b : x ≡ z)
    → ap f (a ⊙ b) ≡ ap f a ⊙ ap f b
  ap-comp-⊙ f a b =
    pcom.map (λ _ → f) (sym a) refl b

```

### Evaluating at refl

`pcom refl refl refl` is an hcom with all-refl boundary. It does
not reduce to `refl` definitionally — the hcom is stuck. So all
these need propositional proofs.

```agda

  -- unitr refl and idem both have type refl ⊙ refl ≡ refl.
  -- The type refl ⊙ refl (= pcom refl refl refl) is a stuck
  -- hcom, so neither reduces to refl definitionally.
  -- Both arise as pcom.unique applied to (refl, cell) in the
  -- contractible HComposite refl refl refl.
  test-unitr-type
    : {x : A} → refl ⊙ refl ≡ refl {x = x}
  test-unitr-type = unitr refl

  test-invl-type
    : {x : A} → refl ⊙ refl ≡ refl {x = x}
  test-invl-type = invl refl

  -- idem IS unitl refl = Path.unitl refl, definitionally.
  test-idem-def
    : {x : A} → idem {x = x} ≡ Path.unitl refl
  test-idem-def = refl -- definitional

  -- Assoc coherence at refl: connecting
  --   ap (_⊙ refl) idem ∙ idem
  -- with
  --   assoc refl refl refl ∙ ap (refl ⊙_) idem ∙ idem
  -- as paths (refl ⊙ refl) ⊙ refl ≡ refl.
  -- Both embed into the reversed singl Σ y, y ≡ refl, which
  -- is contractible. The proof uses total-contr-unique.
  -- test-assoc-coherence
  --   : {x : A}
  --   → ap (_⊙ refl) (idem {x = x}) ∙ idem
  --   ≡ assoc refl refl refl ∙ ap (refl ⊙_) idem ∙ idem
  -- -- Both sides are paths from a stuck hcom to refl. Connecting
  -- -- them amounts to a coherence for the path groupoid's
  -- -- associator at refl. Provable via explicit hcom fillers or
  -- -- by embedding into a contractible E₃ fiber (as in
  -- -- Cat.Coherence), but non-trivial.
  -- test-assoc-coherence {x} = {!refl!}

```

### Nested composition normal forms

Triple compositions at `refl` reduce through `idem`.

```agda

  test-triple-l
    : {x : A} → (refl ⊙ refl) ⊙ refl ≡ refl {x = x}
  test-triple-l = ap (_⊙ refl) idem ∙ idem

  test-triple-r
    : {x : A} → refl ⊙ (refl ⊙ refl) ≡ refl {x = x}
  test-triple-r = ap (refl ⊙_) idem ∙ idem

  -- assoc bridges the two triple-idem proofs: composing
  -- assoc with test-triple-r gives test-triple-l.
  -- Requires comparing paths in A at a specific point,
  -- which in general needs is-set A. In arbitrary A
  -- this is provable via embedding into the contractible
  -- HComposite fiber, but the cell construction is non-trivial.
  -- test-triple-bridge
  --   : {x : A}
  --   → test-triple-l {x = x}
  --   ≡ assoc refl refl refl ∙ test-triple-r
  -- test-triple-bridge {x} = {!!}

```

### Comparison of ⊙-vs-∙ at specific values

`refl ⊙ refl` and `refl ∙ refl` are both `pcom refl refl refl`,
so they are definitionally equal. `⊙-vs-∙` at refl is a path
from `pcom refl refl refl` to itself, which equals `refl` via
`pcom.unit`.

```agda

  test-⊙∙-refl-val
    : {x : A} → refl ⊙ refl ≡ refl ∙ refl {x = x}
  test-⊙∙-refl-val = refl -- definitional

  -- ⊙-vs-∙ refl refl : pcom refl refl refl ≡ pcom refl refl refl
  -- is a loop in the contractible HComposite fiber, hence refl.
  -- The proof uses is-contr→is-set on HComposite to show the
  -- loop is trivial, then ap fst to project.
  -- test-⊙∙-refl
  --   : {x : A} → ⊙-vs-∙ (refl {x = x}) refl ≡ refl
  -- test-⊙∙-refl = {!!}

```

### Pentagon-relevant terms

The ternary `repr.emb` is the fundamental operation. Composition
of the ternary action factors through `noy-composite` in Cat.Virtual.
For the path groupoid, `repr.emb q w p z r = pcom (sym p) q r` and
`noy` is post-composition. Testing that nested `repr.emb` at `refl`
center agrees with composition of the actions.

```agda

  -- The noy-composite analog for the path groupoid:
  -- (a ⊙ b) ∙ c ≡ a ∙ (b ∙ c)
  -- In terms of repr.emb: applying the ternary action of (a ⊙ b)
  -- at (idn, c) equals applying a's action at (idn, b ∙ c).
  -- noy q z r = repr.emb q _ refl z r = pcom refl q r = q ∙ r.
  -- So noy (a ⊙ b) z c = (a ⊙ b) ∙ c
  -- and noy a z (noy b z c) = a ∙ (b ∙ c) = noy a z (b ∙ c).
  -- These are related by ⊙-vs-∙ and Path.assoc.
  test-noy-composite
    : {w x y z : A} (a : w ≡ x) (b : x ≡ y) (c : y ≡ z)
    → (a ⊙ b) ∙ c ≡ a ∙ (b ∙ c)
  test-noy-composite a b c =
    ap (_∙ c) (⊙-vs-∙ a b) ∙ sym (Path.assoc a b c)

  -- Direct ternary action test:
  -- repr.emb (a ⊙ b) w refl z c
  --   = pcom refl (a ⊙ b) c = (a ⊙ b) ∙ c
  -- repr.emb a w refl x (repr.emb b x refl z c)
  --   = pcom refl a (pcom refl b c) = a ∙ (b ∙ c)
  test-emb-nested
    : {w x y z : A} (a : w ≡ x) (b : x ≡ y) (c : y ≡ z)
    → repr.emb (a ⊙ b) _ refl _ c
    ≡ repr.emb a _ refl _ (repr.emb b _ refl _ c)
  test-emb-nested a b c = test-noy-composite a b c

```

```agda
-- end
```
