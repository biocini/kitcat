# Research: Rezk Completion Retraction for Virtual ∞-Groupoids

## The Library: Synthetic Category Theory Internal to HoTT

Kitcat is a Cubical Agda library doing formal category theory
internal to homotopy type theory. Categories are defined via
ternary composition (`emb`) with contractible composition fibers.
The key design: contractibility gives associativity, unit laws,
pentagon, and triangle for free — as projections from contractible
types. No truncation assumptions on hom types.

The formal category theory is done internal to HoTT —
contractibility, equivalences, fibers, and h-levels are the
native vocabulary for categorical notions. The native notion of
"these compose to that" is the emb-level composite witness
(`_⨾_=>_`), not bare path equality.

---

## The Category Record (`Cat.Virtual`)

```agda
record category o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    emb : ∀ {x y} → hom x y
        → ∀ w → hom w x → ∀ z → hom y z → hom w z
    unit : ∀ {x} →
      Σ e ∶ hom x x
      , ( (∀ {z} → is-equiv (λ (h : hom x z) → emb e x e z h))
        × (∀ {w} → is-equiv (λ (g : hom w x) → emb e w g x e)))
      × (emb e x e x e ≡ e)

  idn : ∀ {x} → hom x x
  idn = unit .fst

  noy : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  noy f z h = emb f _ idn z h

  yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
  yon f w g = emb f w g _ idn

  field
    compose-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr
          (Σ s ∶ hom x z
          , emb s ≡ (λ w a v b → emb f w a v (noy g v b)))
    interchange
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        w (a : hom w x) v (b : hom z v)
      → emb f w a v (noy g v b) ≡ emb g w (yon f w a) v b
    yon-eval
      : ∀ {x y} (f : hom x y) → yon f x idn ≡ f

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = compose-contr f g .center .fst

  emb-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g) ≡ (λ w a v b → emb f w a v (noy g v b))
  emb-composite f g = compose-contr f g .center .snd
```

`emb f w a z b` is ternary composition: given `f : x → y`,
context morphisms `a : w → x` and `b : y → z`, produce `w → z`.
Binary composition `f ⨾ g` is the unique `s` whose `emb s`
matches the noy-composite target (from `compose-contr`).

## Derived Operations (`module Virtual`)

All derived from the fields above — no additional axioms.

```agda
module Virtual {o} {h} (C : category o h) where
  open category C public

  -- Pointwise emb-composite
  emb-composite-pt : emb (f ⨾ g) w a v b ≡ emb f w a v (noy g v b)
  emb-composite-pt f g w a v b i = emb-composite f g i w a v b

  -- Composite characterizations via noy and yon
  noy-composite : noy (g ⨾ h) v b ≡ noy g v (noy h v b)
  noy-composite g h b i = emb-composite g h i _ idn _ b

  yon-composite : yon (f ⨾ g) w a ≡ yon g w (yon f w a)
  yon-composite f g w a = emb-composite-pt f g w a _ idn ∙ interchange f g w a _ idn

  -- Composition equals yon-action
  comp-eq : f ⨾ g ≡ yon g _ f
  comp-eq f g = sym (yon-eval (f ⨾ g)) ∙ yon-composite f g _ idn ∙ ap (yon g _) (yon-eval f)

  -- Identity is idempotent
  idem : idn ⨾ idn ≡ idn
  idem = comp-eq idn idn ∙ yon-idpt

  -- Absorption laws (derived from idem + equiv→lc)
  absorb-l : noy idn z h ≡ h
  absorb-l h = equiv→lc unit-eqvl (sym (subst ... idem (noy-composite idn idn h)))

  absorb-r : yon idn w g ≡ g
  absorb-r g = equiv→lc unit-eqvr (sym (subst ... idem (yon-composite idn idn _ g)))

  -- emb is an embedding (contractible image fibers)
  emb-image-contr : ∀ (f : hom x y) → is-contr (Σ g, emb g ≡ emb f)
  emb-image-contr f = subst (is-contr ∘ fiber emb) path (composable-contr idn f)
    where path = emb-ext λ w a v b → interchange idn f w a v b ∙ ap (λ t → emb f w t v b) (absorb-r a)

  emb-inj : emb f ≡ emb g → f ≡ g
  emb-inj p = emb-image-ind f (λ n _ → f ≡ n) refl g (sym p)

  -- Unit laws from contractible fibers (as ap fst of fiber paths)
  unitr : f ⨾ idn ≡ f
  unitr f = ap fst (is-contr→is-prop (emb-image-contr f)
    (f ⨾ idn , emb-composite f idn ∙ emb-ext λ w a v b → ap (emb f w a v) (absorb-l b))
    (f , refl))

  unitl : idn ⨾ f ≡ f
  unitl f = ap fst (is-contr→is-prop (composable-contr idn f)
    (idn ⨾ f , emb-composite idn f)
    (f , emb-ext λ w a v b → emb-noy f w a v b))

  -- Associativity from E₃-contr (contractible triple-composition fiber)
  assoc : (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h = ap fst (is-contr→is-prop (E₃-contr f g h) lhs rhs)

  -- Identity uniqueness
  unit-is-prop : (e : hom x x) → (equivs) → (yon-idpt) → e ≡ idn
```

## Neutrality and Functors (`Cat.Base`)

```agda
module Cat {o h} (C : category o h) where
  open Virtual C

  is-neutral : hom x y → Type (o ⊔ h)
  is-neutral f = (∀ {z} → is-equiv (λ h → f ⨾ h)) × (∀ {w} → is-equiv (λ g → g ⨾ f))

  idn-is-neutral : is-neutral idn
  idempotent-neutral→idn : is-neutral e → e ⨾ e ≡ e → e ≡ idn

record functor (C D : category o h) where
  field
    map  : C.ob → D.ob
    hmap : C.hom x y → D.hom (map x) (map y)
    preserves-comp    : hmap (f ⨾ g) ≡ hmap f ⨾ hmap g
    preserves-neutral : is-neutral f → is-neutral (hmap f)
  -- Derived: hmap-idn : hmap idn ≡ idn
```

## Path Groupoid Instance (`Cat.Groupoid`)

For any type A (no truncation), the path groupoid is a category:

```agda
module _ {u} (A : Type u) where
  private
    E : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
    E = yon-unbiased.emb {A = λ _ → A}   -- E f w a v b = pcom (sym a) f b

    E-equiv : is-equiv E                  -- from Core.Groupoid.repr.emb-equiv

  ∞-groupoid : category u u
  ∞-groupoid .category.ob = A
  ∞-groupoid .category.hom = _≡_
  ∞-groupoid .category.emb = E
  ∞-groupoid .category.unit = gpd-unit    -- (refl, (equivs, pcom.unit refl))
  ∞-groupoid .category.compose-contr f g = eqv-fibers E-equiv (noy-target f g)
  ∞-groupoid .category.interchange = gpd-interchange   -- pcom-split-l/r
  ∞-groupoid .category.yon-eval f = pcom.unit f         -- pcom refl f refl ≡ f
```

## The Rezk Completion (`Cat.Rezk`) — Current State

### The HIT (4 constructors, no truncation)

```agda
{-# OPTIONS --cubical --safe --no-guardedness #-}

module _ {o h} (C : category o h) where
  private module C = Virtual C
  open Cat C using (is-neutral)

  is-∞-groupoid : Type (o ⊔ h)
  is-∞-groupoid = ∀ {x y} (f : C.hom x y) → is-neutral f

  module _ (gpd : is-∞-groupoid) where
    data Rezk : Type (o ⊔ h) where
      q    : C.ob → Rezk
      seg  : ∀ {x y} → C.hom x y → q x ≡ q y
      seg∙ : ∀ {x y z} (f : C.hom x y) (g : C.hom y z)
           → seg (f C.⨾ g) ≡ seg f ∙ seg g
      seg₁ : ∀ {x} → seg (C.idn {x}) ≡ refl
```

### The Code Fibration (complete)

```agda
    module _ (x₀ : C.ob) where
      private
        -- Post-composition with neutral g is an equivalence
        post-equiv : C.hom y z → C.hom x₀ y ≃ C.hom x₀ z
        post-equiv g = (C._⨾ g) , gpd g .snd

        -- Functoriality: post-equiv respects composition
        post-equiv-comp : post-equiv (f C.⨾ g) ≡ post-equiv f ∙e post-equiv g
        post-equiv-comp f g = equiv-path _ _ (funext λ a → sym (C.assoc a f g))

        -- Identity: post-equiv idn ≡ aut (identity equivalence)
        post-equiv-idn : post-equiv C.idn ≡ aut
        post-equiv-idn = equiv-path _ _ (funext λ a → C.unitr a)

        -- 2-cells for the HIT's path-between-path constructors
        ua-comp-square : ua (post-equiv (f C.⨾ g)) ≡ ua (post-equiv f) ∙ ua (post-equiv g)
        ua-comp-square f g = ap ua (post-equiv-comp f g) ∙ ua-∙e (post-equiv f) (post-equiv g)

        ua-idn-square : ua (post-equiv C.idn) ≡ refl
        ua-idn-square = ap ua post-equiv-idn ∙ ua-id

      -- Code maps Rezk to Type, sending q y to hom x₀ y
      Code : Rezk → Type h
      Code (q y) = C.hom x₀ y
      Code (seg g i) = ua (post-equiv g) i
      Code (seg∙ f g i j) = ua-comp-square f g i j
      Code (seg₁ {x} i j) = ua-idn-square {x} i j
```

### Encode, Decode, and Section (complete)

```agda
      encode : q x₀ ≡ q y → C.hom x₀ y
      encode p = subst Code p C.idn

      decode : C.hom x₀ y → q x₀ ≡ q y
      decode f = seg f

      -- Section: encode (decode f) ≡ f
      section : encode (decode f) ≡ f
      section f = ua-β (post-equiv f) C.idn ∙ C.unitl f
      -- transport (ua (_⨾ f)) idn = idn ⨾ f = f
```

### What's Missing: The Retraction

Need: `∀ {y} (p : q x₀ ≡ q y) → decode (encode p) ≡ p`

## The Retraction Problem

### Approach 1: J-induction

Path induction on `p : q x₀ ≡ q y`:

```
J (λ y p → decode (encode p) ≡ p) base-case
```

Base case: `decode (encode refl) ≡ refl`

```
decode (encode refl)
  = decode (subst Code refl idn)
  = decode (transport refl idn)
  = decode idn              -- by transport-refl
  = seg idn                 -- by definition of decode
  ≡ refl                    -- by seg₁
```

The question: does this J-induction produce a well-typed
term in Cubical Agda? J works on paths in ANY type,
including HITs. But `encode` uses `subst Code p idn`,
where `Code` is defined by Rezk-elimination. When `p`
is not a constructor path, `encode p` is an opaque
`transport`. J-induction on `p` gives the base case
where `p = refl`, and `encode refl` reduces to
`transport refl idn = idn`. So the base case works.

But does the J computation produce terms that interact
correctly with the HIT's higher constructors? In Cubical
Agda, J is `transport` in the identity type, which uses
`hcom` and `transp`. These should compose correctly with
the HIT's `Code`, which uses `Glue` types for the `seg`
case. The question is whether any normalization/reduction
issues arise.

### Approach 2: Generalized decode by Rezk-elimination

Define `decode-gen : (z : Rezk) → Code z → q x₀ ≡ z` by
pattern matching on `z : Rezk`:

```
decode-gen (q y) f = seg f
decode-gen (seg g i) = ???  -- PathP obligation
decode-gen (seg∙ f g i j) = ??? -- 3-cube obligation
decode-gen (seg₁ i j) = ??? -- 3-cube obligation
```

The `seg` case requires:
```
PathP (λ i → ua (post-equiv g) i → q x₀ ≡ seg g i)
  (λ f → seg f)    -- at i=0: hom x₀ y → q x₀ ≡ q y
  (λ f → seg f)    -- at i=1: hom x₀ z → q x₀ ≡ q z
```

The intermediate type `ua (post-equiv g) i` is a Glue type.
At `i = 0` it's `hom x₀ y`, at `i = 1` it's `hom x₀ z`.
Transporting a function `λ f → seg f` introduces
`transport⁻¹` at the input, giving `λ f → seg ((_⨾ g)⁻¹ f)`
at `i = 1`, which ≠ `λ f → seg f` definitionally.

### Approach 3: Use `seg∙` to fix the boundary

At `i = 1`, we need `seg f`, but transport gives
`seg ((_⨾ g)⁻¹ f)`. These are related by:
```
seg ((_⨾ g)⁻¹ f) ∙ seg g ≡ seg ((_⨾ g)⁻¹ f ⨾ g) ≡ seg f
```
using `seg∙` and the retraction `(_⨾ g)⁻¹ f ⨾ g ≡ f`
(from the equivalence counit).

This gives a propositional fix at the boundary, but the
generalized decode needs a DEFINITIONAL match. The
propositional fix must be absorbed into the path using
`hcom` or a connection argument.

## Related Problem: Cat.Slice dep-fill

The slice category C/X has `hom/X (A, fA) (B, fB) = Σ k, k ⨾ fB ≡ fA`.
Constructing paths in this Sigma requires `PathP` for the
commuting witness — the same dep-fill problem. Three approaches:

1. **emb-section**: Prove `emb-inj (ap emb p) ≡ p` in Cat.Virtual,
   enabling conversion between emb-level (set-like) and hom-level paths.
2. **Reformulate emb/X**: Define the slice's emb so witnesses
   compose coherently with emb-composite-pt.
3. **Direct path algebra**: Verify each chain manually.

## Key Infrastructure Available

From `Core.Kan`:
- `pcom`, `pfil`, `hcom`, `hfil` — path composition primitives
- `is-contr→is-prop`, `is-contr→is-set` — h-level lemmas
- `Σ-contr-contr`, `TotalP`, `total-contr-unique`
- `contr-face` — ap-fst extraction over contractible Σ
- `Path.unitl/r`, `Path.invl/r`, `Path.assoc`, `Path.grp-cancel`

From `Core.Univalence`:
- `ua`, `ua-β`, `ua-η` — univalence
- `ua-∙e` — ua respects equivalence composition
- `ua-id` — ua of identity equivalence is refl

From `Core.Equiv`:
- `is-equiv`, `iso→equiv`, `equiv-path`
- `is-equiv-is-prop` — is-equiv is propositional
- `Equiv.fwd`, `Equiv.inv`, `Equiv.unit`, `Equiv.counit`

From `Core.Transport`:
- `subst`, `transport-refl`, `contr-ind`, `coe01`
- `SinglP-contr` — reversed singleton contractibility

## References

- Rijke, "Introduction to HoTT" — Ch 5 (identity systems),
  Ch 11 (fundamental theorem), Ch 17 (univalence)
- Capriotti-Kraus, arXiv:1707.03693 — univalent higher categories
- Ahrens-Kapulkin-Shulman — Rezk completion for 1-categories
- Sterling, jonmsterling.com/005B — virtual bicategory theory
- 1lab, Cat.Instances.Delooping — delooping HIT with squash
- Cavallo 2024 — parametric cubical type theory
