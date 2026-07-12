# Pentagon and Triangle Coherence in Cat.Cat.Virtual

Lane Biocini — March 2026

A systematic analysis of the pentagon and triangle proofs in the
ternary-composition formulation of categories. The proofs derive all
Mac Lane coherences from three fields: `compose-contr`, `interchange`,
and (for the full triangle) `absorb-coh`.

---

## 1. The fiber method

The central technique: **coherence conditions between bracketings are
paths in contractible types, so they hold trivially; the real work is
identifying the abstract paths with the geometrically meaningful
ones.**

The pattern has three layers.

### Layer 1: Target functions

For any n-fold composite, define Eₙ as the "fully right-associated
noy-chain" — the canonical embedding behavior of the composite:

```
E₂(f,g)     = λ w a v b. emb f w a v (noy g v b)
E₃(f,g,h)   = λ w a v b. emb f w a v (noy g v (noy h v b))
E₄(f,g,h,k) = λ w a v b. emb f w a v (noy g v (noy h v (noy k v b)))
```

The outermost morphism f acts via `emb`; each subsequent morphism
extends rightward via `noy`. This is the "right-leaning comb" in tree
language — the canonical normal form for the n-fold composite.

### Layer 2: Contractible fibers

Show `fiber emb Eₙ` is contractible. Every bracketing of `f₁ ⨾ ⋯ ⨾ fₙ`
lives in this fiber (its `emb` equals Eₙ by iterated `emb-composite-pt`
and `noy-composite`). So all bracketings are identified as points in a
contractible type.

### Layer 3: Coherence for free

- `is-contr → is-prop`: any two bracketings are equal (associativity,
  unit laws)
- `is-contr → is-set`: any two *paths* between bracketings are equal
  (pentagon, triangle at the fiber level)

This is the HoTT incarnation of the classical insight: Mac Lane
coherence says all diagrams of structural isomorphisms commute, and
the contractibility of the emb-fiber *is* that coherence theorem
rendered type-theoretically. The contractible fiber doesn't prove
coherence — it **is** coherence.

### Connection to Capriotti-Kraus

The connection to Capriotti-Kraus's complete semi-Segal types is
structural. Their condition: the space of composition witnesses (horn
fillers) is contractible. Cat.Virtual's `compose-contr`: the space of
morphisms `s` with `emb s` equal to a prescribed target is
contractible. Same abstract condition, different encoding. The
difference: Capriotti-Kraus work simplicially (higher coherences come
for free from higher simplices); Cat.Virtual works algebraically
(higher coherences must be verified, but they all follow from the same
contractibility trick at progressively higher Eₙ levels).

---

## 2. The E₃ and E₄ targets

### Semantics

The chain `noy g v (noy h v (noy k v b))` represents *iterated
right-extension*. Since `noy f v b = emb f _ idn v b`:

```
noy k v b           = "extend b leftward through k"
noy h v (noy k v b) = "extend further leftward through h"
noy g v (⋯)         = "extend further leftward through g"
```

Then `emb f w a v (⋯)` attaches the outermost f with an arbitrary
left context a.

### Derivation of Eₙ-contr

The derivation is inductive. Starting from `composable-contr` (which
gives contractibility of `fiber emb E₂(f,g)` for any f, g):

**E₃-contr f g h:**
1. Start with `composable-contr (f ⨾ g) h` — contractibility of
   `fiber emb (λ w a v b. emb (f⨾g) w a v (noy h v b))`.
2. The gap between this target and `E₃ f g h` is bridged pointwise by
   `emb-composite-pt f g w a v (noy h v b)`.
3. `subst` along the funext of these equations transports
   contractibility.

**E₄-contr f g h k:**
1. Start from `composable-contr ((f⨾g)⨾h) k`.
2. The gap is bridged by two chained pointwise equalities:
   `emb-composite-pt (f⨾g) h` then `emb-composite-pt f g`.

The `subst` encodes the fact that contractibility of higher composites
is *derived* from contractibility of binary composites: the n-fold
target is the binary target with one argument further decomposed. Each
`emb-composite-pt` step peels off one layer of the left-associated
tree.

---

## 3. The pentagon

### 3.1 The five fiber points

The five points pt₁ – pt₅ in `fiber emb (E₄ f g h k)` correspond to
the five vertices of the Mac Lane pentagon:

| Point | Bracketing         | Proof chain reaches E₄ via                          |
|-------|--------------------|------------------------------------------------------|
| pt₁   | ((f⨾g)⨾h)⨾k       | emb-composite ×3, peeling left-to-right              |
| pt₂   | (f⨾(g⨾h))⨾k       | emb-composite ×2, then noy-composite g h             |
| pt₃   | f⨾((g⨾h)⨾k)       | emb-composite ×1, noy-composite (g⨾h) k, noy-composite g h |
| pt₄   | (f⨾g)⨾(h⨾k)       | emb-composite ×2, emb-composite-pt, noy-composite h k |
| pt₅   | f⨾(g⨾(h⨾k))       | emb-composite ×1, noy-composite g (h⨾k), noy-composite h k |

Each second component is a chain of path algebra: unfold `emb s` via
`emb-composite`, then adjust noy arguments via `noy-composite`, until
reaching E₄'s normal form. The second components differ in *how* they
reach E₄ — which order they peel off the composition layers. This
proof-relevant content makes the fiber approach work: the second
components carry enough information to distinguish geometrically
different paths through the pentagon.

### 3.2 The trivial fiber-level identity

```
σ₁₄ ∙ σ₄₅ ≡ σ₁₂ ∙ σ₂₃ ∙ σ₃₅
```

where σᵢⱼ = is-contr→is-prop E₄c ptᵢ ptⱼ. Proved by
`is-contr→is-set E₄c pt₁ pt₅`. Trivially inhabited because E₄-contr
is contractible, hence a set, so *all* paths between the same
endpoints are equal.

But this is not yet the Mac Lane pentagon. The σᵢⱼ are abstract (from
`is-contr→is-prop`); they have no a priori relation to `assoc`. The
face lemmas bridge this gap.

### 3.3 The face lemma pattern

Each face lemma establishes `αᵢⱼ ≡ [geometric operation]` where
αᵢⱼ = ap fst σᵢⱼ. The pattern:

1. **Construct a geometric path** γᵢⱼ-full : ptᵢ ≡ ptⱼ whose `ap fst`
   image is *by construction* the desired geometric operation (an
   associator or whiskered associator).

2. **Apply `total-contr-unique`** to conclude `ap fst σᵢⱼ = ap fst γᵢⱼ-full`.
   Since the fiber is contractible and both σᵢⱼ and γᵢⱼ-full are paths in it,
   their fst-projections must agree.

3. **Simplify using `ap-comp fst`** to distribute `ap fst` over
   `γᵢⱼ-full = wᵢ ∙ (λ i → γᵢⱼ-pt i) ∙ wⱼ`. The `wᵢ` and `wⱼ` are
   "bookkeeping" paths that are `refl` at the fst level (just
   reassociating proof chains). The geometric core `λ i → γᵢⱼ-pt i`
   carries the actual associator/whiskering. After distribution, we
   get `refl ∙ [desired] ∙ refl`, which collapses via `Path.unitl`
   and `Path.unitr`.

`ap-comp fst` is needed (rather than definitional distribution)
because the category record uses `no-eta-equality`.

### 3.4 The naturality square in face₁₄

Face₁₄ is harder than the other faces. The reason: σ₁₄ connects pt₁
and pt₄, which differ in both the *outer* bracketing (((f⨾g)⨾h)⨾k to
(f⨾g)⨾(h⨾k)) and the *inner* decomposition (the noy chain
rearranges).

The difficulty appears in the suffix w₁₄. The geometric path for
face₁₄ applies `assoc (f⨾g) h k`, but at the fiber level this means
`emb-composite-pt f g` is applied at two different arguments —
`noy (h⨾k) v b` versus `noy h v (noy k v b)` — connected by
`noy-composite h k b`. This produces a naturality square:

```
emb (f⨾g) w a v (noy (h⨾k) v b) ──emb-composite-pt f g──→ emb f w a v (noy g v (noy (h⨾k) v b))
         │                                                              │
         │ ap (emb (f⨾g) w a v) (noy-composite h k b)                  │ ap (… noy g v …) (noy-composite h k b)
         ↓                                                              ↓
emb (f⨾g) w a v (noy h v (noy k v b)) ─emb-composite-pt f g─→ emb f w a v (noy g v (noy h v (noy k v b)))
```

This commutes because `emb-composite-pt f g w a v` is functorially
indexed by its last argument. In cubical terms:

```
λ i j → emb-composite-pt f g w a v (noy-composite h k b i) j
```

fills the square. `Path.commutes` extracts the equation (w₁₄-nat):

```
ap (emb (f⨾g) w a v) (noy-composite h k b) ∙ emb-composite-pt f g w a v (noy h v (noy k v b))
≡ emb-composite-pt f g w a v (noy (h⨾k) v b) ∙ ap (λ t → emb f w a v (noy g v t)) (noy-composite h k b)
```

The other faces don't need this because their geometric cores only
vary one "coordinate" at a time — face₁₄ simultaneously varies an
inner argument and an outer composite.

### 3.5 Assembly

The final `pentagon` theorem:

```
assoc (f⨾g) h k ∙ assoc f g (h⨾k)
≡ ap (_⨾ k) (assoc f g h) ∙ assoc f (g⨾h) k ∙ ap (f ⨾_) (assoc g h k)
```

is obtained from `hom-identity : α₁₄ ∙ α₄₅ ≡ α₁₂ ∙ α₂₃ ∙ α₃₅` by
substituting the five face identifications:

| αᵢⱼ | Identified with              | Via     |
|------|------------------------------|---------|
| α₁₄ | assoc (f⨾g) h k             | face₁₄ |
| α₄₅ | assoc f g (h⨾k)             | face₄₅ |
| α₁₂ | ap (_⨾ k) (assoc f g h)     | face₁₂ |
| α₂₃ | assoc f (g⨾h) k             | face₂₃ |
| α₃₅ | ap (f ⨾_) (assoc g h k)     | face₃₅ |

`hom-identity` itself comes from the fiber-level `identity` by
distributing `ap fst` over the composites via `ap-comp fst`.

---

## 4. The triangle

### 4.1 The three fiber points

The triangle lives in `fiber emb E₂(f,g)`, which is
`composable-contr f g` — contractible.

| Point | Bracketing   | Proof chain                                     |
|-------|--------------|-------------------------------------------------|
| pt₁   | (f⨾idn)⨾g   | emb-composite ×2, emb-composite-pt f idn, ap … absorb-l |
| pt₂   | f⨾(idn⨾g)   | emb-composite ×1, ap … noy-composite idn g, ap … absorb-l |
| pt₃   | f⨾g          | emb-composite f g (the center of composable-contr) |

Both pt₁ and pt₂ reach E₂(f,g) by first expanding their composite,
then canceling the introduced identity via absorption.

### 4.2 The weak triangle

```
ap (_⨾ g) (unitr f) ≡ assoc f idn g ∙ α₂₃
```

where α₂₃ = ap fst σ₂₃ is abstract. Proved by the same fiber
pattern: derive `hom-identity : α₁₃ ≡ α₁₂ ∙ α₂₃`, identify α₁₃
with `ap (_⨾ g) (unitr f)` via face₁₃, identify α₁₂ with
`assoc f idn g` via face₁₂, substitute.

This needs only `absorb-l` (which enters the proof chains of pt₁ and
pt₂). No coherence between `absorb-l` and `absorb-r` is required.

### 4.3 What absorb-coh says

`absorb-coh` states:

```
absorb-l (noy f v b)
  ≡ interchange idn f _ idn v b ∙ ap (λ t → emb f _ t v b) (absorb-r idn)
```

The two ways of eliminating a redundant identity from a ternary
composition agree:

- **(Left absorption)** Notice idn acts trivially on the left: `absorb-l`
- **(Interchange + right absorption)** Swap viewpoints (noy → yon via
  interchange), then notice idn acts trivially on the right: `absorb-r`

This is a coherence condition between the two absorption paths — the
two "proofs that idn is neutral" are compatible when composed through
interchange. It is exactly the kind of 2-cell coherence that
separates a bicategory from a strict 2-category.

### 4.4 absorb-l-noy-retract

The key lemma:

```
emb-noy f _ idn v b ∙ absorb-l (noy f v b) ≡ refl
```

The path `emb-noy` decomposes as
`ap (emb f _ _ v b) (sym (absorb-r idn)) ∙ sym (interchange idn f …)`.
Using `absorb-coh` to expand the second factor, the composite becomes
`(sym B ∙ sym A) ∙ (A ∙ B) = refl` by groupoid cancellation. The
cancellation is exact because `absorb-coh` identifies the two
absorption paths precisely.

This retraction is the engine that identifies α₂₃ with
`ap (f ⨾_) (unitl g)`. The geometric path γ₂₃-full for the full
triangle has an intermediate step v₁ that uses
`absorb-l-noy-retract` to collapse a residual path to refl.

### 4.5 The gap

The gap between weak and full Mac Lane triangle is precisely the
identification of α₂₃:

- **Weak**: `ap (_⨾ g) (unitr f) ≡ assoc f idn g ∙ α₂₃` where α₂₃
  is an abstract fiber projection. Provable from base axioms alone.
- **Full**: `ap (_⨾ g) (unitr f) ≡ assoc f idn g ∙ ap (f ⨾_) (unitl g)`.
  Requires `absorb-coh`.

The reason: `unitl g` is defined via `composable-contr idn g`, while
α₂₃ is defined via `composable-contr f g`. These are *different*
contractible fibers. The face₂₃ proof must build a path in
`composable-contr f g` whose fst-projection is `ap (f ⨾_) (unitl g)`,
and this requires knowing how `absorb-l` decomposes through
interchange — which is exactly `absorb-coh`.

The `2-coherent` record encapsulates this: it is the *one additional
2-cell* needed to turn the weak bicategorical structure into a genuine
bicategory. Pentagon is free from contractibility; triangle requires
one explicit coherence datum connecting the two absorption laws.

---

## 5. Comparison with other approaches

### Sterling's virtual bicategories

Sterling formulates virtual bicategories where composition is
witnessed by cells in a virtual double category. The structural
parallel: both approaches characterize the composite by its universal
property rather than defining it as a function and proving properties.

Where Sterling has opcartesian cells, Cat.Virtual has fiber
contractibility. The `emb` function plays the role of the virtual
composition cell — it encodes how a morphism "acts" on a composable
pair, and `compose-contr` says this action has a contractible space of
lifts. The pentagon and triangle proofs have the same conceptual
engine: coherences hold because the relevant "space of witnesses" is
contractible. The mechanisms differ (double-categorical reasoning vs.
path algebra in contractible fibers).

### Classical Mac Lane coherence

The standard proof goes through strictification: every monoidal
category is monoidally equivalent to a strict one where all structural
maps are identities.

Cat.Virtual provides a genuinely different proof. Instead of
strictification:

1. All bracketings of a given composite are points in a contractible type.
2. All paths between bracketings are paths in a set (is-contr → is-set).
3. Therefore all path equations (coherences) hold.

This avoids the detour through strict categories entirely and
illuminates something the classical proof obscures: **coherence is not
a property of the structural maps, but of the space of
compositions.** The classical proof works because that space *happens
to be* contractible, encoded indirectly via the equivalence to a
strict category. Cat.Virtual makes the contractibility explicit and
primary.

One revelation: pentagon is "more free" than triangle. Any coherence
statable as a path equation in an Eₙ fiber holds by the same
is-contr→is-set argument. The triangle is harder because it connects
two *different* contractibility witnesses (for left and right unit),
and the coherence between these witnesses is not derivable from their
individual contractibility.

### Capriotti-Kraus univalent higher categories

Complete semi-Segal types: composition is a contractible choice of
horn fillers. Cat.Virtual: composition is a contractible fiber of emb.
Same abstract condition, different encoding.

Key difference: Capriotti-Kraus include univalence (type of
isomorphisms ≃ paths between objects). Cat.Virtual deliberately does
not — it gives wild/untruncated categories where hom types have
arbitrary homotopical content.

---

## 6. The squaring effect

Cat.Virtual's identity is defined by `unit`, which provides
`idn : hom x x` with:

- Equivalences: `λ h → emb e x e z h` and `λ g → emb e w g x e` are equivalences
- Idempotency: `emb e x e z (emb e x e z h) ≡ emb e x e z h` (and dual)

Absorption `absorb-l h : emb e x e z h ≡ h` is derived by applying
`equiv→lc` (injectivity of equivalences) to the idempotency equation:
if φ(φ(h)) = φ(h) and φ is injective, then φ(h) = h.

The ternary absorption condition `emb e x e z h ≡ h` involves `e`
**twice**: it says `e ∙ e ∙ h = h` in path groupoids, i.e., `e² = 1`.
This is quadratic in `e`. It detects involutions, not identities.

**Counterexample**: In K(ℤ/2, 1) (= RP^∞), the generator `gen` has
`gen ∙ gen = refl` but `gen ≠ refl`. This `gen` satisfies all
Cat.Virtual unit conditions:

- `gen ∙ gen ∙ h = h` (since gen² = refl) ✓
- `λ h → gen ∙ gen ∙ h` is an equivalence (it's the identity) ✓
- Idempotency: `gen ∙ gen ∙ (gen ∙ gen ∙ h) = gen ∙ gen ∙ h` ✓
- But `gen ≠ refl` ✗

So `unit-is-prop` fails: there are at least two distinct units.
Consequently `idn-contr` cannot be derived from the base axioms, and
`idn-ind` (elimination over arbitrary unit data) is unavailable in
Cat.Virtual.

VirtualAlt's binary formulation `noy e z f ≡ f` (where e appears
once) avoids this: `e ∙ f = f` directly implies `e = refl`. This is
why VirtualAlt may eventually subsume Cat.Virtual.

---

## Summary: proof architecture

| Layer                    | What it provides                        | Mechanism                              |
|--------------------------|-----------------------------------------|----------------------------------------|
| Base axioms              | emb, unit, compose-contr, interchange   | Raw data                               |
| Contractible fibers      | Eₙ-contr, emb-image-contr              | subst along pointwise expansion chains |
| Hom-level identities     | unitl, unitr, assoc                     | ap fst of is-contr→is-prop             |
| Fiber-level coherences   | pentagon identity, triangle identity    | is-contr→is-set (trivially inhabited)  |
| Face lemmas              | Identify αᵢⱼ with geometric operations | total-contr-unique + ap-comp fst       |
| Hom-level coherences     | Mac Lane pentagon, Mac Lane triangle    | Substitution of face identifications   |
| 2-coherence              | absorb-coh                              | Separate axiom (2-coherent record)     |

The pattern generalizes: any coherence condition statable as a path
equation in an Eₙ fiber holds trivially. The work is always in the
face lemmas — identifying the abstract fiber projections with the
geometrically meaningful maps. This is where naturality squares,
`ap-comp` distribution, and (for the triangle) the `absorb-coh` datum
do their work.
