# Equivalences and contractibility

The equivalence relation on types: `A ≃ B` is the type of **bi-invertible
maps** `A → B`. Everything is built on **homotopies**
`f ~ g := Π (x:A). f x = g x` — pointwise identifications, the only notion of
sameness of functions available without funext. The second half introduces
**contractibility** ("exactly one element, up to identification") and the
payoff theorem: a map is an equivalence iff all its fibers are contractible.
That characterization is what makes equivalences usable in practice (it powers
the fundamental theorem of identity types, univalence, and truncation levels).

Two design constraints shape every definition below:

- Functions are compared *pointwise*. Judgmental equality of functions is
  rare, and `f = g` is unprovable in pure type theory even when `f ~ g` holds
  (funext closes this gap; see funext.md).
- `is-equiv f` must be a **property** of `f`, not structure on it — this is
  provable once funext is available (funext.md, truncation-levels.md), and it
  forces the bi-invertible definition over the naive quasi-inverse one.

## Key definitions

### Homotopies

For dependent functions `f g : Π (x:A). B x`:

```
f ~ g  :=  Π (x:A). f x = g x
```

Motivating example (`neg-bool`). Type theory provides **no** means to prove
`neg-bool ∘ neg-bool = id` — not judgmentally (the two sides agree only after
case analysis on the input) and not as an identity type (pre-funext). What
*is* constructible, by `bool`-induction, is the pointwise version:

```
neg-neg-bool : neg-bool ∘ neg-bool ~ id
neg-neg-bool true  := refl true
neg-neg-bool false := refl false
```

This is the general pattern: pointwise identifications are cheap (induction on
the domain), identifications of functions are not. Homotopies are the
prevalent notion of sameness of maps.

**Commutative diagrams.** A triangle with `h : A → B`, `g : B → X`, `f : A → X`
*commutes* when equipped with a homotopy `H : f ~ g ∘ h`. A square with
`f : A → B`, `g : A → A'`, `f' : A' → B'`, `h : B → B'` commutes when equipped
with `h ∘ f ~ f' ∘ g`. "Commutes" always means *equipped with a homotopy* —
the homotopy is data, not an annotation.

**Iterated homotopies.** Since `f ~ g` is itself a Π-type, homotopies between
homotopies `H K : f ~ g` make sense: `H ~ K := Π (x:A). H x = K x`, and so on
upwards. Coherence conditions (e.g. for contractible maps below) live one
level up.

### Groupoid structure on homotopies

Defined pointwise from the path groupoid (see identity-types.md):

```
refl-htpy f  : f ~ f                       refl-htpy f  := λx. refl (f x)
H⁻¹          : g ~ f     (for H : f ~ g)   H⁻¹          := λx. (H x)⁻¹
H ∙ K        : f ~ h     (for K : g ~ h)   H ∙ K        := λx. H x ∙ K x
```

(`∙` is diagram-order: first `H`, then `K`.) The groupoid laws hold **up to
homotopy** — never judgmentally, and (pre-funext) not as identifications:

```
assoc-htpy H K L  : (H ∙ K) ∙ L ~ H ∙ (K ∙ L)
left-unit-htpy H  : refl-htpy f ∙ H ~ H
right-unit-htpy H : H ∙ refl-htpy g ~ H
left-inv-htpy H   : H⁻¹ ∙ H ~ refl-htpy g
right-inv-htpy H  : H ∙ H⁻¹ ~ refl-htpy f
```

Each is constructed pointwise from the corresponding path law, e.g.
`assoc-htpy H K L x := assoc (H x) (K x) (L x)`.

### Whiskering

Composing a homotopy with a function on either side:

```
h · H  :=  λx. ap h (H x)  :  h ∘ f ~ h ∘ g    (H : f ~ g,  f g : A → B,  h : B → C)
H · f  :=  λx. H (f x)     :  g ∘ f ~ h ∘ f    (H : g ~ h,  g h : B → C,  f : A → B)
```

Left whiskering `h · H` uses `ap` (the function acts on the path); right
whiskering `H · f` is precomposition of the homotopy's argument.

### Naturality of homotopies

For `H : f ~ g` (with `f g : A → B`) and `p : x = y`, the **naturality
square**

```
         H x
  f x ────────→ g x
   │             │
ap f p         ap g p
   ↓             ↓
  f y ────────→ g y
         H y
```

commutes, witnessed by

```
nat-htpy H p : ap f p ∙ H y = H x ∙ ap g p
```

Construction: path induction on `p`. At `refl x`, both sides reduce to
`H x` versus `H x ∙ refl (g x)` — precisely `(right-unit (H x))⁻¹`.

**Consequence (retraction-swap).** For `f : A → A` and `H : f ~ id`:

```
H (f x) = ap f (H x)
```

Apply naturality of `H` at the path `H x : f x = x`, use `ap id (H x) = H x`,
and cancel the right factor `H x` (legal: `concat' (H x) := λp. p ∙ H x` is an
equivalence). This identification is the workhorse inside the coherence
proofs for equivalences.

### Sections, retractions, equivalences

For `f : A → B`:

```
sec f       :=  Σ (g : B → A). f ∘ g ~ id     -- right inverses
retr f      :=  Σ (h : B → A). h ∘ f ~ id     -- left inverses
is-equiv f  :=  sec f × retr f
A ≃ B       :=  Σ (f : A → B). is-equiv f
```

An equivalence is a **bi-invertible map**: it carries a *separate* right
inverse and left inverse, not one map with both homotopies. The **inverse**
`e⁻¹` of `e : A ≃ B` is *defined* as the section of `e` (which is also a
retraction, by the proposition below). If `f` has a retraction, `A` is called
a **retract** of `B`.

**Why not a single quasi-inverse?** The naive notion

```
has-inverse f  :=  Σ (g : B → A). (f ∘ g ~ id) × (g ∘ f ~ id)
```

is the wrong definition of `is-equiv`: `has-inverse f` is homotopically
complicated — later one shows `has-inverse (id : S¹ → S¹) ≃ ℤ` (circle.md) —
so it can never be a proposition. But "being an equivalence" must be a
proposition if equivalences are to behave like identifications (univalence).
Nevertheless there are maps both ways:

- `has-inverse f → is-equiv f`: immediate (split the homotopies). **This is
  the direction used to prove something is an equivalence.**
- `is-equiv f → has-inverse f`: from section `(g, G)` and retraction
  `(h, H)`, first identify the two inverses:
  `K := (H · g)⁻¹ ∙ (h · G) : g ~ h` (at `y : B`: `g y ← h (f (g y)) → h y`);
  then `g` is also a left inverse via `g (f x) —K (f x)→ h (f x) —H x→ x`.

### Contractible types

```
is-contr A  :=  Σ (c : A). Π (x:A). c = x
```

The first component `c` is the **center of contraction**; the second `C` is
the **contraction**. Note `C : const c ~ id` — a contraction is literally a
homotopy from the constant map at `c` to the identity. A contractible type is
a "singleton up to homotopy".

**Singleton induction.** A pointed type `(A, a)` satisfies **singleton
induction** if for every family `B` over `A` the evaluation map

```
ev-pt : (Π (x:A). B x) → B a,    ev-pt f := f a
```

has a section; i.e. there are

```
ind-sing a  : B a → Π (x:A). B x
comp-sing a : ev-pt ∘ ind-sing a ~ id
```

— to define a dependent map out of `A` it suffices to give its value at `a`,
and the computation rule holds *up to identification* (contrast `𝟏`, whose
induction principle computes judgmentally; `𝟏` therefore satisfies singleton
induction via `λb. refl b`).

### Fibers and contractible maps

For `f : A → B` and `b : B`, the **(homotopy) fiber** of `f` at `b` is

```
fib f b  :=  Σ (a : A). f a = b
```

— the type-theoretic preimage: elements mapping to `b`, each equipped with
the witness. Identity types of fibers are characterized by

```
Eq-fib f ((x,p),(x',p'))  :=  Σ (α : x = x'). p = ap f α ∙ p'
```

and the canonical map `((x,p) = (x',p')) → Eq-fib f ((x,p),(x',p'))` (from
reflexivity `λ(x,p). (refl x, refl p)`, by path induction) is an equivalence.
So: to identify two fiber elements, give a base path plus a filler of the
triangle over `b`.

A map is **contractible** when every fiber is contractible:

```
is-contr-map f  :=  Π (b:B). is-contr (fib f b)
```

This is the type-theoretic analogue of "bijective": every preimage has exactly
one element, up to identification.

**Coherently invertible maps** (a technical waypoint). `f` is coherently
invertible if it comes equipped with

```
g : B → A,   G : f ∘ g ~ id,   H : g ∘ f ~ id,   K : G · f ~ f · H
```

(`G · f` and `f · H` both have type `f ∘ g ∘ f ~ f`; `K` is the coherence.)
Write `is-coh-invertible f` for the type of such quadruples.

## Key results

### Basic examples of equivalences

- `id : A → A` is an equivalence (its own section and retraction).
- `neg-bool : bool → bool` is an equivalence (`neg-neg-bool` serves as both
  homotopies).
- On `ℤ`: `succ-ℤ`, `pred-ℤ`, `x ↦ x + k` (for each `k : ℤ`), and `x ↦ −x`
  are equivalences (from the group laws). Similarly `succ-Fin`, `pred-Fin`,
  `add-Fin k`, `neg-Fin` on `Fin k`.
- Path-algebra operations are equivalences, with explicit inverses:
  `inv : (x = y) → (y = x)`, inverse `inv`;
  `concat p : (y = z) → (x = z)`, inverse `concat (p⁻¹)`;
  `concat' q : (x = y) → (x = z)` where `concat' q p := p ∙ q`, inverse
  `concat' (q⁻¹)`;
  `tr B p : B x → B y`, inverse `tr B (p⁻¹)`.
- Non-examples: `const b : bool → bool` is never an equivalence (needs
  `true ≠ false`; see inductive-types.md); `bool ≄ 𝟏`; `ℕ ≄ Fin k`.

### Inverses of equivalences

- **The inverse of an equivalence is an equivalence.** The section of `e` is
  also a retraction (via `is-equiv f → has-inverse f`), hence itself an
  equivalence with inverse `e`.
- Any section and any retraction *of an equivalence* is again an equivalence
  (a corollary of 3-for-2 below).

### Closure of equivalences under homotopy

If `H : f ~ g`, then `is-equiv f ↔ is-equiv g`. Explicitly, transport the
homotopies: a section `(s, S)` of `f` yields the section
`(s, (H · s)⁻¹ ∙ S)` of `g`, and a retraction `(r, R)` of `f` yields the
retraction `(r, (r · H)⁻¹ ∙ R)` of `g`. So one may always replace a map by a
homotopic, better-behaved one before proving it is an equivalence. Homotopic
equivalences also have homotopic inverses.

### 3-for-2 property of equivalences

Given a commuting triangle `H : f ~ g ∘ h` (with `h : A → B`, `g : B → X`,
`f : A → X`): **if any two of `f`, `g`, `h` are equivalences, so is the
third.** Proof shape: if `h` has a section `s : B → A`, the reflected
triangle (maps `s`, `f`, `g`) commutes and `f` has a section iff `g` does;
dually, a retraction of `g` lets one trade retractions between `f` and `h`.
Consequences: equivalences are closed under composition and under "division"
on either side; sections and retractions of equivalences are equivalences.

### Identity types of Σ-types (the model characterization)

For `s t : Σ (x:A). B x`:

```
Eq-Σ s t  :=  Σ (α : pr₁ s = pr₁ t). tr B α (pr₂ s) = pr₂ t
```

Then `pair-eq : (s = t) → Eq-Σ s t` — defined by path induction from
`reflexive-Eq-Σ (x,y) := (refl x, refl y)` — is an equivalence. Its inverse
`eq-pair` is built by Σ-induction then double path induction
(`eq-pair (refl x, refl y) := refl (x,y)`); both homotopies are discharged by
induction since everything computes on `refl`.

General workflow for characterizing identity types: (1) define a relation
`R` intended to be equivalent to `=`; (2) show `R` is reflexive; (3) get the
canonical map `(x = y) → R x y` by path induction; (4) show it is an
equivalence. Step (4) is the hard one — the fundamental theorem
(fundamental-theorem.md) exists to streamline it.

### Algebraic laws as equivalences

Unit/zero/commutativity/associativity/distributivity of `×` and `+`, and the
Σ-versions, are all equivalences, constructed by pattern matching (maps and
homotopies defined by induction; homotopies are `refl` after case splits):

```
𝟘 + B ≃ B        A + 𝟘 ≃ A        A + B ≃ B + A      (A + B) + C ≃ A + (B + C)
𝟘 × B ≃ 𝟘        A × 𝟘 ≃ 𝟘        𝟏 × B ≃ B          A × 𝟏 ≃ A
A × B ≃ B × A    (A × B) × C ≃ A × (B × C)
A × (B + C) ≃ (A × B) + (A × C)    (A + B) × C ≃ (A × C) + (B × C)
Σ (x:𝟘). B x ≃ 𝟘   Σ (x:A). 𝟘 ≃ 𝟘   Σ (x:𝟏). B x ≃ B ⋆   Σ (x:A). 𝟏 ≃ A
```

Σ has two associativity forms (currying between `Σ (w : Σ (x:A). B x). C w`
and `Σ (x:A). Σ (y:B x). C (x,y)`) and distributes over `+`, but has **no
commutativity** (the fibers vary). Non-dependent swap:
`Σ (x:A). Σ (y:B). C x y ≃ Σ (y:B). Σ (x:A). C x y`. Functorial actions
`f + g` and `f × g` preserve equivalences. Consequences:
`Fin (k+l) ≃ Fin k + Fin l` and `Fin (k·l) ≃ Fin k × Fin l`. Laws for
Π-types require funext.

### Contractible types

- `𝟏` is contractible: center `⋆`, contraction by `𝟏`-induction (`refl ⋆`).
- **Singleton contractibility (key fact).** For any `a : A`, the total space
  `Σ (x:A). a = x` is contractible, with center `(a, refl a)`; the
  contraction is by based path induction. This is the engine behind the
  fundamental theorem of identity types. Variant: `Σ (x:A). x = a` is
  contractible — it is exactly `fib id a`, and `id` is an equivalence, hence
  a contractible map (below).
- **Contractibility iff singleton induction.** `is-contr A` ⟺ `(a : A)` and
  `A` satisfies singleton induction. Forward: given `(a, C)`, first *adjust*
  `C` to `C' x := (C a)⁻¹ ∙ C x` so that `C' a = refl a` (by the left
  inverse law); then set `ind-sing a b x := tr B (C' x) b`, and the
  computation rule follows by `ap (λω. tr B ω b)` on `C' a = refl a`.
  Backward: `ind-sing a (refl a) : Π (x:A). a = x` is a contraction.
- **Equivalent characterizations.** The following are logically equivalent:
  - `is-contr A`;
  - `A ≃ 𝟏` (equivalently: `const ⋆ : A → 𝟏` is an equivalence);
  - `A` is an **inhabited proposition**: `A × is-prop A`, where
    `is-prop A := Π (x y : A). is-contr (x = y)` (truncation-levels.md).
    Forward: in a contractible type every `x = y` is itself contractible —
    apply 3-for-2 for contractibility (below) to
    `pr₁ : (Σ (z:A). x = z) → A` to make it an equivalence, then its fiber
    at `y` is equivalent to `x = y`. Backward: the inhabitant is the center
    and proposition-ness supplies the contraction.
- **Closure properties.** Retracts of contractible types are contractible;
  `A × B` is contractible iff both factors are; **3-for-2 for
  contractibility**: for `f : A → B`, any two of `is-contr A`, `is-contr B`,
  `is-equiv f` imply the third (apply 3-for-2 for equivalences to the
  triangle of constant maps over `𝟏`, using `A ≃ 𝟏 ⟺ is-contr A`).
  `Fin k` is *not* contractible for `k ≠ 1`.
- **Left unit law of Σ.** If `A` is contractible with center `a`, then
  `y ↦ (a, y) : B a → Σ (x:A). B x` is an equivalence: a Σ-type over a
  contractible base collapses to the fiber at the center.

### Equivalences are exactly the contractible maps

**Theorem.** `is-equiv f ⟺ is-contr-map f`. Both directions are
constructive:

1. **Contractible map ⇒ equivalence.** Centers of contraction of the fibers
   give `(g y, G y) : fib f y` for each `y : B` — a section `g : B → A` with
   `G : f ∘ g ~ id`. For the retraction: both `(g (f x), G (f x))` and
   `(x, refl (f x))` lie in `fib f (f x)`; contractibility identifies them
   by some `q`, and `ap pr₁ q : g (f x) = x`.
2. **Equivalence ⇒ contractible map**, in three steps:
   - `is-equiv f → has-inverse f` (above).
   - **Every invertible map is coherently invertible.** Given `(g, G, H)`,
     improve `G` to
     `G' y := (G (f (g y)))⁻¹ ∙ ap f (H (g y)) ∙ G y`;
     the coherence `f · H ~ G' · f` reduces — via the retraction-swap
     identification `H (g (f x)) = ap (g ∘ f) (H x)` — to a naturality
     square of `G · f : f ∘ g ∘ f ~ f`, which commutes by `nat-htpy`.
   - **Coherently invertible ⇒ contractible fibers.** For `y : B` take
     center `(g y, G y)`. A contraction must identify `(g y, G y)` with
     each `(x, p) : fib f y`; by path induction on `p : f x = y` it
     suffices to treat `(x, refl (f x))`, where `Eq-fib` asks for
     `α : g (f x) = x` with `G (f x) = ap f α ∙ refl (f x)`. Take
     `α := H x` and `K' x := K x ∙ (right-unit-htpy (f · H) x)⁻¹`.

**Corollaries and companions.**

- **Fibrant replacement.** Every map factors as an equivalence followed by a
  projection: `e : A ≃ Σ (y:B). fib f y` with
  `e a := (f a, (a, refl (f a)))` and `f ~ pr₁ ∘ e`.
- **Fibers of `pr₁`.** For a family `B` over `A`:
  `fib pr₁ a ≃ B a` via `λ((x,y),p). tr B p y`. Hence
  `pr₁ : (Σ (x:A). B x) → A` is an equivalence iff
  `Π (x:A). is-contr (B x)`; likewise a section `x ↦ (x, b x)` is an
  equivalence iff `Π (x:A). is-contr (B x)`.

## Reasoning idioms

### Proving `is-equiv f` — pick the cheapest route

1. **Explicit quasi-inverse** (`has-inverse f → is-equiv f`). Define
   `g : B → A` and both homotopies by induction/pattern matching on the
   domain; after case splits the homotopies are usually `refl`. *Use when:*
   the inverse is concrete and algebraic — structural laws (`×`, `+`, `Σ`
   rewrites), group operations on `ℤ`, permutations of `Fin k`. Default
   first attempt.
2. **Contractible fibers** (`is-contr-map f → is-equiv f`). Show each
   `fib f b` contractible by exhibiting a center and contracting, usually by
   path induction on the fiber's path component. *Use when:* the inverse is
   awkward to write down but "unique existence" is clear; when `f` is a
   canonical map out of an identity type (the fundamental theorem upgrades
   this: total-space contractibility ⟹ fiberwise equivalence); when working
   with the Σ-unit laws. Coherence subtlety: building the contraction from a
   raw invertible map `(g, G, H)` requires the *improved* `G'` (see the
   proof above) — in practice, path-induction on the fiber's path sidesteps
   writing `G'` explicitly.
3. **3-for-2.** Exhibit `f ~ g ∘ h` with two of `f g h` known equivalences;
   conclude the third. *Use when:* `f` arises as a composite (very often);
   to show a section or retraction of an equivalence is an equivalence; to
   transfer "being an equivalence" across a commuting triangle instead of
   constructing an inverse by hand.
4. **Homotopy-closure.** Replace `f` by a homotopic `g` you understand,
   prove `is-equiv g`, conclude `is-equiv f`. *Use when:* `f` is defined by
   a complicated induction but agrees pointwise with a simple map. Combines
   with 3-for-2: since triangles only commute up to homotopy, factorizations
   up to homotopy are enough.
5. **Retracts (mostly for contractibility).** Retracts of contractible types
   are contractible — show `A` is a retract of a known contractible type, or
   rewrite `A ≃ Σ (x:X). B x` with `X` contractible and collapse by the left
   unit law (`A ≃ B a`), or show `A ≃ 𝟏` outright. (Map-level closure of
   equivalences under retracts follows later via the fiber argument: fibers
   of a retract are retracts of fibers, and retracts of contractible types
   are contractible.)
6. **Characterize identity types** (the `pair-eq` workflow): reflexive
   relation `R` → canonical map `(x = y) → R x y` by path induction →
   equivalence. *Use when* the goal is `(s = t) ≃ R s t`; expect step 4
   (equivalence) to dominate, and delegate it to the fundamental theorem
   whenever possible: it suffices that `Σ (y:A). R x y` is contractible for
   each `x`.

### Using (eliminating) contractibility

- From `is-contr-map f`, extract the inverse *and* both homotopies: centers
  of contraction of the fibers give `(g y, G y) : fib f y`, and the
  retraction homotopy comes from uniqueness inside `fib f (f x)`.
  Contractibility of each fiber is a *choice principle for free* — no
  truncation issues.
- From `is-contr A` with center `a`: to build `Π (x:A). B x`, give only
  `b : B a` (singleton induction, `ind-sing a b x := tr B (C x) b`). To
  identify two elements, compose their contractions. To use `A` inside a
  Σ-type, contract it away via the left unit law.
- Identity types of a contractible type are contractible — contractible
  types are propositions, so equality proofs between their elements are
  automatic.

## Pitfalls

- **Never adopt `has-inverse f` as the definition of `is-equiv f`.** It is
  structure, not a property (`has-inverse (id : S¹ → S¹) ≃ ℤ`), and
  everything downstream (univalence, embeddings, truncation levels) depends
  on `is-equiv f` being a proposition. Exhibiting a quasi-inverse is a fine
  *proof technique* precisely because `has-inverse f → is-equiv f`.
- **`f ~ g` does not yield `f = g`** without funext. State commuting
  diagrams, groupoid laws of functions, and coherence conditions with `~`,
  not `=`. Conversely, do not try to prove `f = g` directly: prove `f ~ g`
  and (if available) apply funext.
- **The two inverses of a bi-invertible map are not literally the same
  map.** Only after constructing `K : g ~ h` may you treat the section as a
  retraction. "The inverse of `e`" means "the section of `e`"; that it is
  also a retraction is a theorem, not a definition.
- **Groupoid laws of homotopies are homotopies, not identifications, and
  never judgmental.** `H ∙ H⁻¹` is not `refl-htpy`, not even pointwise
  judgmentally (path laws hold only up to paths). Chain them explicitly via
  `assoc-htpy`, the unit laws, and the inverse laws.
- **Coherence is not optional.** A bare invertible map `(g, G, H)` does not
  directly give contractible fibers; `G` must be improved to `G'` with
  `f · H ~ G' · f`. When a contractibility-of-fibers proof stalls at the
  `refl` case, the missing ingredient is usually this coherence — or the
  analogous adjustment `C' x := (C a)⁻¹ ∙ C x` forcing `C' a = refl a` for
  contractions.
- **Watch concatenation order and whiskering sides.** `p ∙ q` is
  diagram-order (first `p`, then `q`);
  `nat-htpy H p : ap f p ∙ H y = H x ∙ ap g p` (`f`-paths on the left).
  `h · H` postcomposes (uses `ap`); `H · f` precomposes (substitutes the
  argument). Confusing `G · f` with `f · G` is the most common slip in
  coherence calculations.
- **`is-contr A` is data, not mere truth**: an element is a center *plus* a
  contraction, and must be constructed. (It is a proposition once funext is
  available, but that does not manufacture an element.) Keep the hierarchy
  straight: contractible (`A ≃ 𝟏`) is stronger than inhabited (`A`), which
  is stronger than merely inhabited (`‖A‖`; see logic-truncation.md). A bare
  hypothesis `x : A` never yields a contraction.
- **Non-equivalence needs invariants.** To show `f` is not an equivalence or
  `A ≄ B`, find a property transported by equivalences that separates the
  sides: `true = false → 𝟘` kills `bool ≃ 𝟏` and `const b` being an
  equivalence; size arguments kill `ℕ ≃ Fin k` and `is-contr (Fin k)` for
  `k ≠ 1`.
- **Σ has no commutativity.** Only the non-dependent swap
  `Σ (x:A). Σ (y:B). C x y ≃ Σ (y:B). Σ (x:A). C x y` is available; the
  fibers of a genuine Σ-type depend on the outer variable.
- **Π-type laws need funext.** Do not attempt commutativity/associativity of
  function types, or `is-equiv` proofs about maps between function types,
  before funext.md is loaded.

## See also

- identity-types.md — the path groupoid operations (`_∙_`, `_⁻¹`, `ap`,
  `tr`, path induction) from which homotopies are built pointwise; based
  path induction *is* contractibility of `Σ (x:A). a = x` in disguise.
- dependent-type-theory.md — `≡` versus `=`; Π- and Σ-types; the judgmental
  computation rules behind the `neg-bool` example.
- inductive-types.md — `bool`, `𝟏`, `𝟘`, `ℕ`, `Fin k`, coproducts; the
  induction principles used to build homotopies (`neg-neg-bool`) and the
  algebraic equivalences; `true ≠ false` for non-equivalence proofs.
- universes.md — `A ≃ B` as a type in `𝒰`; type families as maps into `𝒰`.
- fundamental-theorem.md — the payoff of singleton contractibility:
  total-space contractibility implies fiberwise equivalence; the systematic
  replacement for hand-rolled step-4 proofs when characterizing identity
  types.
- funext.md — `happly : (f = g) → (f ~ g)` as an equivalence; the proof that
  `is-equiv f` (and `is-contr A`) is a proposition; the laws of Π-types.
- truncation-levels.md — `is-prop A := Π (x y : A). is-contr (x = y)`;
  `is-contr = is-trunc −2`; contractible = inhabited proposition.
- logic-truncation.md — `‖A‖` versus `A` versus `is-contr A`: mere existence
  versus a chosen center; why extracting inverses from contractible fibers
  needs no truncation.
- univalence.md — `(A = B) ≃ (A ≃ B)`; the ultimate reason `is-equiv` had
  to be a property.
- circle.md — `has-inverse (id : S¹ → S¹) ≃ ℤ`: the concrete failure of
  quasi-inverses as a structure.
- finite-types.md — `Fin (k+l) ≃ Fin k + Fin l`, `Fin (k·l) ≃ Fin k × Fin l`;
  `succ-Fin` as an equivalence; `Fin k` not contractible for `k ≠ 1`.
- number-theory.md — the `ℤ` group laws behind `succ-ℤ`, `x ↦ x + k`,
  `x ↦ −x` being equivalences.
- groups.md — group isomorphisms as equivalences of underlying types.
- quotients.md — maps out of quotients are checked against
  equivalence-respecting data.
- w-types.md — W-type algebra reuses the Σ-law and equivalence toolkit.
