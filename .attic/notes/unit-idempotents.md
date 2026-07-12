# Unit Idempotents in Cat.Virtual

## The question

Can we wrap Cat.Virtual's `unit` field in `is-contr`?

```
unit-contr : ∀ {x} → is-contr
  (Σ e ∶ hom x x
  , ( (∀ {z} → is-equiv (λ (h : hom x z) → emb e x e z h))
    × (∀ {w} → is-equiv (λ (g : hom w x) → emb e w g x e)))
  × (∀ {z} (h : hom x z) → emb e x e z (emb e x e z h) ≡ emb e x e z h)
  × (∀ {w} (g : hom w x) → emb e w (emb e w g x e) x e ≡ emb e w g x e))
```

## Answer: no, for the path groupoid on arbitrary types

### Setup

For the path groupoid on `A`:
- `emb f w a z b = pcom (sym a) f b`
- By `pcom→cat-l`: `pcom (sym p) q r ≡ p ∙ (q ∙ r)`

### Verification of the pcom→cat-l computation

`pcom→cat-l` has signature:
```
pcom→cat-l : {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
  → pcom (sym p) q r ≡ p ∙ (q ∙ r)
```

**Left action.** `emb e x e z h = pcom (sym e) e h`. Matching against
`pcom (sym p) q r` gives `p = e, q = e, r = h`. Result:

    emb e x e z h ≡ e ∙ (e ∙ h)

**Right action.** `emb e w g x e = pcom (sym g) e e`. Matching gives
`p = g, q = e, r = e`. Result:

    emb e w g x e ≡ g ∙ (e ∙ e)

Both match the original claims. The slot-filling is correct.

### What the conditions reduce to

Write `F(h) = e ∙ (e ∙ h)` and `R(g) = g ∙ (e ∙ e)`.

**Left idempotency** says `F(F(h)) ≡ F(h)`, i.e.,

    e ∙ (e ∙ (e ∙ (e ∙ h))) ≡ e ∙ (e ∙ h)

Since `F` is an equivalence, left-cancel to get `F(h) ≡ h`, i.e.,
`e ∙ (e ∙ h) ≡ h` for all `h`. Setting `h = refl` and using
`unitr` on the inner term yields **e ∙ e ≡ refl**, i.e., `e` has
order dividing 2 in the loop group.

Conversely, `e ∙ e ≡ refl` implies `e ∙ (e ∙ h) ≡ (e ∙ e) ∙ h ≡
refl ∙ h ≡ h` (using associativity and unit laws), so `F ∼ id`,
from which idempotency `F(F(h)) ≡ F(h)` is immediate.

**Right idempotency** says `R(R(g)) ≡ R(g)`, i.e.,

    (g ∙ (e ∙ e)) ∙ (e ∙ e) ≡ g ∙ (e ∙ e)

With `R` an equivalence, right-cancel to get `R(g) ≡ g`, i.e.,
`g ∙ (e ∙ e) ≡ g` for all `g`. Setting `g = refl` and using
`unitl` yields the same condition **e ∙ e ≡ refl**.

So the two idempotency conditions (left and right) are genuinely
the same condition: `e² ≡ refl`.

### The is-equiv data: propositional and redundant

Given `e² ≡ refl`, we have `F ∼ id` and `R ∼ id`. A function
homotopic to the identity is an equivalence: take
`is-equiv-id : is-equiv id` and transport along the homotopy.
Concretely, if `e ∙ (e ∙ h) ≡ h` for all `h`, then `F` is a
bi-invertible map with both inverses being `id`.

Since `is-equiv` is a proposition (Rijke 10.4.4), the `is-equiv`
fields contribute no additional data beyond `e² ≡ refl`.

### Precise characterization of the unit Sigma type

The full unit Sigma type for the path groupoid is equivalent to:

    Σ (e : x ≡ x) , e ∙ e ≡ refl

via the following chain:

```
Σ e, (is-equiv F × is-equiv R) × (F ∘ F ∼ F) × (R ∘ R ∼ R)
  ≃ Σ e, (F ∘ F ∼ F) × (R ∘ R ∼ R)        -- is-equiv deducible from idpt
  ≃ Σ e, (F ∼ id) × (R ∼ id)                -- equiv + idpt ⇒ absorption; absorption ⇒ idpt
  ≃ Σ e, (e² ≡ refl) × (e² ≡ refl)         -- evaluating F ∼ id and R ∼ id at refl
  ≃ Σ e, e² ≡ refl                           -- both components are the same condition
```

The second step requires care. From left to right: if `F` is an
equivalence and `F ∘ F ∼ F`, then left-cancel to get `F ∼ id`.
From right to left: `F ∼ id` implies `F ∘ F ∼ F ∼ id ∼ F`.

The third step: `F ∼ id` is `∀ h, e ∙ (e ∙ h) ≡ h`, which is a
family of paths in `hom x z`. The forall-free version is equivalent
to `e² ≡ refl` because:
- Forward: evaluate at `h = refl`.
- Backward: from `e² ≡ refl`, derive `e ∙ (e ∙ h) ≡ (e ∙ e) ∙ h
  ≡ refl ∙ h ≡ h` using associativity and unit laws.

The fourth step: `R ∼ id` also reduces to `e² ≡ refl` by the same
argument, so the pair is redundant and we can project.

However, this final equivalence `Σ e, (e² ≡ refl) × (e² ≡ refl) ≃
Σ e, e² ≡ refl` is only valid if we know the second component is
propositional. The type `e ∙ e ≡ refl` is propositional when `x ≡ x`
is a set. In general, distinct proofs of `e² ≡ refl` exist, and the
diagonal `Δ : (p : e² ≡ refl) → (p , p)` need not be an equivalence.

**Upshot.** The unit Sigma is equivalent to
`Σ (e : x ≡ x), (e ∙ (e ∙ h) ≡ h for all h)`, which in turn is
equivalent to `Σ (e : x ≡ x), e² ≡ refl` when `x ≡ x` is a set,
but in general is a retract of `(Σ e, e² ≡ refl) × (Σ e, e² ≡ refl)`
projected along the diagonal. The moral equivalence
`unit ≃ Σ e, e² ≡ refl` holds at 0-truncated hom types.

### 2-torsion classification

The question "for which types is `Σ (e : x ≡ x), e² ≡ refl`
contractible?" is equivalent to asking when the 2-torsion subgroup
of the loop space `Ω(A, x)` is trivial (i.e., the only element
of order dividing 2 is `refl`).

**Sets (0-types).** `x ≡ x` is a proposition, so the only loop is
`refl`. Contractible. This is the easy case.

**S^1.** `π₁(S¹) ≅ Z`. The 2-torsion subgroup of Z is trivial
(the only `n` with `2n = 0` is `n = 0`). Contractible.

**S^2.** `π₁(S²) ≅ 0` (simply connected), so the base loop space
has only `refl`. Contractible. (The higher homotopy groups are
irrelevant here since we only look at `x ≡ x`, not iterated loops.)

**S^n for n >= 2.** All simply connected, so `π₁ = 0`. Same argument.
Contractible.

**K(Z, 1) ≅ S^1.** Same as S^1. Contractible.

**K(Z/2Z, 1) ≅ RP^infinity.** `π₁ ≅ Z/2Z`. The nontrivial element
`α` satisfies `α² = refl`. Both `refl` and `α` inhabit the Sigma.
**Not contractible** -- has exactly 2 points.

**K(G, 1) for abelian G.** `Σ e, e² ≡ refl` bijects with the
2-torsion subgroup `G[2] = {g ∈ G : 2g = 0}` (using additive
notation). Contractible iff `G[2] = {0}`, i.e., G has no 2-torsion.
Examples:
- G = Z: contractible
- G = Z/nZ for odd n: contractible (gcd(2,n) = 1 ⇒ no 2-torsion)
- G = Z/2Z: not contractible
- G = Z/4Z: not contractible (2 has order 2)
- G = Z/2Z x Z/2Z: not contractible (3 elements of order 2)
- G = Q: contractible (torsion-free)

**K(G, n) for n >= 2.** These are simply connected (π₁ = 0), so
the base loop space is trivial. Contractible.

**General characterization.** The type
`Σ (e : x ≡ x), e² ≡ refl` is contractible if and only if the
2-torsion subgroup of `π₁(A, x)` is trivial, where `π₁` denotes
the (set-truncated) fundamental group. More precisely: in the
untruncated setting, contractibility of the Sigma requires both
(a) no nontrivial 2-torsion loops and (b) contractibility of
the proof component `e² ≡ refl` at `e = refl`, which is
`refl ≡ refl` in `x ≡ x`, i.e., an element of `Ω²(A, x)`.
This is contractible iff `A` is a 1-type.

So the full answer: `Σ (e : x ≡ x), e² ≡ refl` is contractible
iff A is a 1-type with no 2-torsion in π₁.

### Obstruction 1: 2-torsion in the loop space

On `K(Z/2Z, 1)`, the fundamental group has a nontrivial
element `α` with `α² = refl`. Both `refl` and `α` satisfy all unit
conditions, so the Sigma has (at least) two points. Not contractible.

### Obstruction 2: proof data at higher h-levels

Even on types with no 2-torsion, contractibility of the Sigma
requires the proof data to be trivial. At `e = refl`, the fiber
of `e² ≡ refl` is `refl ∙ refl ≡ refl`, which reduces (via
`unitl`) to `refl ≡ refl` in `x ≡ x`. This is a point in
`Ω²(A, x)`. Contractibility of this type (over the base `e = refl`)
requires `Ω(A, x)` to be a set, i.e., A is a 1-type.

For a concrete failure: on `S²`, we have `π₁ = 0` (no 2-torsion),
but `π₂(S²) ≅ Z`, so `Ω²(S², base)` is nontrivial. The Sigma
has a unique base point (`refl`) but the proof fiber over it is
not contractible.

## How Kraus avoids the 2-torsion issue

### Kraus's setup

Kraus works with a semicategory: a type `Hom x y` with binary
composition `_⋄_` and associativity `ass`. His conditions are:

- **Idempotent:** `e ⋄ e ≡ e`
- **Equivalence:** `(h ↦ h ⋄ e)` and `(f ↦ e ⋄ f)` are equivalences

### The critical difference: e ⋄ e ≡ e vs e ⋄ e ≡ id

For the path groupoid viewed as a semicategory with `f ⋄ g = f ∙ g`:

- **Kraus idempotent:** `e ∙ e ≡ e`
- **Cat.Virtual absorption:** `e ∙ (e ∙ h) ≡ h`, reducing to `e ∙ e ≡ refl`

These are fundamentally different equations:
- `e ∙ e ≡ e` says **e is a fixed point of left-multiplication by e**
- `e ∙ e ≡ refl` says **e has order dividing 2 in the loop group**

From `e ∙ e ≡ e`, right-compose with `sym e`:

    (e ∙ e) ∙ sym e ≡ e ∙ sym e
    e ∙ (e ∙ sym e) ≡ refl    (by assoc + invr)
    e ∙ refl ≡ refl            (by invr)
    e ≡ refl                   (by unitr)

So Kraus idempotency `e ⋄ e ≡ e` **immediately forces e ≡ refl** in
the path groupoid. There is no room for 2-torsion elements to satisfy
the condition. This is why Kraus can prove contractibility: the only
idempotent equivalence in a group is the identity element.

Cat.Virtual's condition is weaker: it asks for `e² = id` (involution)
rather than `e² = e` (idempotent). Every involution is an idempotent
in the sense of "idempotent action on hom" but not in the sense of
"idempotent under self-composition." The latter is what Kraus uses,
and it's the stronger condition that pins down the identity uniquely.

### Why the translation fails

Kraus's binary composition `_⋄_` and Cat.Virtual's ternary `emb` are
connected by:

    f ⋄ g = emb f _ g _ idn = yon f _ g

In Kraus's framework, `e ⋄ e ≡ e` translates to `yon e _ e ≡ e`.
In Cat.Virtual, `yon e w g = emb e w g _ idn`, so
`yon e x e = emb e x e x idn = pcom (sym e) e refl ≡ e ∙ e` (via
`pcom→cat-l` and `unitr`). So `yon e x e ≡ e` is `e ∙ e ≡ e`,
which is Kraus's condition.

Cat.Virtual's unit axiom instead asks for the weaker
`emb e x e z (emb e x e z h) ≡ emb e x e z h`, which is
idempotency of the *action* `F(h) = emb e x e z h`, not
idempotency of `e` under self-composition. The action-idempotency
+ action-equivalence gives `F ∼ id`, i.e., `e` is absorbing
(neutral). But the Sigma quantifies over `e` first, and `F ∼ id`
only pins `e` down to a 2-torsion element, not to `refl`.

To get Kraus's condition from Cat.Virtual's setup, you'd need
`yon e x e ≡ e` as a field, which is `emb e x e x idn ≡ e`.
By `pcom→cat-l` this is `e ∙ (e ∙ refl) ≡ e`, i.e., `e ∙ e ≡ e`.
This is strictly stronger than what Cat.Virtual currently requires.

### Kraus's contractibility proof structure

Kraus's proof (from `Identities.agda`, module `unique`) goes:

1. Given `i₀` an idempotent equivalence, construct an equivalence chain:
```
Σ e, is-idpt e × is-eqv e
  ≃ Σ e, is-eqv e × is-idpt e              -- swap
  ≃ Σ e, (Σ p : is-eqv e, e ≡ I(e,p))     -- idpt ≃ (e ≡ I(e))
  ≃ Σ e, (Σ p : is-eqv e, e ≡ i₀)         -- I(e,p) ≡ i₀ by uniqueness
  ≃ Σ (e, e ≡ i₀), is-eqv e               -- reassociate
  ≃ is-eqv i₀                              -- contract (Σ e, e ≡ i₀)
  ≃ Unit                                    -- is-eqv is a prop
```

Key step: `I(e, p)` (the Harpaz-Lurie construction: `I = e⁻¹ ⋄ e`
where `e⁻¹` is the inverse of left-multiplication by `e`) produces
a canonical idempotent equivalence from any equivalence `e`. By
uniqueness of idempotent equivalences (`i₁ ⋄ i₂ ≡ i₂` and
`i₁ ⋄ i₂ ≡ i₁` gives `i₁ ≡ i₂`), all such `I(e,p)` equal `i₀`.

The crucial ingredient is **associativity** -- used both in the
uniqueness proof and in showing `I(e,p)` is idempotent. Cat.Virtual
has associativity (from compose-contr + interchange), so in
principle the Kraus argument could be translated. But it would
require reformulating the unit axiom to use Kraus-style
idempotency `e ⋄ e ≡ e` rather than action-idempotency.

## Alternative formulations

### Approach 1: noy/yon neutrality

Define the unit via:
```
unit : ∀ {x} → Σ e ∶ hom x x , noy e ≡ (λ z h → h)
```

For path groupoids: `noy e z h = emb e x idn z h = pcom refl e h`.
By `pcom→cat-l` (with `p = refl`): `pcom refl e h ≡ refl ∙ (e ∙ h)
≡ e ∙ h` (modulo `unitl`). So `noy e ≡ (λ z h → h)` forces
`e ∙ h ≡ h` for all `h`, which gives `e ≡ refl`.

**Problem:** This is exactly standard left-neutrality. The Sigma
`Σ e, noy e ≡ (λ z h → h)` for path groupoids is:
`Σ (e : x ≡ x), ∀ z (h : x ≡ z), e ∙ h ≡ h`. At `e = refl` the
fiber is `∀ z (h : x ≡ z), refl ∙ h ≡ h`, which is a product of
path types. Is this contractible?

By Rijke 11.2.4 (fundamental theorem of identity types), the total
space `Σ z, x ≡ z` is contractible, so `∀ z (h : x ≡ z), P(z, h)`
is contractible whenever `P(x, refl)` is. Here `P(z, h) = (refl ∙ h
≡ h)`, and `P(x, refl) = (refl ∙ refl ≡ refl) = (refl ≡ refl)` in
`x ≡ x`. This is contractible iff A is a 1-type. Same obstruction.

**Circular dependency problem.** `noy` is defined as
`noy f z h = emb f _ idn z h`, so it depends on `idn`, which comes
from `unit`. The formulation is circular unless we make `noy`
independent of `idn`.

We could instead use the raw `emb`-based version: for each `e`,
define `noy_e(z, h) = emb e x e z h` where the second slot is also
`e` (the unit candidate itself). Then `noy_e ≡ (λ z h → h)` is
`∀ z h, emb e x e z h ≡ h`, which is exactly the absorption
condition. But this is what Cat.Virtual already captures via the
equivalence + idempotency, and it reduces to `e² ≡ refl`, not
`e ≡ refl`.

### Approach 2: emb e ≡ target characterization

Characterize the identity as the morphism whose embedding acts as
the "swap-compose" operation:

```
unit : ∀ {x} → Σ e ∶ hom x x
  , emb e ≡ (λ w a z b → emb a w ??? z b)
```

This doesn't have a clean target because `emb` takes a morphism
`x → y` and produces a 4-argument function, while the "identity
behavior" of `emb` is `emb idn w a z b = ???` where the output
depends on what `a` and `b` compose to. Without a pre-existing
composition operation, we can't state the target.

### Approach 3: Using compose-contr as the identity characterization

The compose-contr gives `is-contr (Σ s, emb s ≡ noy-char)` for each
pair `(f, g)`. In particular, `compose-contr f idn` gives
`is-contr (Σ s, emb s ≡ (λ w a v b → emb f w a v (noy idn v b)))`.
Since `noy idn v b = emb idn _ idn v b`, and via absorption
`noy idn ∼ id`, this fiber contains `f`.

Could we define `idn` as a fixed point? I.e., `idn` is the `e`
such that for all `f`, the composite `f ⨾ e` equals `f`?

The problem is that `_⨾_` is defined in terms of compose-contr,
which uses `noy`, which uses `idn`. So `f ⨾ e ≡ f` presupposes
`idn` exists. This is inherently circular.

**A non-circular version:** We could try to characterize `idn` as
an `e` such that `compose-contr f e` (for all `f`) has center whose
first component equals `f`. But compose-contr's target involves
`noy e`, which involves `idn`, creating the same circularity.

### Approach 4: Kraus-style idempotency in Cat.Virtual

Replace Cat.Virtual's unit axiom with:
```
unit : ∀ {x} → Σ e ∶ hom x x
  , (emb e x e x e ≡ e)        -- Kraus idempotency: yon e x e ≡ e
  × (∀ z → is-equiv (λ (h : hom x z) → emb e x e z h))
  × (∀ w → is-equiv (λ (g : hom w x) → emb e w g x e))
```

Here `emb e x e x e` plays the role of `e ⋄ e` in Kraus. This
formulation does not depend on `idn` or `noy` -- it's self-contained.
The condition `emb e x e x e ≡ e` (after unfolding via `pcom→cat-l`)
is `e ∙ (e ∙ e) ≡ e`, which for loops gives `e³ ≡ e`, not `e² ≡ e`.

Wait -- this is wrong. Let me recheck. `emb e x e x e` with
slots `w = x, a = e, z = x, b = e` gives `pcom (sym e) e e`.
By `pcom→cat-l` with `p = e, q = e, r = e`:
`pcom (sym e) e e ≡ e ∙ (e ∙ e)`. So the condition
`emb e x e x e ≡ e` is `e ∙ (e ∙ e) ≡ e`, i.e., `e³ ≡ e`.

This is weaker than Kraus's `e² ≡ e`. For a group, `e³ = e` means
`e² = id`, which is back to the 2-torsion condition.

The issue is that Cat.Virtual's `emb e x e x e` is not the same as
`yon e x e` because `yon` uses `idn` in one slot:
`yon e x g = emb e x g _ idn`. If we had `yon e x e = emb e x e _ idn`,
the right slot would be `idn`, not `e`. The Kraus condition `e ⋄ e ≡ e`
corresponds to `yon e x e ≡ e`, which is `emb e x e x idn ≡ e`, i.e.,
`pcom (sym e) e refl ≡ e`, i.e., `e ∙ (e ∙ refl) ≡ e`, i.e., `e² ≡ e`.

But `yon` depends on `idn`. To state `yon e x e ≡ e` without `idn`,
we'd need to put `refl` (or the actual identity morphism) in that slot,
which reintroduces `idn` dependence.

**Conclusion.** There is no obvious way to state Kraus idempotency
(`e ⋄ e ≡ e`) in Cat.Virtual's `emb`-based framework without
referencing `idn`, because `_⋄_` is defined via `yon` which uses
`idn`. The `emb`-self-application `emb e x e x e` gives `e³ ≡ e`,
a strictly weaker condition.

### Approach 5: Baking absorption directly into the axiom

```
unit : ∀ {x} → Σ e ∶ hom x x
  , (∀ {z} (h : hom x z) → emb e x e z h ≡ h)
  × (∀ {w} (g : hom w x) → emb e w g x e ≡ g)
```

This directly states absorption (neutrality) rather than deriving
it from equivalence + idempotency. It's cleaner and avoids the
`is-equiv` fields entirely.

For path groupoids, this is `Σ e, (∀ h, e ∙ (e ∙ h) ≡ h) ×
(∀ g, g ∙ (e ∙ e) ≡ g)`. As analyzed above, both conditions
reduce to `e² ≡ refl`. The Sigma is still not contractible for
types with 2-torsion in π₁, by the same obstruction.

This formulation is equivalent to the current one (absorption
implies idempotency; equivalence + idempotency implies absorption)
but more economical. It's worth considering as a simplification,
but it doesn't help with contractibility.

## Interaction with compose-contr

Compose-contr gives `is-contr (Σ s, emb s ≡ noy-char)`. Can the
identity be characterized using this?

The unit laws `f ⨾ idn ≡ f` and `idn ⨾ f ≡ f` follow from
compose-contr: `f ⨾ idn` lives in a contractible fiber that also
contains `f` (after showing the targets match via absorption).
This is exactly how `unitr` and `unitl` are currently derived.

The question is whether `idn` itself can be characterized as a
fixed point. For instance: "the composite of any `f` with the
identity is `f`" characterizes `idn` among morphisms `hom x x`.
Formally: `idn` is the unique `e : hom x x` such that for all
`f : hom x y`, the composite `f ⨾ e` (which exists by
compose-contr) equals `f`. This is equivalent to absorption.

The obstacle remains: this characterization is a
*property* of `e`, not a *contractible type*. The type
`Σ e, ∀ f, f ⨾ e ≡ f` has the same 2-torsion obstruction because
`f ⨾ e ≡ f` unfolds to absorption.

## What does work

The bare Sigma (current formulation) is inhabitable for any type:
`(refl, equiv-data, idpt-data)` works because `emb refl` acts as the
identity on both sides.

## Summary of the situation

| Condition | For path groupoid | Contractible? |
|-----------|------------------|---------------|
| Cat.Virtual unit (current) | `Σ e, e² ≡ refl` + props | No (2-torsion + h-level) |
| Direct absorption | `Σ e, F ∼ id × R ∼ id` | No (same as above) |
| Kraus idempotent-eqv | `Σ e, e² ≡ e` + eqv | Yes! (forces e = refl) |
| noy-neutrality | `Σ e, noy e ∼ id` | No (circular + same obstruction) |

The fundamental tension: Cat.Virtual's `emb`-based unit axiom captures
*absorption* (being neutral in the action on hom), which for groups
means `e² = id` (involution). Kraus's axiom captures *idempotency
under self-composition*, which for groups means `e² = e` (whence
`e = id`). The latter is strictly stronger and pins down the identity
uniquely. The former allows all involutions, which include nontrivial
2-torsion elements.

## Possible paths forward

1. **Accept non-contractibility.** The current formulation works: `unit`
   is inhabited for all types, and absorption follows. The `idn-ind`
   and `idn-unique` principles mentioned in Cat.Virtual require showing
   `unit-is-prop` (not `is-contr`), which is a weaker statement.

2. **Strengthen to Kraus-style.** Would require introducing a notion of
   `yon e x e` without circularity through `idn`. One option: add a
   separate `compose` operation `_⋄_ : hom x y → hom y z → hom x z`
   (defined as `yon f _ g`) and state Kraus idempotency in terms of
   `_⋄_`. But this changes the foundational structure significantly.

3. **Derive unit-is-prop from the full structure.** If we have
   compose-contr + interchange + the current unit, the full categorical
   structure (associativity, unit laws) is available. We can then
   attempt the Kraus proof internally: given two units `e₁, e₂`,
   show `e₁ ≡ e₂` via `e₁ ⨾ e₂ ≡ e₂` (right-neutrality of `e₁`)
   and `e₁ ⨾ e₂ ≡ e₁` (left-neutrality of `e₂`). This gives
   uniqueness of the *morphism* `e`, and then the proof data is
   propositional (being `is-equiv` data). This should work.

   Explicitly: given `(e₁, d₁)` and `(e₂, d₂)` in the unit type,
   `absorb-l` from `e₁` gives `emb e₁ x e₁ z e₂ ≡ e₂`,
   `absorb-r` from `e₂` gives `emb e₂ x e₁ x e₂ ≡ e₁`. Wait --
   the absorption goes through `emb` with both slots being the *same*
   unit. `absorb-l` using `e₁`: `emb e₁ x e₁ z h ≡ h` for all `h`.
   Set `h = e₂` (assuming `z = x`): `emb e₁ x e₁ x e₂ ≡ e₂`.
   `absorb-r` using `e₂`: `emb e₂ w g x e₂ ≡ g` for all `g`.
   Set `g = e₁` (assuming `w = x`): `emb e₂ x e₁ x e₂ ≡ e₁`.

   But `emb e₁ x e₁ x e₂ ≠ emb e₂ x e₁ x e₂` in general -- these
   use different morphisms in the first slot! We'd need interchange
   or some relation between them.

   In the binary formulation: `e₁ ⋄ e₂ = yon e₁ _ e₂ = emb e₁ x e₂ _ idn₁`
   where `idn₁` is the identity from unit₁. This mixes the two units
   in a way that makes the Kraus uniqueness argument difficult to
   replicate directly.

   This approach needs more thought. The key question is whether
   `emb e₁ x e₁ x e₂` equals `emb e₂ x e₁ x e₂` via some path
   derivable from the two units' data.

4. **Use emb-image-contr for unit uniqueness.** Since `emb` is an
   embedding (`emb-image-contr`), two morphisms with the same
   `emb`-image are equal. If we can show `emb e₁ ≡ emb e₂` for any
   two units, then `e₁ ≡ e₂` by `emb-inj`. The `emb`-image of a
   unit `e` satisfies `emb e w a z b ≡ emb idn w a z b` (by the
   absorption + embedding properties), but again this references
   `idn` from one particular unit.

## Relation to compose-contr weakening

The March 2026 refactoring split `compose-contr` into:
- `compose-contr`: single noy-characterization (contractible for any type)
- `interchange`: separate field (inhabited for any type)

This eliminated the 1-type obstruction from the COMPOSITION axioms.
The unit axiom has a different obstruction (2-torsion + h-level of
proof data) that is orthogonal to the composition story.

## Open questions

1. Can unit uniqueness (morphism component) be derived from the
   existing Cat.Virtual axioms without strengthening the unit field?
   The Kraus argument translated to the ternary setting would do this.

2. Is there a notion of "idempotent" for `emb` that doesn't pass
   through binary composition and still forces `e = idn`?

3. For the actual use case (virtual bicategories, not just path
   groupoids), does the non-contractibility of the unit type matter?
   If hom types are always sets (which we do NOT assume), the
   2-torsion obstruction vanishes and only the h-level obstruction
   remains.
