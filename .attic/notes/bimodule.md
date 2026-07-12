# Bimodule analysis of `emb`

## Setup

The ternary composition map

```
emb : hom x y → ∀ w → hom w x → ∀ v → hom y v → hom w v
```

sends each morphism to its bimodule action. After uncurrying, the
codomain is a dependent function type over two pointed total spaces:

```
Π (w : ob, a : hom w x) (v : ob, b : hom y v) . hom w v
```

The two dependent pair types are:

- `Σ w, hom w x` — incoming morphisms to `x`, pointed by `(x, idn)`
- `Σ v, hom y v` — outgoing morphisms from `y`, pointed by `(y, idn)`

## The restriction chain

There is a chain of restriction maps given by evaluation at the
respective centers:

```
Π(Σ w, hom w x)(Σ v, hom y v). hom w v
        │
        │ restrict to (w, a) = (x, idn)
        v
Π(Σ v, hom y v). hom x v
        │
        │ restrict to (v, b) = (y, idn)
        v
    hom x y
```

And `emb` composes with these restrictions:

- Restricting `emb f` to `(x, idn)` on the left gives `noy f`:
  the map `(v, b) ↦ emb f x idn v b`.
- Restricting `noy f` to `(y, idn)` gives `emb f x idn y idn`.

Each restriction is an equivalence iff the corresponding total space
is contractible. A dependent function out of a contractible type is
determined by its value at the center.

## The path groupoid: double Singl

For the path groupoid on a type `A`:

- `hom x y = x ≡ y`
- `emb f w a v b = a ∙ f ∙ b`
- `Σ w, w ≡ x` is contractible with center `(x, refl)`
- `Σ v, y ≡ v` is contractible with center `(y, refl)`

Both restrictions are equivalences. The codomain collapses:

```
Π(Σ w, w ≡ x)(Σ v, y ≡ v). w ≡ v
  ≃ Π(Σ v, y ≡ v). x ≡ v       contract left
  ≃ x ≡ y                        contract right
```

The forward direction sends `f : x ≡ y` to `λ w a v b → a ∙ f ∙ b`,
which is exactly `emb f`. The inverse sends `T` to `T x refl y refl`.
So `emb` IS the canonical equivalence between a type and the space of
dependent functions out of two contractible Singl types over it.

`emb` is an equivalence here not because of any categorical property
but because the Singl types are contractible — every bimodule map is
forced to be representable since there's no room for non-representable
ones.

## General analysis

When the two total spaces are not contractible, the codomain of `emb`
is genuinely larger than `hom x y`. A bimodule map can vary
non-trivially over both fibers, and evaluation at the centers loses
information in both directions.

### Both `Σ w, hom w x` and `Σ v, hom y v` contractible

Both restrictions are equivalences. The codomain collapses to
`hom x y`. `emb` is forced to be an equivalence. This is the path
groupoid case.

### One contractible (say `Σ w, hom w x`)

The first restriction is an equivalence, so `emb` factors through
`noy` up to equivalence. The source parameterization is trivial — a
bimodule map is determined by its action with `idn` on the left. Then:

- `emb` is an equivalence iff `noy` is an equivalence
- `emb` is an embedding iff `noy` is an embedding

The question reduces to `noy` vs the fiber `Σ v, hom y v`.
Symmetrically, if `Σ v, hom y v` is contractible, `emb` factors
through `yon`.

### Neither contractible

The section space `Π(Σ w, hom w x)(Σ v, hom y v). hom w v` has more
room than `hom x y`. The two cases:

**Equivalence**: every bimodule map is representable. `hom x y` is as
large as the full section space despite the total spaces being
non-contractible. The variation of a bimodule map over the fibers is
entirely determined by its value at the centers — a Yoneda
completeness condition.

**Embedding**: morphisms faithfully represent their bimodule actions
(contractible fibers over the image), but there exist bimodule maps
in `Π(Σ w, hom w x)(Σ v, hom y v). hom w v` that don't come from
any morphism. The image of `emb` is a proper sub-type of the section
space.

## What inhabits each case

### `emb` an equivalence

**Path groupoids on any type.** The canonical case. Both Singl types
contractible, forcing equivalence regardless of the h-level of `A`.

**Posets and preorders.** `hom x y` is a proposition. The bimodule map
space `Π(Σ w, hom w x)(Σ v, hom y v). hom w v` is also a proposition
(dependent product of propositions). The two propositions are logically
equivalent: `hom x y` gives a bimodule map by transitivity, and a
bimodule map gives `hom x y` by evaluating at the centers. A logical
equivalence between propositions is an equivalence. So `emb` is an
equivalence for any preorder — despite `Σ w, hom w x` being
potentially large (the entire downward closure of `x`).

**Codiscrete categories** (all homs contractible). Both domain and
codomain of `emb` are contractible, so `emb` is trivially an
equivalence.

The pattern: `emb` is an equivalence when the bimodule map space has
no more room than `hom x y`. This happens either because the Singl
types are contractible (codomain shrinks), or because the hom spaces
are truncated enough that the codomain can't grow beyond `hom x y`
even over non-contractible Singl types.

### `emb` an embedding (not equivalence)

**Deloopings of monoids and groups.** `BM` has one object, `hom = M`.
Then `emb : M → (M → M → M)` sends `f ↦ λ a b → a · f · b`. It's an
embedding: evaluating at `a = b = e` recovers `f`, so fibers over the
image are contractible. But the codomain `M → M → M` is vastly larger
than `M` — most binary operations on `M` aren't of the sandwich form
`a · f · b`. Even for a finite group `G`, the codomain has
`|G|^(|G|²)` elements vs `|G|`.

**Ordinary 1-categories** (`Set`, `Grp`, `Top`, etc.). Morphisms are
determined by their composition behavior (embedding), but not every
bimodule map between representables comes from a morphism.

**Wild higher categories** in general. Anything where hom spaces are
sets or higher and the Singl types are non-contractible.

### The dividing line

The threshold is roughly: `emb` is an equivalence when hom spaces are
(-1)-truncated (propositions) or the Singl types are contractible.
Once hom spaces are 0-truncated (sets) with non-contractible Singl
types, the bimodule map space can grow beyond `hom x y`, and `emb`
drops to an embedding. The delooping `BG` of a non-trivial group is
the sharpest counterexample — the simplest category where the gap
between embedding and equivalence is visible.

## Relationship to Cat.Virtual axioms

In the Cat.Virtual record, `emb` being an embedding is derived from
the axioms (`emb-image-contr`). The derivation goes through the
identity instantiation:

1. `compose-contr idn f` gives
   `is-contr (fiber emb (λ w a v b → emb idn w a v (noy f v b)))`
2. The target collapses to `emb f` via `interchange` + `absorb-r`
3. Transport gives `is-contr (fiber emb (emb f))` for all `f`

So the embedding property comes from composing with `idn` — the
identity instantiation strips away the noy wrapper and recovers the
morphism's own bimodule action.

`emb` being an equivalence is strictly stronger and is NOT derivable
from the Cat.Virtual axioms — it would require knowing the image of
`emb` is everything, which is external data about the category.

`noy` and `yon` being embeddings (`noy-inj`, `yon-inj`) is also
automatic from the Cat.Virtual axioms, derived from `interchange` +
`emb-inj`.

## The refactored `compose-contr`

The original `compose-contr` bundled both noy and yon
characterizations into one contractible type:

```
is-contr (Σ s, (emb s ≡ noy-char) × (emb s ≡ yon-char))
```

This required the agreement path `noy-char ≡ yon-char` to be
contractible, which holds only when the function type into hom spaces
is a set — i.e., when `ob` is a 1-type. The path groupoid on `S²`
is a counterexample (the 2-path `surf` gives a second distinct
agreement proof).

The refactored version splits this into:

- `compose-contr`: `is-contr (Σ s, emb s ≡ noy-char)` — a fiber of
  the embedding `emb`, contractible for any type.
- `interchange`: `emb f w a v (noy g v b) ≡ emb g w (yon f w a) v b`
  — a path, inhabited for any type. Not a contractibility condition,
  so it carries real data in the wild setting (it is not located in a
  contractible fiber unless hom spaces are propositions).

The 1-type obstruction vanishes. The path groupoid on any type
inhabits the refactored record.
