Lane Biocini
February 2026

Coherence bootstrap for categories.
The embedding `repr` that defines composition carries all higher
coherences automatically. Applying `ap` to the embedding gives
equivalences at each path level, making all diagrams of canonical
isomorphisms commute.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

-- Cat.Cell2: Why the naive (∞,∞) tower collapses, and what's needed
--
-- The hope was: iterate yon-emb to get directed content at every
-- dimension. The reality: ap on an embedding is an equivalence,
-- so all levels ≥ 2 are Yoneda-complete. Directed content lives
-- only at dimension 1. This is an (∞,1)-category.
--
-- This is a known feature of HoTT-internal category theory.
-- In Riehl-Shulman (arXiv:1705.07442), directed 2-cells come
-- from 2-simplices via the postulated directed interval. In
-- plain HoTT/cubical, all higher cells are paths ⟹ invertible.
--
-- Below: (a) the collapse, (b) what strictification it buys,
-- (c) what additional data genuine (∞,∞) requires.

module Cat.Coherence where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv
open import Core.Transport
open import Core.Path
open import Core.Function.Base
open import Core.Function.Embedding
open import Cat.Base

module _ {o} {h} (C : category o h) where
  open Cat C

  -- ═══════════════════════════════════════════════════
  -- § The Collapse
  -- ═══════════════════════════════════════════════════
  --
  -- yon is an embedding. Embeddings satisfy:
  --   ap f : (x ≡ y) ≃ (f x ≡ f y)
  -- So the level-2 "yon" = ap yon is an equivalence.
  -- No gap. No directed content. Induction kills all
  -- higher levels.

  module collapse (x y : ob) where

    𝓡 : Type (o ⊔ h)
    𝓡 = ∀ w → hom w x → hom w y

    yon₂ : ∀ {f g : hom x y} → f ≡ g → yon f ≡ yon g
    yon₂ = ap yon

    yon₂-is-equiv : ∀ {f g : hom x y} → is-equiv (yon₂ {f} {g})
    yon₂-is-equiv = is-embedding→ap-equiv yon-emb

    -- Level 3: ap yon₂ = ap (ap yon).
    -- yon₂ is equiv ⟹ embedding ⟹ ap yon₂ is equiv.
    -- By induction, apⁿ yon is an equivalence for all n ≥ 1.
    -- The entire tower above dimension 1 is invertible.

  -- ═══════════════════════════════════════════════════
  -- § What the Collapse Buys: Free Coherence
  -- ═══════════════════════════════════════════════════
  --
  -- The collapse is not a bug — it's the (∞,1) coherence
  -- theorem. Since level 2 is Yoneda-complete:
  --
  -- • unitl, unitr, assoc are paths in hom (level-2 cells)
  -- • pentagon, triangle, etc. are paths between paths
  --   (level-3 cells)
  -- • all such coherences are unique when they exist
  --
  -- This is why we don't need to provide pentagon as data.
  -- The Segal condition (composite-contr) at level 1
  -- generates all coherence at levels ≥ 2 for free.

  module coherence-example {x y z w : ob}
    (f : hom x y) (g : hom y z) (h : hom z w) where

    -- Two paths from (f ⨾ g) ⨾ h to f ⨾ (g ⨾ h):
    -- both are assoc. Any two such paths are equal
    -- iff hom is a set (1-category case).
    --
    -- For general hom, the paths might differ, but
    -- their IMAGES under ap yon are always equal
    -- (since yon₂ is an equivalence, the fibers over
    -- any point in 𝓡 are contractible — i.e. ≈ is
    -- a prop even when ≡ is not).
    --
    -- Wait — that's wrong. yon₂ being an equivalence
    -- means (f ≡ g) ≃ (yon f ≡ yon g). This DOESN'T
    -- make f ≡ g a prop. It makes it equivalent to a
    -- path in function space, which has the same
    -- h-level as the original.
    --
    -- So coherences are NOT automatically unique unless
    -- hom is a set. What IS free is that coherences in
    -- the ≈ world (paths in 𝓡) are exactly coherences
    -- in the ≡ world (paths in hom). No information
    -- loss. The tame side adds nothing new.

  -- ═══════════════════════════════════════════════════
  -- § What (∞,∞) Actually Requires
  -- ═══════════════════════════════════════════════════
  --
  -- Directed content at dimension 2 requires hom₂ as
  -- ADDITIONAL DATA — not derived from paths.
  --
  -- An (∞,∞)-category is enriched in (∞,∞)-categories:
  -- each hom(x,y) is not just a type but an (∞,∞)-cat
  -- whose morphisms may be non-invertible.

  -- Coinductive sketch (not valid Agda, just the idea):
  --
  -- record ∞-cat : Type where
  --   coinductive
  --   field
  --     ob  : Type
  --     hom : ob → ob → ∞-cat        ← the key move
  --     yon : ... ↪ presheaves ...
  --
  -- At each level k, yon is an embedding (not equiv).
  -- Paths at each level map INTO hom via path-to-cell,
  -- but hom may contain non-invertible cells.

  -- The truncated version (2-category via yon-emb):

  record cat₂ (o h h₂ : Level) : Type₊ (o ⊔ h ⊔ h₂) where
    field
      -- Level 1 (standard yon-emb category)
      ob₁     : Type o
      hom₁    : ob₁ → ob₁ → Type h
      yon₁    : ∀ {x y} → hom₁ x y → ∀ w → hom₁ w x → hom₁ w y
      yon₁-emb : ∀ {x y} → is-embedding (yon₁ {x} {y})
      idn₁-fib : ∀ {x} → fiber (yon₁ {x} {x}) (λ w h → h)
      comp₁-fib : ∀ {x y z} (f : hom₁ x y) (g : hom₁ y z)
        → fiber yon₁ (λ w h → yon₁ g w (yon₁ f w h))

      -- Level 2 (separate, not from paths)
      hom₂    : ∀ {x y} → hom₁ x y → hom₁ x y → Type h₂
      yon₂    : ∀ {x y} {f g : hom₁ x y}
        → hom₂ f g → ∀ w → hom₂ w f → hom₂ w g
      yon₂-emb : ∀ {x y} {f g : hom₁ x y}
        → is-embedding (yon₂ {f = f} {g})
      idn₂-fib : ∀ {x y} {f : hom₁ x y}
        → fiber (yon₂ {f = f} {f}) (λ w α → α)
      comp₂-fib : ∀ {x y} {f g h : hom₁ x y}
        → (α : hom₂ f g) (β : hom₂ g h)
        → fiber yon₂ (λ w φ → yon₂ β w (yon₂ α w φ))

      -- Compatibility: paths give rise to 2-cells
      -- (but not every 2-cell is a path)
      path→hom₂ : ∀ {x y} {f g : hom₁ x y}
        → f ≡ g → hom₂ f g

    -- where comp₁ is derived from comp₁-fib as usual
    comp₁ : ∀ {x y z} → hom₁ x y → hom₁ y z → hom₁ x z
    comp₁ f g = comp₁-fib f g .fst

    field

      -- Whiskering: 1-composition acts on 2-cells
      -- (This is where the interaction between levels lives)
      whisker-l : ∀ {x y z} {f g : hom₁ x y} (h : hom₁ y z)
        → hom₂ f g → hom₂ (comp₁ f h) (comp₁ g h)
      whisker-r : ∀ {x y z} (h : hom₁ x y) {f g : hom₁ y z}
        → hom₂ f g → hom₂ (comp₁ h f) (comp₁ h g)

  -- ═══════════════════════════════════════════════════
  -- § Where This Leaves the Library
  -- ═══════════════════════════════════════════════════
  --
  -- Cat.Base with yon-emb gives (∞,1)-categories. This is
  -- the right level for most of the theory we've been
  -- building: BG, Rezk completion, canonical equality.
  --
  -- For (∞,∞), we'd need cat₂ above (or the coinductive
  -- version). The yon-emb idea still applies at each level,
  -- but the levels must be given as separate data.
  --
  -- Comparison with existing approaches:
  --
  -- • Riehl-Shulman STT: gets all levels from the directed
  --   interval. More economical, but requires postulates.
  --
  -- • Globular/opetopic: gives levels as separate data,
  --   similar to cat₂. Our yon-emb replaces explicit
  --   composition + associator + pentagonator + ... with
  --   a single embedding condition per level. Still a win.
  --
  -- • Complicial sets (Verity): directed cells at each
  --   dimension via thin/thick simplices. Closest classical
  --   analogue to having both paths and hom₂.
  --
  -- The yon-emb contribution: at each level, a single
  -- embedding condition (+ closure) replaces all the
  -- coherence data. Segal condition per dimension. The
  -- price is carrying hom-data at each level.
