Lane Biocini
July 2026

Associativity and the Mac Lane pentagon for representable hcategories.
The tower gates on the bundle `(C : hcategory o h)` and is purely
associativity: it consumes only `compose-contr`, `emb-comp`, and
`·-comp` — no unit axiom, no `interchange`. `assoc-tower` derives
`assoc` from the contractible triple-composite fiber; `pentagon-tower`
carries the quadruple composite, the five faces, and the named
`pentagon`.

This is the collapsed form of the tower. Every canonical fiber point
is identified in a `subst`-transported contractible fiber (`E₃-contr`,
`E₄-contr` built from `compose-contr` by transporting along pointwise
`emb-comp`/`·-comp` expansions); each face reads a fiber edge against a
canonical lift of `assoc-σ` — a right whisker `Λk`, a left whisker
`Λf`/`Φ`, or a reindex `R` — through `contr-face`. Two helpers factor
the shared skeleton: `reindex-face` (which builds its own reindex lift
and both `Path.assoc` bridges) carries `face₂₃`/`face₄₅`, and
`whisker-face` (generic over the lift, taking the two bridges from the
caller) carries `face₁₂`/`face₃₅`/`face₁₄`. No face is left direct.

The bridge structure — the `Path.assoc` reassociations, the `ap-comp`
distributions, and `face₁₄`'s `homotopy-natural` square — is validated
as irreducible at this record. Binary right-nested fiber witnesses are
the optimum: `pcom`-native endpoints were tested and cost more (they
force a conservation `+1` on every whisker face), so the binary form
stays (bridge-conservation, spike-verified).

The whole tower is the regression baseline for the planned deeper
reformulation — the transfer-principle collapse that would remove the
face plumbing outright is still under investigation.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep.Coherence where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using
  ( is-contr→is-prop; _∙_; contr-face; module Path
  ; pcom; module pcom; pcom→∙ )
open import Core.Transport.J using (subst)
open import Core.Path.Base using (ap-comp)
open import Core.Homotopy using (homotopy-natural)
open import Core.Coherence.Base using (coh-project)

open import Cat.Codep.Base
```

## Triple composite, assoc-σ, assoc

`pt-l`/`pt-r` are the two canonical fibers of the triple composite,
their witnesses right-nested binary `∙`-chains. `E₃-contr` transports
`compose-contr` along the pointwise `emb-comp` expansion; `assoc` is
the projection of the fiber path.

```agda
module assoc-tower {o h} (C : hcategory o h) where
  open hcategory C

  E₃ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w) → composite x w
  E₃ f g h = emb f · g · h

  pt-l : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
       → fiber emb (E₃ f g h)
  pt-l f g h = (f ⨾ g) ⨾ h , emb-comp (f ⨾ g) h ∙ ap (_· h) (emb-comp f g)

  pt-r : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
       → fiber emb (E₃ f g h)
  pt-r f g h = f ⨾ (g ⨾ h) , emb-comp f (g ⨾ h) ∙ ·-comp (emb f) g h

  E₃-contr : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
           → is-contr (fiber emb (E₃ f g h))
  E₃-contr f g h .center = pt-l f g h
  E₃-contr f g h .paths =
    is-contr→is-prop
      (subst (λ T → is-contr (fiber emb T))
        (ap (_· h) (emb-comp f g))
        (compose-contr (f ⨾ g) h)) _

  assoc-σ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
          → pt-l f g h ≡ pt-r f g h
  assoc-σ f g h = is-contr→is-prop (E₃-contr f g h) (pt-l f g h) (pt-r f g h)

  assoc : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
        → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h = ap fst (assoc-σ f g h)
```

## The quadruple composite and the five faces

`pentagon-fibers` fixes `f g h k` and carries the quadruple composite
`E₄`, its `subst`-manufactured contractibility `E₄c`, the five
canonical vertices `pt₁..pt₅` (right-nested binary witnesses), and the
faces. Each face reads a fiber edge `αᵢⱼ` against a named associator
through `contr-face` and a canonical lift.

The lifts: `Λk` right-whiskers by `k`, `Φ`/`Λf` left-whisker by `f`
(the `emb`-at-center link makes `Φ` commute with everything
definitionally), and `R₁₄` reindexes by the `emb-comp f g` expansion.
`reindex-face` handles the two pure-reindex faces (`face₂₃`/`face₄₅`),
building the reindex lift and both `Path.assoc` bridges internally.
`whisker-face` factors the `contr-face` + `Λ`-core skeleton but leaves
the two bridges to the caller (their segment types are face-specific);
it carries `face₁₂` and `face₃₅`, and — being generic over the lift —
also `face₁₄`, whose `homotopy-natural` `v`-bridge merely rides in as
that caller-supplied bridge (it resists `reindex-face`'s fixed
`Path.assoc` tail, not `whisker-face`).

```agda
module pentagon-tower {o h} (C : hcategory o h) where
  open hcategory C
  open assoc-tower C

  module pentagon-fibers {x y z w v}
    (f : hom x y) (g : hom y z) (h : hom z w) (k : hom w v)
    where

    E₄ : composite x v
    E₄ = emb f · g · h · k

    E₄c : is-contr (fiber emb E₄)
    E₄c .center .fst = ((f ⨾ g) ⨾ h) ⨾ k
    E₄c .center .snd =
        emb-comp ((f ⨾ g) ⨾ h) k
      ∙ ap (_· k) (emb-comp (f ⨾ g) h)
      ∙ ap (_· k) (ap (_· h) (emb-comp f g))
    E₄c .paths =
      is-contr→is-prop
        (subst (λ T → is-contr (fiber emb T)) path₄
          (compose-contr ((f ⨾ g) ⨾ h) k)) _
      where
        path₄ : emb ((f ⨾ g) ⨾ h) · k ≡ E₄
        path₄ = ap (_· k) (emb-comp (f ⨾ g) h)
              ∙ ap (_· k) (ap (_· h) (emb-comp f g))

    pt₁ : fiber emb E₄
    pt₁ = ((f ⨾ g) ⨾ h) ⨾ k
        , emb-comp ((f ⨾ g) ⨾ h) k
        ∙ ap (_· k) (emb-comp (f ⨾ g) h)
        ∙ ap (_· k) (ap (_· h) (emb-comp f g))

    pt₂ : fiber emb E₄
    pt₂ = (f ⨾ (g ⨾ h)) ⨾ k
        , emb-comp (f ⨾ (g ⨾ h)) k
        ∙ ap (_· k) (emb-comp f (g ⨾ h))
        ∙ ap (_· k) (·-comp (emb f) g h)

    pt₃ : fiber emb E₄
    pt₃ = f ⨾ ((g ⨾ h) ⨾ k)
        , emb-comp f ((g ⨾ h) ⨾ k)
        ∙ ·-comp (emb f) (g ⨾ h) k
        ∙ ap (_· k) (·-comp (emb f) g h)

    pt₄ : fiber emb E₄
    pt₄ = (f ⨾ g) ⨾ (h ⨾ k)
        , emb-comp (f ⨾ g) (h ⨾ k)
        ∙ ap (_· (h ⨾ k)) (emb-comp f g)
        ∙ ·-comp (emb f · g) h k

    pt₅ : fiber emb E₄
    pt₅ = f ⨾ (g ⨾ (h ⨾ k))
        , emb-comp f (g ⨾ (h ⨾ k))
        ∙ ·-comp (emb f) g (h ⨾ k)
        ∙ ·-comp (emb f · g) h k

    σ₁₂ = is-contr→is-prop E₄c pt₁ pt₂
    σ₂₃ = is-contr→is-prop E₄c pt₂ pt₃
    σ₁₄ = is-contr→is-prop E₄c pt₁ pt₄
    σ₄₅ = is-contr→is-prop E₄c pt₄ pt₅
    σ₃₅ = is-contr→is-prop E₄c pt₃ pt₅

    α₁₂ = ap fst σ₁₂
    α₂₃ = ap fst σ₂₃
    α₁₄ = ap fst σ₁₄
    α₄₅ = ap fst σ₄₅
    α₃₅ = ap fst σ₃₅

    -- Canonical lifts. fst ∘ L = reindex ∘ fst holds definitionally, so
    -- ap fst (ap L assoc-σ) is the intended associator.
    Λk : fiber emb (E₃ f g h) → fiber emb E₄
    Λk (m , p) = m ⨾ k , emb-comp m k ∙ ap (_· k) p

    Φ : composite y v → composite x v
    Φ L γ = emb f (γ .fst , (γ .snd .fst , L (ctr y , γ .snd)))

    Λf : fiber emb (E₃ g h k) → fiber emb E₄
    Λf (m , p) = f ⨾ m , emb-comp f m ∙ ap Φ p

    R₁₄ : fiber emb (E₃ (f ⨾ g) h k) → fiber emb E₄
    R₁₄ (m , p) = m , p ∙ ap (_· k) (ap (_· h) (emb-comp f g))

    -- reindex-face: the pure-reindex faces (both bridges Path.assoc).
    -- Given the sub-triple f' g' h' and the tail C : E₃ f' g' h' ≡ E₄,
    -- the reindex lift R (m , p) = (m , p ∙ C) and the two bridges (a
    -- Path.assoc reassociation each) are supplied internally.
    reindex-face
      : ∀ {y' z'} (f' : hom x y') (g' : hom y' z') (h' : hom z' v)
        (C : E₃ f' g' h' ≡ E₄)
        (σ : (((f' ⨾ g') ⨾ h')
                 , emb-comp (f' ⨾ g') h' ∙ ap (_· h') (emb-comp f' g') ∙ C)
           ≡ ((f' ⨾ (g' ⨾ h'))
                 , emb-comp f' (g' ⨾ h') ∙ ·-comp (emb f') g' h' ∙ C))
      → ap fst σ ≡ assoc f' g' h'
    reindex-face f' g' h' C σ =
      contr-face E₄c σ
        (Path.assoc (emb-comp (f' ⨾ g') h') (ap (_· h') (emb-comp f' g')) C)
        (λ i → R (assoc-σ f' g' h' i))
        (sym (Path.assoc (emb-comp f' (g' ⨾ h')) (·-comp (emb f') g' h') C))
      where
        R : fiber emb (E₃ f' g' h') → fiber emb E₄
        R (m , p) = m , p ∙ C

    -- whisker-face: factors the contr-face + Λ-core skeleton shared by
    -- the single-lift faces. The caller supplies the lift Λ over the
    -- sub-triple p q r and the two face-specific bridges w and v (their
    -- segment types depend on the face, so they stay caller-side). The
    -- endpoint witnesses α/β are inferred from σ.
    whisker-face
      : ∀ {x₀ y₀ z₀ w₀}
        (p : hom x₀ y₀) (q : hom y₀ z₀) (r : hom z₀ w₀)
        (Λ : fiber emb (E₃ p q r) → fiber emb E₄)
        {α : emb (Λ (pt-l p q r) .fst) ≡ E₄}
        {β : emb (Λ (pt-r p q r) .fst) ≡ E₄}
        (σ : (Λ (pt-l p q r) .fst , α) ≡ (Λ (pt-r p q r) .fst , β))
        (w : α ≡ Λ (pt-l p q r) .snd)
        (v : Λ (pt-r p q r) .snd ≡ β)
      → ap fst σ ≡ ap fst (λ i → Λ (assoc-σ p q r i))
    whisker-face p q r Λ σ w v =
      contr-face E₄c σ w (λ i → Λ (assoc-σ p q r i)) v

    -- face₁₂: right whisker. Bridges are single ap-comp distributions.
    face₁₂ : α₁₂ ≡ ap (_⨾ k) (assoc f g h)
    face₁₂ = whisker-face f g h Λk σ₁₂ w₁₂ v₁₂
      where
        w₁₂ : pt₁ .snd ≡ (Λk (pt-l f g h)) .snd
        w₁₂ = sym (ap (emb-comp ((f ⨾ g) ⨾ h) k ∙_)
          (ap-comp (_· k) (emb-comp (f ⨾ g) h) (ap (_· h) (emb-comp f g))))
        v₁₂ : (Λk (pt-r f g h)) .snd ≡ pt₂ .snd
        v₁₂ = ap (emb-comp (f ⨾ (g ⨾ h)) k ∙_)
          (ap-comp (_· k) (emb-comp f (g ⨾ h)) (·-comp (emb f) g h))

    -- face₃₅: left whisker via Φ. Bridges are single ap-comp Φ.
    face₃₅ : α₃₅ ≡ ap (f ⨾_) (assoc g h k)
    face₃₅ = whisker-face g h k Λf σ₃₅ w₃₅ v₃₅
      where
        w₃₅ : pt₃ .snd ≡ (Λf (pt-l g h k)) .snd
        w₃₅ = ap (emb-comp f ((g ⨾ h) ⨾ k) ∙_)
          (sym (ap-comp Φ (emb-comp (g ⨾ h) k) (ap (_· k) (emb-comp g h))))
        v₃₅ : (Λf (pt-r g h k)) .snd ≡ pt₅ .snd
        v₃₅ = ap (emb-comp f (g ⨾ (h ⨾ k)) ∙_)
          (ap-comp Φ (emb-comp g (h ⨾ k)) (·-comp (emb g) h k))

    -- face₂₃/face₄₅: pure reindex through reindex-face — one-liners.
    face₂₃ : α₂₃ ≡ assoc f (g ⨾ h) k
    face₂₃ = reindex-face f (g ⨾ h) k (ap (_· k) (·-comp (emb f) g h)) σ₂₃

    face₄₅ : α₄₅ ≡ assoc f g (h ⨾ k)
    face₄₅ = reindex-face f g (h ⨾ k) (·-comp (emb f · g) h k) σ₄₅

    -- face₁₄: a reindex, but its v-bridge carries the naturality square
    -- of ·-comp along emb-comp f g, so it cannot use reindex-face's fixed
    -- Path.assoc tail. It routes through whisker-face instead — that
    -- helper is generic over the lift, so R₁₄ and the naturality tail
    -- pass through as the lift and the v-bridge.
    face₁₄ : α₁₄ ≡ assoc (f ⨾ g) h k
    face₁₄ = whisker-face (f ⨾ g) h k R₁₄ σ₁₄ w₁₄ v₁₄
      where
        w₁₄ : pt₁ .snd ≡ (R₁₄ (pt-l (f ⨾ g) h k)) .snd
        w₁₄ = Path.assoc (emb-comp ((f ⨾ g) ⨾ h) k)
          (ap (_· k) (emb-comp (f ⨾ g) h))
          (ap (_· k) (ap (_· h) (emb-comp f g)))
        v₁₄ : (R₁₄ (pt-r (f ⨾ g) h k)) .snd ≡ pt₄ .snd
        v₁₄ = sym (Path.assoc A₁₄ N₁₄ C₁₄) ∙ ap (A₁₄ ∙_) nat₁₄
          where
            A₁₄ = emb-comp (f ⨾ g) (h ⨾ k)
            N₁₄ = ·-comp (emb (f ⨾ g)) h k
            C₁₄ = ap (_· k) (ap (_· h) (emb-comp f g))
            nat₁₄ = sym (homotopy-natural (λ F → ·-comp F h k) (emb-comp f g))

    -- The fiber-level pentagon and its projection.
    hom-identity : α₁₄ ∙ α₄₅ ≡ pcom (sym α₁₂) α₂₃ α₃₅
    hom-identity =
      coh-project E₄c fst (σ₁₄ ∙ σ₄₅) (pcom (sym σ₁₂) σ₂₃ σ₃₅)
        (ap-comp fst σ₁₄ σ₄₅)
        (pcom.ap (λ _ → fst) (sym σ₁₂) σ₂₃ σ₃₅)

    pentagon
      : assoc (f ⨾ g) h k ∙ assoc f g (h ⨾ k)
      ≡ ap (_⨾ k) (assoc f g h)
        ∙ assoc f (g ⨾ h) k
        ∙ ap (f ⨾_) (assoc g h k)
    pentagon =
      pcom (ap (_∙ α₄₅) face₁₄ ∙ ap (assoc (f ⨾ g) h k ∙_) face₄₅)
        hom-identity
        (λ i → pcom (sym (face₁₂ i)) (face₂₃ i) (face₃₅ i))
      ∙ pcom→∙
          (ap (_⨾ k) (assoc f g h))
          (assoc f (g ⨾ h) k)
          (ap (f ⨾_) (assoc g h k))
```
