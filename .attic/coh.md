# Coherence: Pentagon and Triangle for Cat.Virtual

## Status: DONE (fiber-level)

All definitions typecheck cleanly. Hom-level recovery via `ap-comp fst` is a future step.

## Architecture

Coherences are stated at the **fiber level** in `fiber emb target`, where
`target` is the fully-expanded ternary sandwich expression. In a contractible
fiber, `is-contr→is-set` gives us that any two paths between the same endpoints
are equal — coherences are free.

## Definitions

### Unit laws

`unitr f` and `unitl f` are `ap fst` of the canonical path in `emb-image-contr f`
between `(f ⨾ idn, witness)` / `(idn ⨾ f, witness)` and `(f, refl)`.

### Associator

`E₃ f g h = λ w a v b → emb f w a v (noy g v (noy h v b))` is the fully-expanded
triple composite target. `E₃-contr` is derived from `composable-contr (f ⨾ g) h`
via `subst` along pointwise `emb-composite-pt f g`.

`assoc f g h = ap fst (is-contr→is-prop (E₃-contr f g h) lhs rhs)`

### Pentagon (fiber-level)

`E₄ f g h k = λ w a v b → emb f w a v (noy g v (noy h v (noy k v b)))` is the
4-fold target. `E₄-contr` from `composable-contr ((f ⨾ g) ⨾ h) k` via two
`emb-composite-pt` transports.

Five fiber points `pt₁`–`pt₅` for five bracketings. Five sigma edges
`σᵢⱼ = is-contr→is-prop E₄c ptᵢ ptⱼ`. Five hom edges `αᵢⱼ = ap fst σᵢⱼ`.

    identity : σ₁₄ ∙ σ₄₅ ≡ σ₁₂ ∙ σ₂₃ ∙ σ₃₅

by `is-contr→is-set E₄c pt₁ pt₅`.

### Triangle (fiber-level)

Three fiber points in `composable-contr f g` for `(f ⨾ idn) ⨾ g`,
`f ⨾ (idn ⨾ g)`, and `f ⨾ g`.

    identity : σ₁₃ ≡ σ₁₂ ∙ σ₂₃

by `is-contr→is-set cc pt₁ pt₃`.

## Why fiber-level, not hom-level

`ap fst` does NOT distribute over `_∙_` definitionally when the
contractibility proof uses `subst` (which introduces `transp` that doesn't
reduce due to `no-eta-equality` on the category record). The hom-level
statement `α₁₄ ∙ α₄₅ ≡ α₁₂ ∙ α₂₃ ∙ α₃₅` can be recovered via an
`ap-comp fst` lemma from `Core.Path.Base`.

## Dependency order

    composable-contr, emb-composite, noy-composite, emb-image-contr  (existing)
        │
        ├── E₃-contr  ←  subst along emb-composite-pt
        ├── E₄-contr  ←  subst along emb-composite-pt (×2)
        │
        ├── assoc     ←  ap fst ∘ is-contr→is-prop E₃-contr
        ├── unitr     ←  ap fst ∘ is-contr→is-prop emb-image-contr
        ├── unitl     ←  ap fst ∘ is-contr→is-prop emb-image-contr
        │
        ├── pentagon  ←  is-contr→is-set E₄-contr
        └── triangle  ←  is-contr→is-set composable-contr

## No new axioms

Everything derives from existing `composable-contr` + `emb-image-contr`.
