# Fiber-level pentagon and triangle (preserved)

These are the original fiber-level coherences before the fused-witness
redesign. The pentagon/triangle identities hold at the sigma level in
contractible fibers. The edges (αᵢⱼ = ap fst σᵢⱼ) are E₄-canonical
reassociations, NOT the E₃-derived assoc. Relating them to the
classical pentagon requires the face-compatibility work that motivated
the redesign.

## Code (from Cat.Virtual lines 436-614)

```agda
  private
    E₄ : ∀ {x y z w v} (f : hom x y) (g : hom y z)
        (h : hom z w) (k : hom w v)
      → ∀ w' → hom w' x → ∀ v' → hom v v' → hom w' v'
    E₄ f g h k =
      λ w a v b →
        emb f w a v (noy g v (noy h v (noy k v b)))

  E₄-contr
    : ∀ {x y z w v} (f : hom x y) (g : hom y z)
      (h : hom z w) (k : hom w v)
    → is-contr (fiber emb (E₄ f g h k))
  E₄-contr f g h k =
    subst (is-contr ∘ fiber emb) path
      (composable-contr ((f ⨾ g) ⨾ h) k)
    where
      path
        : (λ w a v b →
            emb ((f ⨾ g) ⨾ h) w a v (noy k v b))
        ≡ E₄ f g h k
      path = funext λ w → funext λ a →
        funext λ v → funext λ b →
          emb-composite-pt (f ⨾ g) h w a v (noy k v b)
        ∙ emb-composite-pt f g w a v
            (noy h v (noy k v b))

  module pentagon
    {x y z w v}
    (f : hom x y) (g : hom y z)
    (h : hom z w) (k : hom w v)
    where
    private
      E₄c = E₄-contr f g h k

      pt₁ : fiber emb (E₄ f g h k)
      pt₁ = ((f ⨾ g) ⨾ h) ⨾ k
          , emb-composite ((f ⨾ g) ⨾ h) k
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              emb-composite-pt (f ⨾ g) h w a v
                (noy k v b)
            ∙ emb-composite-pt f g w a v
                (noy h v (noy k v b))

      pt₂ : fiber emb (E₄ f g h k)
      pt₂ = (f ⨾ (g ⨾ h)) ⨾ k
          , emb-composite (f ⨾ (g ⨾ h)) k
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              emb-composite-pt f (g ⨾ h) w a v
                (noy k v b)
            ∙ ap (emb f w a v)
                (noy-composite g h (noy k v b))

      pt₃ : fiber emb (E₄ f g h k)
      pt₃ = f ⨾ ((g ⨾ h) ⨾ k)
          , emb-composite f ((g ⨾ h) ⨾ k)
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              ap (emb f w a v)
                (noy-composite (g ⨾ h) k b)
            ∙ ap (emb f w a v)
                (noy-composite g h (noy k v b))

      pt₄ : fiber emb (E₄ f g h k)
      pt₄ = (f ⨾ g) ⨾ (h ⨾ k)
          , emb-composite (f ⨾ g) (h ⨾ k)
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              emb-composite-pt f g w a v
                (noy (h ⨾ k) v b)
            ∙ ap (λ t → emb f w a v (noy g v t))
                  (noy-composite h k b)

      pt₅ : fiber emb (E₄ f g h k)
      pt₅ = f ⨾ (g ⨾ (h ⨾ k))
          , emb-composite f (g ⨾ (h ⨾ k))
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              ap (emb f w a v)
                (noy-composite g (h ⨾ k) b)
            ∙ ap (λ t → emb f w a v (noy g v t))
                  (noy-composite h k b)

    σ₁₄ : pt₁ ≡ pt₄
    σ₁₄ = is-contr→is-prop E₄c pt₁ pt₄

    σ₄₅ : pt₄ ≡ pt₅
    σ₄₅ = is-contr→is-prop E₄c pt₄ pt₅

    σ₁₂ : pt₁ ≡ pt₂
    σ₁₂ = is-contr→is-prop E₄c pt₁ pt₂

    σ₂₃ : pt₂ ≡ pt₃
    σ₂₃ = is-contr→is-prop E₄c pt₂ pt₃

    σ₃₅ : pt₃ ≡ pt₅
    σ₃₅ = is-contr→is-prop E₄c pt₃ pt₅

    α₁₄ : ((f ⨾ g) ⨾ h) ⨾ k ≡ (f ⨾ g) ⨾ (h ⨾ k)
    α₁₄ = ap fst σ₁₄

    α₄₅ : (f ⨾ g) ⨾ (h ⨾ k) ≡ f ⨾ (g ⨾ (h ⨾ k))
    α₄₅ = ap fst σ₄₅

    α₁₂ : ((f ⨾ g) ⨾ h) ⨾ k ≡ (f ⨾ (g ⨾ h)) ⨾ k
    α₁₂ = ap fst σ₁₂

    α₂₃ : (f ⨾ (g ⨾ h)) ⨾ k ≡ f ⨾ ((g ⨾ h) ⨾ k)
    α₂₃ = ap fst σ₂₃

    α₃₅ : f ⨾ ((g ⨾ h) ⨾ k) ≡ f ⨾ (g ⨾ (h ⨾ k))
    α₃₅ = ap fst σ₃₅

    identity : σ₁₄ ∙ σ₄₅ ≡ σ₁₂ ∙ σ₂₃ ∙ σ₃₅
    identity = is-contr→is-set E₄c pt₁ pt₅
      (σ₁₄ ∙ σ₄₅) (σ₁₂ ∙ σ₂₃ ∙ σ₃₅)

  module triangle
    {x y z} (f : hom x y) (g : hom y z)
    where
    private
      cc = composable-contr f g

      pt₁ : fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      pt₁ = (f ⨾ idn) ⨾ g
          , emb-composite (f ⨾ idn) g
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              emb-composite-pt f idn w a v (noy g v b)
            ∙ ap (emb f w a v) (absorb-l (noy g v b))

      pt₂ : fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      pt₂ = f ⨾ (idn ⨾ g)
          , emb-composite f (idn ⨾ g)
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              ap (emb f w a v)
                (noy-composite idn g b)
            ∙ ap (emb f w a v) (absorb-l (noy g v b))

      pt₃ : fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      pt₃ = f ⨾ g , emb-composite f g

    σ₁₃ : pt₁ ≡ pt₃
    σ₁₃ = is-contr→is-prop cc pt₁ pt₃

    σ₁₂ : pt₁ ≡ pt₂
    σ₁₂ = is-contr→is-prop cc pt₁ pt₂

    σ₂₃ : pt₂ ≡ pt₃
    σ₂₃ = is-contr→is-prop cc pt₂ pt₃

    α₁₃ : (f ⨾ idn) ⨾ g ≡ f ⨾ g
    α₁₃ = ap fst σ₁₃

    α₁₂ : (f ⨾ idn) ⨾ g ≡ f ⨾ (idn ⨾ g)
    α₁₂ = ap fst σ₁₂

    α₂₃ : f ⨾ (idn ⨾ g) ≡ f ⨾ g
    α₂₃ = ap fst σ₂₃

    identity : σ₁₃ ≡ σ₁₂ ∙ σ₂₃
    identity = is-contr→is-set cc pt₁ pt₃
      σ₁₃ (σ₁₂ ∙ σ₂₃)
```
