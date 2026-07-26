The enriched homothetic relation `_∻_`, bundling per-morphism
associator data (thunkability, linearity, and mediality) alongside
neutrality. Adding mediality forces the loop and coloop derived
from a neutral morphism to be two-sided units at their respective
endpoints, which gives us symmetry of `_∻_` without global
associativity.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Data.Magmoid
import Cat.Data.Base as M
import Cat.Data.Neutral as N

module Cat.Data.Neutral.Eq (M : Magmoids) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv

open M M
open N M

_∻_ : ob → ob → Type (o ⊔ h)
a ∻ b = Σ f ∶ hom a b , is-neutral f × is-thunkable f × is-linear f × is-medial f

∻→≐ : ∀ {a b} → a ∻ b → a ≐ b
∻→≐ (f , n , _) = f , n

∻-cat
  : ∀ {a b c} → a ∻ b → b ∻ c → a ∻ c
∻-cat
  {a} {b} {c}
  (f , fn , ft , fl , fm)
  (g , gn , gt , gl , gm) = f ⨾ g , cn , ct , cl , cm
  where
    coh : composable f g
    coh = (λ h → gl h f) , (λ k → ft g k)

    cn : is-neutral (f ⨾ g)
    cn = composable.comp-is-neutral coh fn gn

    ct : is-thunkable (f ⨾ g)
    ct h k =
      sym (ft g (h ⨾ k))
      ∙ f ◃ gt h k
      ∙ ft (g ⨾ h) k
      ∙ ft g h ▹ k

    cl : is-linear (f ⨾ g)
    cl α β =
      α ◃ gl β f
      ∙ gl α (β ⨾ f)
      ∙ fl α β ▹ g
      ∙ sym (gl (α ⨾ β) f)

    cm : is-medial (f ⨾ g)
    cm α β =
      α ◃ sym (ft g β)
      ∙ fm α (g ⨾ β)
      ∙ gm (α ⨾ f) β
      ∙ sym (fm α g) ▹ β
```

Symmetry of `_∻_`. The inverse morphism is `divr loop`.

```agda
∻-sym : ∀ {a b} → a ∻ b → b ∻ a
∻-sym {a} {b} (e , en , et , el , em) =
  inv , inv-n , inv-t , inv-l , inv-m
  where
    open is-neutral en

    inv : hom b a
    inv = divr loop

    e⨾inv≡coloop : e ⨾ inv ≡ coloop
    e⨾inv≡coloop = divr→rcancel (en .snd)
      (sym (et inv e)
        ∙ e ◃ post-counit loop
        ∙ pre-counit e
        ∙ sym (post-counit e))

    inv-ldiv : is-right-divisible inv
    inv-ldiv = iso→equiv (_⨾ inv) (_⨾ e)
      (λ f →
        sym (el f inv)
        ∙ f ◃ post-counit loop
        ∙ is-medial→loop-unitr em f)
      (λ g →
        sym (em g inv)
        ∙ g ◃ e⨾inv≡coloop
        ∙ is-linear→coloop-unitr el g) .snd

    inv-rdiv : is-left-divisible inv
    inv-rdiv = iso→equiv (inv ⨾_) (e ⨾_)
      (λ h →
        et inv h
        ∙ e⨾inv≡coloop ▹ h
        ∙ is-medial→coloop-unitl em h)
      (λ g →
        em inv g
        ∙ post-counit loop ▹ g
        ∙ is-thunkable→loop-unitl et g) .snd

    inv-n : is-neutral inv
    inv-n = inv-rdiv , inv-ldiv

    inv-t : is-thunkable inv
    inv-t g h = divl→lcancel (en .fst)
      (et inv (g ⨾ h)
        ∙ e⨾inv≡coloop ▹ (g ⨾ h)
        ∙ is-medial→coloop-unitl em (g ⨾ h)
        ∙ sym (is-medial→coloop-unitl em g ▹ h)
        ∙ sym (e⨾inv≡coloop ▹ g) ▹ h
        ∙ sym (et inv g) ▹ h
        ∙ sym (et (inv ⨾ g) h))

    inv-l : is-linear inv
    inv-l f g = divr→rcancel (en .snd)
      (sym (el f (g ⨾ inv))
        ∙ f ◃ sym (el g inv)
        ∙ f ◃ (g ◃ post-counit loop)
        ∙ f ◃ is-medial→loop-unitr em g
        ∙ sym (is-medial→loop-unitr em (f ⨾ g))
        ∙ sym ((f ⨾ g) ◃ post-counit loop)
        ∙ el (f ⨾ g) inv)

    inv-m : is-medial inv
    inv-m {w} {z} f g =
      sym (post-counit f) ▹ (inv ⨾ g)
      ∙ step₀
      ∙ (post-counit f ▹ inv) ▹ g
      where
        step₀
          : (divr f ⨾ e) ⨾ (inv ⨾ g) ≡ ((divr f ⨾ e) ⨾ inv) ⨾ g
        step₀ =
          sym (em (divr f) (inv ⨾ g))
          ∙ divr f ◃ (et inv g)
          ∙ divr f ◃ (e⨾inv≡coloop ▹ g)
          ∙ divr f ◃ is-medial→coloop-unitl em g
          ∙ sym (is-linear→coloop-unitr el (divr f) ▹ g)
          ∙ sym (divr f ◃ e⨾inv≡coloop) ▹ g
          ∙ em (divr f) inv ▹ g

module from-assoc (assoc : associativity) where

  ≐→∻ : ∀ {a b} → a ≐ b → a ∻ b
  ≐→∻ (f , n) =
    f , n
    , (λ g h → assoc f g h)
    , (λ g h → assoc g h f)
    , (λ g h → assoc g f h)
```
