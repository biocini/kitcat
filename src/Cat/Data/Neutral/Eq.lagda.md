The enriched homothetic relation `_∻_`, bundling per-morphism
associator data (left-associativity, right-associativity, and
mediality) alongside neutrality. Adding mediality forces the loop
and coloop derived from a neutral morphism to be two-sided units at
their respective endpoints, which gives us symmetry of `_∻_` without
global associativity.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

open import Cat.Data.Magmoid
import Cat.Data.Base as M
import Cat.Data.Neutral as N

module Cat.Data.Neutral.Eq (M : magmoids) where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.HLevel
open import Core.Kan
open import Core.Transport
open import Core.Equiv

open M M
open N M
```

Each component beyond neutrality captures a different associator
position for f. The segal-based `is-thunkable` and `is-linear` from
`Cat.Data.Base` are recoverable: mediality wraps to segal
thunkability, and right-associativity wraps to segal linearity.

```agda
is-left-assoc
  : ∀ {x y} → hom x y → Type (o ⊔ h)
is-left-assoc f =
  ∀ {a b} (g : hom _ a) (h : hom a b) → associator f g h

is-right-assoc
  : ∀ {x y} → hom x y → Type (o ⊔ h)
is-right-assoc {x} f =
  ∀ {w a} (g : hom w a) (h : hom a x) → associator g h f

_∻_ : ob → ob → Type (o ⊔ h)
a ∻ b = Σ f ∶ hom a b
  , is-neutral f
  × is-left-assoc f
  × is-right-assoc f
  × is-medial f

∻→≐ : ∀ {a b} → a ∻ b → a ≐ b
∻→≐ (f , n , _) = f , n
```

Segal witnesses derived from the associator data.

```agda
module ∻-segal
  {x y} {f : hom x y}
  (ft : is-left-assoc f)
  (fl : is-right-assoc f)
  (fm : is-medial f)
  where

  to-thunkable : is-thunkable f
  to-thunkable g i w k = fm k g i

  to-linear : is-linear f
  to-linear g i w k = fl k g i
```

Composition of `∻`-morphisms.

```agda
∻-cat
  : ∀ {a b c} → a ∻ b → b ∻ c → a ∻ c
∻-cat
  {a} {b} {c}
  (f , fn , ft , fl , fm)
  (g , gn , gt , gl , gm) = f ⨾ g , cn , ct , cl , cm
  where
    coh : comp-coh f g
    coh = (λ k → fm k g) , (λ h → ft g h)

    cn : is-neutral (f ⨾ g)
    cn = composable.comp-is-neutral coh fn gn

    ct : is-left-assoc (f ⨾ g)
    ct α β =
      sym (ft g (α ⨾ β))
      ∙ f ◃ gt α β
      ∙ ft (g ⨾ α) β
      ∙ ft g α ▹ β

    cl : is-right-assoc (f ⨾ g)
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

    inv-t : is-left-assoc inv
    inv-t g h = divl→lcancel (en .fst)
      (et inv (g ⨾ h)
        ∙ e⨾inv≡coloop ▹ (g ⨾ h)
        ∙ is-medial→coloop-unitl em (g ⨾ h)
        ∙ sym (is-medial→coloop-unitl em g ▹ h)
        ∙ sym (e⨾inv≡coloop ▹ g) ▹ h
        ∙ sym (et inv g) ▹ h
        ∙ sym (et (inv ⨾ g) h))

    inv-l : is-right-assoc inv
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

module from-assoc (assoc' : associativity) where

  ≐→∻ : ∀ {a b} → a ≐ b → a ∻ b
  ≐→∻ (f , n) =
    f , n
    , (λ g h → assoc' f g h)
    , (λ g h → assoc' g h f)
    , (λ g h → assoc' g f h)
```
