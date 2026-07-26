Lane Biocini
March 2026

Categories via binary operations `noy`/`yon` with derived ternary
`emb`. The `noy-assoc` and `yon-assoc` fields witness associativity
of the binary operations, enabling absorption laws from a minimal
unit condition: yon-idempotency plus equivalences.

The absorption chain is non-circular:
`yon-idpt → yon-absorb → emb-image-contr → unitr → noy-absorb`.

The `unit-is-prop` result follows Kraus (2020), "Internal
infinity-Categorical Models of Dependent Type Theory", adapted
to the binary-operation setting.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.VirtualAlt where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport
open import Core.Function.Base
open import Core.Path.Base
open import Core.Groupoid.Virtual
open import Core.Equiv.Base
  using (is-equiv; eqv-fibers; _≃_; Equiv; is-contr-equiv; iso→equiv)
open import Core.Equiv.Properties
  using (is-equiv-is-prop; Σ-equiv-snd; Σ-assoc; Σ-contr-fst;
         path-equiv-r; path-sym-equiv; esym; _∙e_)
open import Core.Function.Embedding
  using (equiv→lc; is-equiv→is-embedding; is-embedding→ap-equiv)
open import Core.HLevel.Base
  using (is-prop-×; is-prop-equiv)
open import Core.Trait.Trunc using (Πi-is-prop)
```

## The category record

```agda
record category o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    noy : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
    yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
    interchange
      : ∀ {x y} (f : hom x y)
        w (a : hom w x) v (b : hom y v)
      → yon (noy f v b) w a ≡ noy (yon f w a) v b
    noy-assoc
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        v (h : hom z v)
      → noy f v (noy g v h) ≡ noy (noy f z g) v h
    yon-assoc
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        w (a : hom w x)
      → yon g w (yon f w a) ≡ yon (yon g x f) w a

  emb : ∀ {x y} → hom x y
      → ∀ w → hom w x → ∀ z → hom y z → hom w z
  emb f w a v b = noy (yon f w a) v b

  field
    compose-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr
          (Σ s ∶ hom x z
          , (emb s
            ≡ (λ w a v b → emb f w a v (noy g v b)))
          × (emb s
            ≡ (λ w a v b →
                emb g w (yon f w a) v b)))

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = compose-contr f g .center .fst
  infixr 40 _⨾_

  emb-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g)
    ≡ (λ w a v b → emb f w a v (noy g v b))
  emb-composite f g =
    compose-contr f g .center .snd .fst

  emb-yon-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g)
    ≡ (λ w a v b → emb g w (yon f w a) v b)
  emb-yon-composite f g =
    compose-contr f g .center .snd .snd

  emb-composite-pt
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x) v (b : hom z v)
    → emb (f ⨾ g) w a v b
    ≡ emb f w a v (noy g v b)
  emb-composite-pt f g w a v b i =
    emb-composite f g i w a v b

  emb-yon-composite-pt
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x) v (b : hom z v)
    → emb (f ⨾ g) w a v b
    ≡ emb g w (yon f w a) v b
  emb-yon-composite-pt f g w a v b i =
    emb-yon-composite f g i w a v b

  emb-interchange
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x) v (b : hom z v)
    → emb f w a v (noy g v b)
    ≡ emb g w (yon f w a) v b
  emb-interchange f g w a v b =
    sym (emb-composite-pt f g w a v b)
    ∙ emb-yon-composite-pt f g w a v b

  field
    unit : ∀ {x} →
      Σ e ∶ hom x x
      , (yon e x e ≡ e)
      × (∀ {z} → is-equiv (noy e z))
      × (∀ {w} → is-equiv (yon e w))

  idn : ∀ {x} → hom x x
  idn = unit .fst

  private
    yon-idpt : ∀ {x} → yon (idn {x}) x idn ≡ idn
    yon-idpt = unit .snd .fst

    noy-eqv : ∀ {x z} → is-equiv (noy (idn {x}) z)
    noy-eqv = unit .snd .snd .fst

    yon-eqv : ∀ {x w} → is-equiv (yon (idn {x}) w)
    yon-eqv = unit .snd .snd .snd

  yon-absorb : ∀ {x w} (a : hom w x) → yon idn w a ≡ a
  yon-absorb a =
    equiv→lc yon-eqv
      (yon-assoc idn idn _ a
      ∙ ap (λ t → yon t _ a) yon-idpt)

  private
    -- yon idn is idempotent: yon idn w (yon idn w a) ≡ yon idn w a
    -- follows from yon-assoc + yon-idpt. Used to build compose-contr witness.
    yon-sq : ∀ {x w} (a : hom w x)
      → yon idn w a ≡ yon idn w (yon idn w a)
    yon-sq a = sym (yon-assoc idn idn _ a
      ∙ ap (λ t → yon t _ a) yon-idpt)

    idem : ∀ {x} → idn {x} ⨾ idn ≡ idn
    idem = ap fst (compose-contr idn idn .paths (idn , p₁ , p₂))
      where
        p₂ : emb idn ≡ (λ w a v b → emb idn w (yon idn w a) v b)
        p₂ = funext λ w → funext λ a → funext λ v → funext λ b →
          ap (λ t → noy t v b) (yon-sq a)

        p₁ : emb idn ≡ (λ w a v b → emb idn w a v (noy idn v b))
        p₁ = p₂ ∙ sym (funext λ w → funext λ a →
          funext λ v → funext λ b →
            emb-interchange idn idn w a v b)

  noy-absorb : ∀ {x z} (f : hom x z) → noy idn z f ≡ f
  noy-absorb {x} {z} f = equiv→lc noy-eqv step
    where
      step : noy idn z (noy idn z f) ≡ noy idn z f
      step =
        ap (λ t → noy t z (noy idn z f)) (sym yon-idpt)
        ∙ sym (emb-composite-pt idn idn x idn z f)
        ∙ ap (λ e → noy (yon e x idn) z f) idem
        ∙ ap (λ t → noy t z f) yon-idpt

  absorb-l : ∀ {x} {z : ob} (h : hom x z)
    → emb idn _ idn z h ≡ h
  absorb-l h =
    ap (λ t → noy t _ h) (yon-absorb idn)
    ∙ noy-absorb h

  absorb-r : ∀ {x} {w : ob} (g : hom w x)
    → emb idn w g _ idn ≡ g
  absorb-r {w = w} g =
    sym (interchange idn w g _ idn)
    ∙ ap (λ t → yon t w g) (noy-absorb idn)
    ∙ yon-absorb g

{-# INLINE category.emb #-}
{-# INLINE category._⨾_ #-}
```

## Derived operations

```agda
module Cat {o} {h} (C : category o h) where
  open category C public

  composable-contr
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-contr
        (fiber (emb {x} {z})
          (λ w a v b → emb f w a v (noy g v b)))
  composable-contr f g .center =
    f ⨾ g , emb-composite f g
  composable-contr f g .paths (s , p) =
    λ i → path i .fst , path i .snd .fst
    where
      path = compose-contr f g .paths
        (s , p , p ∙ funext λ w → funext λ a →
          funext λ v → funext λ b →
            emb-interchange f g w a v b)
```

### Embedding property

```agda
  emb-image-contr
    : ∀ {x y} (f : hom x y)
    → is-contr (fiber emb (emb f))
  emb-image-contr f =
    subst (is-contr ∘ fiber emb) path
      (composable-contr idn f)
    where
      path
        : (λ w a v b → emb idn w a v (noy f v b))
        ≡ emb f
      path = funext λ w → funext λ a →
        funext λ v → funext λ b →
          emb-interchange idn f w a v b
          ∙ ap (λ t → emb f w t v b) (yon-absorb a)

  composable-yon
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → is-contr
        (fiber emb
          (λ w a v b → emb g w (yon f w a) v b))
  composable-yon f g =
    subst (is-contr ∘ fiber emb) path
      (composable-contr f g)
    where
      path
        : (λ w a v b → emb f w a v (noy g v b))
        ≡ (λ w a v b → emb g w (yon f w a) v b)
      path = funext λ w → funext λ a → funext λ v →
        funext λ b → emb-interchange f g w a v b
```

### Induction principles

```agda
  emb-ind
    : ∀ {u} {x y z} (f : hom x y) (g : hom y z)
    → (P : (s : hom x z)
         → emb s
           ≡ (λ w a v b → emb f w a v (noy g v b))
         → Type u)
    → P (f ⨾ g) (emb-composite f g)
    → ∀ s q → P s q
  emb-ind f g P base s q =
    contr-ind (composable-contr f g)
      (λ where (s , q) → P s q)
      base (s , q)

  ⨾-η
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → (s : hom x z)
    → emb s
      ≡ (λ w a v b → emb f w a v (noy g v b))
    → f ⨾ g ≡ s
  ⨾-η f g = emb-ind f g (λ s _ → f ⨾ g ≡ s) refl

  emb-image-ind
    : ∀ {u} {x y} (m : hom x y)
    → (P : (n : hom x y)
         → emb n ≡ emb m → Type u)
    → P m refl
    → ∀ n q → P n q
  emb-image-ind m P base n q =
    coe01 (λ i → P (path i .fst) (path i .snd))
      base
    where
      path : (m , refl) ≡ (n , q)
      path =
        sym (emb-image-contr m .paths (m , refl))
        ∙ emb-image-contr m .paths (n , q)

  emb-inj
    : ∀ {x y} {f g : hom x y}
    → emb f ≡ emb g → f ≡ g
  emb-inj {f = f} {g} p =
    emb-image-ind f
      (λ n _ → f ≡ n) refl g (sym p)
```

### Decomposition lemmas

```agda
  emb-yon
    : ∀ {x y} (f : hom x y)
      w (a : hom w x) v (b : hom y v)
    → emb f w a v b ≡ emb idn w (yon f w a) v b
  emb-yon f w a v b =
    ap (emb f w a v) (sym (noy-absorb b))
    ∙ emb-interchange f idn w a v b

  emb-noy
    : ∀ {x y} (f : hom x y)
      w (a : hom w x) v (b : hom y v)
    → emb f w a v b ≡ emb idn w a v (noy f v b)
  emb-noy f w a v b =
    ap (λ t → emb f w t v b) (sym (yon-absorb a))
    ∙ sym (emb-interchange idn f w a v b)
```

### Injectivity

```agda
  yon-inj
    : ∀ {x y} {f g : hom x y}
    → yon f ≡ yon g → f ≡ g
  yon-inj {f = f} {g} p = emb-inj
    (funext λ w → funext λ a → funext λ v →
      funext λ b →
        emb-yon f w a v b
        ∙ ap (λ t → emb idn w t v b)
            (λ i → p i w a)
        ∙ sym (emb-yon g w a v b))

  noy-inj
    : ∀ {x y} {f g : hom x y}
    → noy f ≡ noy g → f ≡ g
  noy-inj {f = f} {g} p = emb-inj
    (funext λ w → funext λ a → funext λ v →
      funext λ b →
        emb-noy f w a v b
        ∙ ap (λ t → emb idn w a v t)
            (λ i → p i v b)
        ∙ sym (emb-noy g w a v b))
```

### Distribution over composition

```agda
  noy-composite
    : ∀ {x y z} (g : hom x y) (h : hom y z)
      {v : ob} (b : hom z v)
    → noy (g ⨾ h) v b ≡ noy g v (noy h v b)
  noy-composite g h {v} b = yon-inj
    (funext λ w' → funext λ a' →
      interchange (g ⨾ h) w' a' v b
      ∙ emb-composite-pt g h w' a' v b
      ∙ sym (interchange g w' a' v (noy h v b)))

  yon-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
      w (a : hom w x)
    → yon (f ⨾ g) w a ≡ yon g w (yon f w a)
  yon-composite f g w a = noy-inj
    (funext λ v' → funext λ b' →
      emb-yon-composite-pt f g w a v' b')
```

### Unit laws and associativity

```agda
  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn ≡ f
  unitr f =
    ap fst
      (is-contr→is-prop
        (emb-image-contr f) lhs rhs)
    where
      lhs : fiber emb (emb f)
      lhs = f ⨾ idn
          , emb-composite f idn
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              ap (emb f w a v) (noy-absorb b)

      rhs : fiber emb (emb f)
      rhs = f , refl

  unitl : ∀ {x y} (f : hom x y) → idn ⨾ f ≡ f
  unitl f =
    ap fst
      (is-contr→is-prop (composable-contr idn f)
        lhs rhs)
    where
      lhs : fiber emb
        (λ w a v b → emb idn w a v (noy f v b))
      lhs = idn ⨾ f , emb-composite idn f

      rhs : fiber emb
        (λ w a v b → emb idn w a v (noy f v b))
      rhs = f , funext λ w → funext λ a →
        funext λ v → funext λ b →
          emb-noy f w a v b

  private
    E₃ : ∀ {x y z w} (f : hom x y) (g : hom y z)
        (h : hom z w)
      → ∀ w' → hom w' x → ∀ v → hom w v → hom w' v
    E₃ f g h =
      λ w a v b →
        emb f w a v (noy g v (noy h v b))

  E₃-contr
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → is-contr (fiber emb (E₃ f g h))
  E₃-contr f g h =
    subst (is-contr ∘ fiber emb) path
      (composable-contr (f ⨾ g) h)
    where
      path
        : (λ w a v b →
            emb (f ⨾ g) w a v (noy h v b))
        ≡ E₃ f g h
      path = funext λ w → funext λ a →
        funext λ v → funext λ b →
          emb-composite-pt f g w a v (noy h v b)

  assoc
    : ∀ {x y z w} (f : hom x y) (g : hom y z)
      (h : hom z w)
    → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h =
    ap fst
      (is-contr→is-prop (E₃-contr f g h) lhs rhs)
    where
      lhs : fiber emb (E₃ f g h)
      lhs = (f ⨾ g) ⨾ h
          , emb-composite (f ⨾ g) h
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              emb-composite-pt f g w a v (noy h v b)

      rhs : fiber emb (E₃ f g h)
      rhs = f ⨾ (g ⨾ h)
          , emb-composite f (g ⨾ h)
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              ap (emb f w a v)
                (noy-composite g h b)
```

### Right-unit absorption for yon/noy

The identity morphism absorbs on the right of `yon` and `noy`:
`yon f x idn ≡ f` and `noy f y idn ≡ f`. These follow from
the binary associativity fields and the left-absorption laws.

```agda
  yon-unit : ∀ {x y} (f : hom x y) → yon f x idn ≡ f
  yon-unit f = yon-inj (funext λ w → funext λ a →
    sym (yon-assoc idn f w a) ∙ ap (yon f w) (yon-absorb a))

  noy-unit : ∀ {x y} (f : hom x y) → noy f y idn ≡ f
  noy-unit f = noy-inj (funext λ v → funext λ b →
    sym (noy-assoc f idn v b) ∙ ap (noy f v) (noy-absorb b))
```

### Identity uniqueness

Both `emb e₂` and `emb idn` reduce pointwise to
`λ w a v b → noy a v b` under their respective
yon-absorptions. So `emb-inj` gives `idn ≡ e₂`.

```agda
  idn-unique
    : ∀ {x} (e₂ : hom x x)
    → (∀ {w} (a : hom w x) → yon e₂ w a ≡ a)
    → idn ≡ e₂
  idn-unique e₂ yon-abs₂ = emb-inj (sym p) where
    p : emb e₂ ≡ emb idn
    p = funext λ w → funext λ a →
      funext λ v → funext λ b →
        ap (λ t → noy t v b) (yon-abs₂ a)
        ∙ sym (ap (λ t → noy t v b) (yon-absorb a))
```

### Unit is propositional

Following Kraus (2020), "Internal ∞-Categorical Models of
Dependent Type Theory". The type of idempotent equivalences
is contractible when inhabited, hence propositional.

```agda
  private
    is-eqv : ∀ {x} → hom x x → Type _
    is-eqv e =
      (∀ {z} → is-equiv (noy e z))
      × (∀ {w} → is-equiv (yon e w))

    unit-data : ob → Type _
    unit-data x =
      Σ e ∶ hom x x
      , (yon e x e ≡ e) × is-eqv e

    is-eqv-is-prop : ∀ {x} (e : hom x x)
      → is-prop (is-eqv e)
    is-eqv-is-prop e = is-prop-×
      (Πi-is-prop λ _ → is-equiv-is-prop _)
      (Πi-is-prop λ _ → is-equiv-is-prop _)
```

For any `e` with `is-equiv (yon e w)`, the retract
`I(e) = Equiv.inv (yon e x) e` has yon-absorb and
hence equals `idn` by `idn-unique`.

```agda
  module I-construction
    {x : ob} (e : hom x x)
    (yon-eqv-e : ∀ {w} → is-equiv (yon e w))
    where
    private module Ye = Equiv (yon e x , yon-eqv-e)

    I-e : hom x x
    I-e = Ye.inv e

    counit-e : yon e x I-e ≡ e
    counit-e = Ye.counit e

    I-yon-absorb
      : ∀ {w} (a : hom w x) → yon I-e w a ≡ a
    I-yon-absorb a =
      equiv→lc yon-eqv-e
        (yon-assoc I-e e _ a
        ∙ ap (λ t → yon t _ a) counit-e)

    I-eq-idn : idn ≡ I-e
    I-eq-idn = idn-unique I-e I-yon-absorb
```

The idempotency condition `yon e x e ≡ e` is equivalent
to `e ≡ I(e)` via the ap-equivalence of the embedding
`yon e x`, composed with right-translation by the
counit. Since `I(e) ≡ idn`, this further reduces to
`e ≡ idn`.

```agda
    e-I-idpt : (yon e x e ≡ e) ≃ (e ≡ I-e)
    e-I-idpt =
      esym (path-equiv-r counit-e)
      ∙e esym (ap-eqv , is-embedding→ap-equiv
            (is-equiv→is-embedding yon-eqv-e))
      where
        ap-eqv : e ≡ I-e → yon e x e ≡ yon e x I-e
        ap-eqv = ap (yon e x)

    e-idn-idpt : (yon e x e ≡ e) ≃ (e ≡ idn)
    e-idn-idpt = e-I-idpt ∙e path-equiv-r (sym I-eq-idn)
```

We show `unit-data x` is contractible when inhabited by
chaining equivalences to a propositional type, following
Kraus's argument. The chain reassociates the Σ-type to
separate out `e ≡ idn`, contracts the singleton, and
leaves `is-eqv idn` which is propositional.

```agda
  private
    ×-comm-equiv
      : ∀ {u v} {A : Type u} {B : Type v}
      → (A × B) ≃ (B × A)
    ×-comm-equiv = iso→equiv
      (λ (a , b) → b , a)
      (λ (b , a) → a , b)
      (λ _ → refl) (λ _ → refl)

  unit-is-prop : ∀ {x} → is-prop (unit-data x)
  unit-is-prop {x} = is-prop-equiv chain (is-eqv-is-prop idn)
    where
      open I-construction

      -- Σ e, (yon e x e ≡ e) × is-eqv e
      -- ≃ Σ (e, eqv), (yon e x e ≡ e)      [swap + assoc]
      -- ≃ Σ (e, eqv), (e ≡ idn)             [e-idn-idpt]
      -- ≃ Σ (e, e≡idn), is-eqv e            [un-assoc + swap + re-assoc]
      -- ≃ is-eqv idn                         [singleton contraction]

      step1 : unit-data x ≃
        (Σ p ∶ (Σ e ∶ hom x x , is-eqv e)
        , yon (p .fst) x (p .fst) ≡ p .fst)
      step1 = Σ-equiv-snd (λ _ → ×-comm-equiv) ∙e Σ-assoc

      step2 : (Σ p ∶ (Σ e ∶ hom x x , is-eqv e)
          , yon (p .fst) x (p .fst) ≡ p .fst)
        ≃ (Σ p ∶ (Σ e ∶ hom x x , is-eqv e)
          , p .fst ≡ idn)
      step2 = Σ-equiv-snd λ (e , eqv) →
        e-idn-idpt e (eqv .snd)

      step3
        : (Σ p ∶ (Σ e ∶ hom x x , is-eqv e)
          , p .fst ≡ idn)
        ≃ (Σ p ∶ (Σ e ∶ hom x x , e ≡ idn)
          , is-eqv (p .fst))
      step3 =
        esym Σ-assoc
        ∙e Σ-equiv-snd (λ _ → ×-comm-equiv)
        ∙e Σ-assoc

      end-singl : is-contr (Σ e ∶ hom x x , e ≡ idn)
      end-singl = is-contr-equiv
        (Σ-equiv-snd λ _ → path-sym-equiv)
        (Singl-contr idn)

      step4
        : (Σ p ∶ (Σ e ∶ hom x x , e ≡ idn)
          , is-eqv (p .fst))
        ≃ is-eqv idn
      step4 = Σ-contr-fst end-singl

      chain : unit-data x ≃ is-eqv idn
      chain = step1 ∙e step2 ∙e step3 ∙e step4
```

### Pentagon

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

  module pentagon-fibers
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

    private
      assoc-σ
        : ∀ {x y z w}
          (f : hom x y) (g : hom y z) (h : hom z w)
        → (   (f ⨾ g) ⨾ h
            , emb-composite (f ⨾ g) h
            ∙ funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                emb-composite-pt f g w' a v'
                  (noy h v' b))
        ≡ (   f ⨾ (g ⨾ h)
            , emb-composite f (g ⨾ h)
            ∙ funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite g h b))
      assoc-σ f g h =
        is-contr→is-prop (E₃-contr f g h) _ _

      γ₁₂ : pt₁ ≡ pt₂
      γ₁₂ i =
        assoc f g h i ⨾ k
        , emb-composite (assoc f g h i) k
        ∙ (λ j w' a v' b →
            assoc-σ f g h i .snd j w' a v'
              (noy k v' b))

      γ₂₃-pt : ∀ i → fiber emb (E₄ f g h k)
      γ₂₃-pt i =
        assoc f (g ⨾ h) k i
        , assoc-σ f (g ⨾ h) k i .snd
        ∙ funext λ w' → funext λ a →
          funext λ v' → funext λ b →
            ap (emb f w' a v')
              (noy-composite g h (noy k v' b))

      w₂ : pt₂ ≡ γ₂₃-pt i0
      w₂ i =
        (f ⨾ (g ⨾ h)) ⨾ k
        , Path.assoc
            (emb-composite (f ⨾ (g ⨾ h)) k)
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                emb-composite-pt f (g ⨾ h) w' a v'
                  (noy k v' b))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite g h (noy k v' b))) i

      w₃ : γ₂₃-pt i1 ≡ pt₃
      w₃ i =
        f ⨾ ((g ⨾ h) ⨾ k)
        , sym (Path.assoc
            (emb-composite f ((g ⨾ h) ⨾ k))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite (g ⨾ h) k b))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite g h (noy k v' b)))) i

      γ₂₃-full : pt₂ ≡ pt₃
      γ₂₃-full = w₂ ∙ (λ i → γ₂₃-pt i) ∙ w₃

      γ₄₅-pt : ∀ i → fiber emb (E₄ f g h k)
      γ₄₅-pt i =
        assoc f g (h ⨾ k) i
        , assoc-σ f g (h ⨾ k) i .snd
        ∙ funext λ w' → funext λ a →
          funext λ v' → funext λ b →
            ap (λ t → emb f w' a v' (noy g v' t))
              (noy-composite h k b)

      w₄ : pt₄ ≡ γ₄₅-pt i0
      w₄ i =
        (f ⨾ g) ⨾ (h ⨾ k)
        , Path.assoc
            (emb-composite (f ⨾ g) (h ⨾ k))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                emb-composite-pt f g w' a v'
                  (noy (h ⨾ k) v' b))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (λ t → emb f w' a v' (noy g v' t))
                  (noy-composite h k b)) i

      w₅ : γ₄₅-pt i1 ≡ pt₅
      w₅ i =
        f ⨾ (g ⨾ (h ⨾ k))
        , sym (Path.assoc
            (emb-composite f (g ⨾ (h ⨾ k)))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite g (h ⨾ k) b))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (λ t → emb f w' a v' (noy g v' t))
                  (noy-composite h k b))) i

      γ₄₅-full : pt₄ ≡ pt₅
      γ₄₅-full = w₄ ∙ (λ i → γ₄₅-pt i) ∙ w₅

      γ₁₄-pt : ∀ i → fiber emb (E₄ f g h k)
      γ₁₄-pt i =
        assoc (f ⨾ g) h k i
        , assoc-σ (f ⨾ g) h k i .snd
        ∙ funext λ w' → funext λ a →
          funext λ v' → funext λ b →
            emb-composite-pt f g w' a v'
              (noy h v' (noy k v' b))

      w₁ : pt₁ ≡ γ₁₄-pt i0
      w₁ i =
        ((f ⨾ g) ⨾ h) ⨾ k
        , Path.assoc
            (emb-composite ((f ⨾ g) ⨾ h) k)
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                emb-composite-pt (f ⨾ g) h w' a v'
                  (noy k v' b))
            (funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                emb-composite-pt f g w' a v'
                  (noy h v' (noy k v' b))) i

      w₁₄-nat : ∀ w' (a : hom w' x) v' (b : hom v v')
        → ap (emb (f ⨾ g) w' a v') (noy-composite h k b)
          ∙ emb-composite-pt f g w' a v'
              (noy h v' (noy k v' b))
        ≡ emb-composite-pt f g w' a v' (noy (h ⨾ k) v' b)
          ∙ ap (λ t → emb f w' a v' (noy g v' t))
                (noy-composite h k b)
      w₁₄-nat w' a v' b = sym (Path.commutes
        (emb-composite-pt f g w' a v' (noy (h ⨾ k) v' b))
        (ap (λ t → emb f w' a v' (noy g v' t))
          (noy-composite h k b))
        (ap (emb (f ⨾ g) w' a v') (noy-composite h k b))
        (emb-composite-pt f g w' a v'
          (noy h v' (noy k v' b)))
        (λ i j → emb-composite-pt f g w' a v'
          (noy-composite h k b i) j))

      w₁₄ : γ₁₄-pt i1 ≡ pt₄
      w₁₄ i =
        (f ⨾ g) ⨾ (h ⨾ k)
        , (sym (Path.assoc A₁₄ B₁₄ C₁₄)
          ∙ ap (A₁₄ ∙_) N₁₄) i
        where
          A₁₄ = emb-composite (f ⨾ g) (h ⨾ k)
          B₁₄ = funext λ w' → funext λ a →
            funext λ v' → funext λ b →
              ap (emb (f ⨾ g) w' a v')
                (noy-composite h k b)
          C₁₄ = funext λ w' → funext λ a →
            funext λ v' → funext λ b →
              emb-composite-pt f g w' a v'
                (noy h v' (noy k v' b))
          N₁₄ : B₁₄ ∙ C₁₄
              ≡ (funext λ w' → funext λ a →
                  funext λ v' → funext λ b →
                    emb-composite-pt f g w' a v'
                      (noy (h ⨾ k) v' b)
                  ∙ ap (λ t → emb f w' a v' (noy g v' t))
                        (noy-composite h k b))
          N₁₄ j = funext λ w' → funext λ a →
            funext λ v' → funext λ b →
              w₁₄-nat w' a v' b j

      γ₁₄-full : pt₁ ≡ pt₄
      γ₁₄-full = w₁ ∙ (λ i → γ₁₄-pt i) ∙ w₁₄

    face₁₂ : α₁₂ ≡ ap (_⨾ k) (assoc f g h)
    face₁₂ = total-contr-unique E₄c
      α₁₂ (ap (_⨾ k) (assoc f g h))
      (ap snd σ₁₂)
      (ap snd γ₁₂)

    -- face₃₅ requires noy-composite-coh, a 2-coherence datum.
    -- It is proved in the 2-Cat module below.

    face₂₃ : α₂₃ ≡ assoc f (g ⨾ h) k
    face₂₃ =
      total-contr-unique E₄c
        α₂₃ (ap fst γ₂₃-full)
        (ap snd σ₂₃)
        (ap snd γ₂₃-full)
      ∙ ap-comp fst w₂ ((λ i → γ₂₃-pt i) ∙ w₃)
      ∙ ap (refl ∙_)
          (ap-comp fst (λ i → γ₂₃-pt i) w₃
          ∙ Path.unitr (assoc f (g ⨾ h) k))
      ∙ Path.unitl (assoc f (g ⨾ h) k)

    face₄₅ : α₄₅ ≡ assoc f g (h ⨾ k)
    face₄₅ =
      total-contr-unique E₄c
        α₄₅ (ap fst γ₄₅-full)
        (ap snd σ₄₅)
        (ap snd γ₄₅-full)
      ∙ ap-comp fst w₄ ((λ i → γ₄₅-pt i) ∙ w₅)
      ∙ ap (refl ∙_)
          (ap-comp fst (λ i → γ₄₅-pt i) w₅
          ∙ Path.unitr (assoc f g (h ⨾ k)))
      ∙ Path.unitl (assoc f g (h ⨾ k))

    face₁₄ : α₁₄ ≡ assoc (f ⨾ g) h k
    face₁₄ =
      total-contr-unique E₄c
        α₁₄ (ap fst γ₁₄-full)
        (ap snd σ₁₄)
        (ap snd γ₁₄-full)
      ∙ ap-comp fst w₁ ((λ i → γ₁₄-pt i) ∙ w₁₄)
      ∙ ap (refl ∙_)
          (ap-comp fst (λ i → γ₁₄-pt i) w₁₄
          ∙ Path.unitr (assoc (f ⨾ g) h k))
      ∙ Path.unitl (assoc (f ⨾ g) h k)

  module pentagon
    {x y z w v}
    (f : hom x y) (g : hom y z)
    (h : hom z w) (k : hom w v)
    where
    open pentagon-fibers f g h k

    hom-identity
      : α₁₄ ∙ α₄₅ ≡ α₁₂ ∙ α₂₃ ∙ α₃₅
    hom-identity =
      sym (ap-comp fst σ₁₄ σ₄₅)
      ∙ ap (ap fst) identity
      ∙ ap-comp fst σ₁₂ (σ₂₃ ∙ σ₃₅)
      ∙ ap (α₁₂ ∙_) (ap-comp fst σ₂₃ σ₃₅)

  pentagon
    : ∀ {x y z w v}
      (f : hom x y) (g : hom y z)
      (h : hom z w) (k : hom w v)
    → assoc (f ⨾ g) h k ∙ assoc f g (h ⨾ k)
    ≡ ap (_⨾ k) (assoc f g h)
      ∙ assoc f (g ⨾ h) k
      ∙ pentagon-fibers.α₃₅ f g h k
  pentagon f g h k =
    sym (ap (_∙ α₄₅) face₁₄
        ∙ ap (assoc (f ⨾ g) h k ∙_) face₄₅)
    ∙ hom-identity
    ∙ ap (_∙ (α₂₃ ∙ α₃₅)) face₁₂
    ∙ ap (ap (_⨾ k) (assoc f g h) ∙_)
        (ap (_∙ α₃₅) face₂₃)
    where open pentagon-fibers f g h k
          open pentagon f g h k
```

### Weak triangle

The weak triangle uses only `absorb-l` from `unit`,
not `absorb-coh`. The `α₂₃` edge remains abstract.

```agda
  module triangle-fibers
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
            ∙ ap (emb f w a v) (noy-absorb (noy g v b))

      pt₂ : fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      pt₂ = f ⨾ (idn ⨾ g)
          , emb-composite f (idn ⨾ g)
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              ap (emb f w a v)
                (noy-composite idn g b)
            ∙ ap (emb f w a v)
                (noy-absorb (noy g v b))

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

    private
      unitr-σ
        : (   f ⨾ idn
            , emb-composite f idn
            ∙ funext λ w → funext λ a →
              funext λ v → funext λ b →
                ap (emb f w a v) (noy-absorb b))
        ≡ (f , refl)
      unitr-σ =
        is-contr→is-prop (emb-image-contr f) _ _

      γ₁₃-pt : ∀ i → fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      γ₁₃-pt i =
        unitr f i ⨾ g
        , emb-composite (unitr f i) g
        ∙ (λ j w a v b →
            unitr-σ i .snd j w a v (noy g v b))

      v₃ : γ₁₃-pt i1 ≡ pt₃
      v₃ i =
        f ⨾ g
        , Path.unitr (emb-composite f g) i

      γ₁₃-full : pt₁ ≡ pt₃
      γ₁₃-full = (λ i → γ₁₃-pt i) ∙ v₃

      assoc-σ-fig
        : (   (f ⨾ idn) ⨾ g
            , emb-composite (f ⨾ idn) g
            ∙ funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                emb-composite-pt f idn w' a v'
                  (noy g v' b))
        ≡ (   f ⨾ (idn ⨾ g)
            , emb-composite f (idn ⨾ g)
            ∙ funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite idn g b))
      assoc-σ-fig =
        is-contr→is-prop (E₃-contr f idn g) _ _

      γ₁₂-pt : ∀ i → fiber emb
        (λ w a v b → emb f w a v (noy g v b))
      γ₁₂-pt i =
        assoc f idn g i
        , assoc-σ-fig i .snd
        ∙ funext λ w → funext λ a →
          funext λ v → funext λ b →
            ap (emb f w a v)
              (noy-absorb (noy g v b))

      w₁ : pt₁ ≡ γ₁₂-pt i0
      w₁ i =
        (f ⨾ idn) ⨾ g
        , Path.assoc
            (emb-composite (f ⨾ idn) g)
            (funext λ w → funext λ a →
              funext λ v → funext λ b →
                emb-composite-pt f idn w a v
                  (noy g v b))
            (funext λ w → funext λ a →
              funext λ v → funext λ b →
                ap (emb f w a v)
                  (noy-absorb (noy g v b))) i

      w₂ : γ₁₂-pt i1 ≡ pt₂
      w₂ i =
        f ⨾ (idn ⨾ g)
        , sym (Path.assoc
            (emb-composite f (idn ⨾ g))
            (funext λ w → funext λ a →
              funext λ v → funext λ b →
                ap (emb f w a v)
                  (noy-composite idn g b))
            (funext λ w → funext λ a →
              funext λ v → funext λ b →
                ap (emb f w a v)
                  (noy-absorb (noy g v b)))) i

      γ₁₂-full : pt₁ ≡ pt₂
      γ₁₂-full = w₁ ∙ (λ i → γ₁₂-pt i) ∙ w₂

    face₁₃ : α₁₃ ≡ ap (_⨾ g) (unitr f)
    face₁₃ =
      total-contr-unique cc
        α₁₃ (ap fst γ₁₃-full)
        (ap snd σ₁₃)
        (ap snd γ₁₃-full)
      ∙ ap-comp fst (λ i → γ₁₃-pt i) v₃
      ∙ Path.unitr (ap (_⨾ g) (unitr f))

    face₁₂ : α₁₂ ≡ assoc f idn g
    face₁₂ =
      total-contr-unique cc
        α₁₂ (ap fst γ₁₂-full)
        (ap snd σ₁₂)
        (ap snd γ₁₂-full)
      ∙ ap-comp fst w₁ ((λ i → γ₁₂-pt i) ∙ w₂)
      ∙ ap (refl ∙_)
          (ap-comp fst (λ i → γ₁₂-pt i) w₂
          ∙ Path.unitr (assoc f idn g))
      ∙ Path.unitl (assoc f idn g)

  module triangle
    {x y z} (f : hom x y) (g : hom y z)
    where
    open triangle-fibers f g

    hom-identity
      : α₁₃ ≡ α₁₂ ∙ α₂₃
    hom-identity =
      ap (ap fst) identity
      ∙ ap-comp fst σ₁₂ σ₂₃

  triangle-weak
    : ∀ {x y z}
      (f : hom x y) (g : hom y z)
    → ap (_⨾ g) (unitr f)
    ≡ assoc f idn g ∙ triangle-fibers.α₂₃ f g
  triangle-weak f g =
    sym face₁₃
    ∙ hom-identity
    ∙ ap (_∙ α₂₃) face₁₂
    where open triangle-fibers f g
          open triangle f g
```

## 2-coherence

The `noy-absorb-coh` field witnesses that the two canonical
paths from `noy (idn ⨾ f) v b` to `noy f v b` agree:
composing via `noy-composite ∙ noy-absorb` or via
`ap noy unitl`. This stays at the noy-level, avoiding
the `absorb-l`/`emb idn` mismatch entirely.

The `noy-composite-coh` field says: the two ways of
decomposing `noy ((g ⨾ h) ⨾ k) v b` into
`noy g v (noy h v (noy k v b))` are related over
`assoc g h k`. One way first decomposes `(g ⨾ h) ⨾ k`
then `g ⨾ h`; the other first decomposes `g ⨾ (h ⨾ k)`
then `h ⨾ k`. This is the noy-level pentagon coherence
needed for the full Mac Lane pentagon.

```agda
record 2-coherent {o h} (C : category o h)
  : Type (o ⊔ h) where
  open Cat C
  field
    noy-absorb-coh
      : ∀ {x y} (f : hom x y) v (b : hom y v)
      → noy-composite idn f b
        ∙ noy-absorb (noy f v b)
      ≡ ap (λ t → noy t v b) (unitl f)

    noy-composite-coh
      : ∀ {x y z w} (g : hom x y) (h : hom y z)
        (k : hom z w) v (b : hom w v)
      → PathP (λ i → noy (assoc g h k i) v b
                    ≡ noy g v (noy h v (noy k v b)))
          (noy-composite (g ⨾ h) k b
            ∙ noy-composite g h (noy k v b))
          (noy-composite g (h ⨾ k) b
            ∙ ap (noy g v) (noy-composite h k b))
```

## Full Mac Lane triangle and pentagon

The `2-Cat` module opens both `Cat C` and `2-coherent coh`,
then derives the full triangle and pentagon.

The full triangle
`ap (_⨾ g) (unitr f) ≡ assoc f idn g ∙ ap (f ⨾_) (unitl g)`
uses `noy-absorb-coh` to build `γ₂₃-mid`, a fiber path
that varies along `unitl g` using a tail fill
`λ j → noy (unitl g (i ∨ j)) v b` at the noy-level.

The full pentagon uses `noy-composite-coh` to build
`face₃₅ : α₃₅ ≡ ap (f ⨾_) (assoc g h k)`, the missing
face identification. The mid-path `γ₃₅-mid` varies along
`assoc g h k`, with `noy-composite-coh` providing the
PathP that connects the two decomposition strategies.

```agda
module 2-Cat
  {o h} (C : category o h) (coh : 2-coherent C)
  where
  open Cat C public hiding (pentagon)
  open 2-coherent coh public

  private
    module face₂₃-proof
      {x y z} (f : hom x y) (g : hom y z)
      where
      open Cat.triangle-fibers C f g

      private
        cc = composable-contr f g

        pt₂ : fiber emb
          (λ w a v b → emb f w a v (noy g v b))
        pt₂ = f ⨾ (idn ⨾ g)
            , emb-composite f (idn ⨾ g)
            ∙ funext λ w → funext λ a →
              funext λ v → funext λ b →
                ap (emb f w a v)
                  (noy-composite idn g b)
              ∙ ap (emb f w a v)
                  (noy-absorb (noy g v b))

        pt₃ : fiber emb
          (λ w a v b → emb f w a v (noy g v b))
        pt₃ = f ⨾ g , emb-composite f g

        γ₂₃-mid : ∀ i → fiber emb
          (λ w a v b → emb f w a v (noy g v b))
        γ₂₃-mid i =
          f ⨾ (unitl g i)
          , emb-composite f (unitl g i)
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              ap (emb f w a v)
                (λ j → noy (unitl g (i ∨ j)) v b)

        w₀ : pt₂ ≡ γ₂₃-mid i0
        w₀ i =
          f ⨾ (idn ⨾ g)
          , emb-composite f (idn ⨾ g)
          ∙ funext λ w → funext λ a →
            funext λ v → funext λ b →
              (sym (ap-comp (emb f w a v)
                (noy-composite idn g b)
                (noy-absorb (noy g v b)))
              ∙ ap (ap (emb f w a v))
                  (noy-absorb-coh g v b)) i

        v₃ : γ₂₃-mid i1 ≡ pt₃
        v₃ i =
          f ⨾ g
          , Path.unitr (emb-composite f g) i

        γ₂₃-full : pt₂ ≡ pt₃
        γ₂₃-full =
          w₀ ∙ (λ i → γ₂₃-mid i) ∙ v₃

      face₂₃ : α₂₃ ≡ ap (f ⨾_) (unitl g)
      face₂₃ =
        total-contr-unique cc
          α₂₃ (ap fst γ₂₃-full)
          (ap snd σ₂₃)
          (ap snd γ₂₃-full)
        ∙ ap-comp fst w₀
            ((λ i → γ₂₃-mid i) ∙ v₃)
        ∙ ap (refl ∙_)
            (ap-comp fst (λ i → γ₂₃-mid i) v₃
            ∙ Path.unitr (ap (f ⨾_) (unitl g)))
        ∙ Path.unitl (ap (f ⨾_) (unitl g))

  triangle
    : ∀ {x y z}
      (f : hom x y) (g : hom y z)
    → ap (_⨾ g) (unitr f)
    ≡ assoc f idn g ∙ ap (f ⨾_) (unitl g)
  triangle f g =
    sym face₁₃
    ∙ hom-identity
    ∙ ap (_∙ α₂₃) face₁₂
    ∙ ap (assoc f idn g ∙_) face₂₃
    where open Cat.triangle-fibers C f g
          open Cat.triangle C f g
          open face₂₃-proof f g

  private
    module face₃₅-proof
      {x y z w v}
      (f : hom x y) (g : hom y z)
      (h : hom z w) (k : hom w v)
      where
      open Cat.pentagon-fibers C f g h k

      private
        T : ∀ w' → hom w' x → ∀ v' → hom v v' → hom w' v'
        T w' a v' b =
          emb f w' a v' (noy g v' (noy h v' (noy k v' b)))

        E₄c = E₄-contr f g h k

        pt₃ : fiber emb T
        pt₃ = f ⨾ ((g ⨾ h) ⨾ k)
            , emb-composite f ((g ⨾ h) ⨾ k)
            ∙ funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite (g ⨾ h) k b)
              ∙ ap (emb f w' a v')
                  (noy-composite g h (noy k v' b))

        pt₅ : fiber emb T
        pt₅ = f ⨾ (g ⨾ (h ⨾ k))
            , emb-composite f (g ⨾ (h ⨾ k))
            ∙ funext λ w' → funext λ a →
              funext λ v' → funext λ b →
                ap (emb f w' a v')
                  (noy-composite g (h ⨾ k) b)
              ∙ ap (λ t → emb f w' a v' (noy g v' t))
                    (noy-composite h k b)

        γ₃₅-mid : ∀ i → fiber emb T
        γ₃₅-mid i =
          f ⨾ (assoc g h k i)
          , emb-composite f (assoc g h k i)
          ∙ funext λ w' → funext λ a →
            funext λ v' → funext λ b →
              ap (emb f w' a v')
                (noy-composite-coh g h k v' b i)

        w₃ : pt₃ ≡ γ₃₅-mid i0
        w₃ i =
          f ⨾ ((g ⨾ h) ⨾ k)
          , emb-composite f ((g ⨾ h) ⨾ k)
          ∙ funext λ w' → funext λ a →
            funext λ v' → funext λ b →
              sym (ap-comp (emb f w' a v')
                (noy-composite (g ⨾ h) k b)
                (noy-composite g h (noy k v' b))) i

        v₅ : γ₃₅-mid i1 ≡ pt₅
        v₅ i =
          f ⨾ (g ⨾ (h ⨾ k))
          , emb-composite f (g ⨾ (h ⨾ k))
          ∙ funext λ w' → funext λ a →
            funext λ v' → funext λ b →
              ap-comp (emb f w' a v')
                (noy-composite g (h ⨾ k) b)
                (ap (noy g v') (noy-composite h k b)) i

        γ₃₅-full : pt₃ ≡ pt₅
        γ₃₅-full = w₃ ∙ (λ i → γ₃₅-mid i) ∙ v₅

      face₃₅ : α₃₅ ≡ ap (f ⨾_) (assoc g h k)
      face₃₅ =
        total-contr-unique E₄c
          α₃₅ (ap fst γ₃₅-full)
          (ap snd σ₃₅)
          (ap snd γ₃₅-full)
        ∙ ap-comp fst w₃ ((λ i → γ₃₅-mid i) ∙ v₅)
        ∙ ap (refl ∙_)
            (ap-comp fst (λ i → γ₃₅-mid i) v₅
            ∙ Path.unitr (ap (f ⨾_) (assoc g h k)))
        ∙ Path.unitl (ap (f ⨾_) (assoc g h k))

  pentagon
    : ∀ {x y z w v}
      (f : hom x y) (g : hom y z)
      (h : hom z w) (k : hom w v)
    → assoc (f ⨾ g) h k ∙ assoc f g (h ⨾ k)
    ≡ ap (_⨾ k) (assoc f g h)
      ∙ assoc f (g ⨾ h) k ∙ ap (f ⨾_) (assoc g h k)
  pentagon f g h k =
    sym (ap (_∙ α₄₅) face₁₄
        ∙ ap (assoc (f ⨾ g) h k ∙_) face₄₅)
    ∙ hom-identity
    ∙ ap (_∙ (α₂₃ ∙ α₃₅)) face₁₂
    ∙ ap (ap (_⨾ k) (assoc f g h) ∙_)
        (ap (_∙ α₃₅) face₂₃
        ∙ ap (assoc f (g ⨾ h) k ∙_) face₃₅)
    where open Cat.pentagon-fibers C f g h k
          open Cat.pentagon C f g h k
          open face₃₅-proof f g h k
```
