The category of finite ordinals and monotone equivalences is gaunt: between any
two finite ordinals there is at most one monotone equivalence, and a monotone
equivalence forces its endpoints equal.

The proof runs at the level of the underlying naturals. A monotone map that is an
equivalence is strictly monotone, and a strictly monotone map is *inflationary*:
`lower i ≤ lower (s i)`, since below `i` there sit `lower i`-many indices whose
images are strictly smaller. Applying inflation to both the map and its inverse
pins the map's action on the naturals exactly: `lower (f i) ≡ lower i`. Endpoint
equality and uniqueness are then immediate — the first by comparing how far each
ordinal reaches, the second because two such maps agree index by index.

Recovering the order relations relevantly is what makes this reachable: `_≤ᶠ_`
stores its content irrelevantly, but `≤` on the naturals is decidable, so the
content comes back through `Core.Data.Irr`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Data.Fin.Monotone.Gaunt where

open import Core.Type
open import Core.Base
open import Core.Kan using (_∙_)
open import Core.Transport using (subst)
open import Core.Data.Empty
open import Core.Data.Sum
open import Core.Data.Irr using (out-dec)
open import Core.Data.Nat
open Nat
open import Core.Data.Sigma using (fst)
open import Core.Data.Fin.Type
open import Core.Data.Fin.Base using (flast)
open import Core.Data.Fin.Properties using (fin-path; bound)
open import Core.Data.Fin.Monotone.Type using (is-monotone; _≤ᶠ_; _<ᶠ_)
open import Core.Equiv using (_≃_; Equiv)

private variable
  m n : Nat

```

## Relevant order

The irrelevant order on `Fin` is recovered through decidability of `<` on the
naturals, and `is-monotone` is read as a statement about the underlying indices.

```agda

≤ᶠ→ : {i j : Fin n} → i ≤ᶠ j → lower i ≤ lower j
≤ᶠ→ {i = i} {j} = out-dec (≤-dec (lower i) (lower j))

mono→ : {f : Fin m → Fin n} → is-monotone f
      → (i j : Fin m) → lower i ≤ lower j → lower (f i) ≤ lower (f j)
mono→ {f = f} mono i j le = ≤ᶠ→ {i = f i} {j = f j} (mono i j (forget le))

is-monotone-is-prop : (f : Fin m → Fin n) → is-prop (is-monotone f)
is-monotone-is-prop f p q =
  funext λ i → funext λ j → funext λ le → Irr-is-prop (p i j le) (q i j le)

```

## Order arithmetic

A bound together with an inequality of it against its endpoint upgrades to a
strict inequality, and inflation of a strictly monotone map is proved by
induction on the number of indices lying below a given one.

```agda

≤≠→< : {a b : Nat} → a ≤ b → ¬ (a ≡ b) → a < b
≤≠→< {a} {b} le ne with cmp b a
... | inr a<b = a<b
... | inl b≤a = ex-falso (ne (≤-antisym le b≤a))

inflation : {s : Fin m → Fin n}
          → ((i i' : Fin m) → lower i < lower i' → lower (s i) < lower (s i'))
          → (i : Fin m) → lower i ≤ lower (s i)
inflation {m} {n} {s} str i = ge (lower i) i le.rx
  where
    ge : (c : Nat) (j : Fin m) → c ≤ lower j → c ≤ lower (s j)
    ge Z     j _     = lt.z<s
    ge (S c) j Sc≤j  = s<s (le-lt-cat (ge c j' c≤j') (str j' j c<j))
      where
        c<j : c < lower j
        c<j = lt.peel (lower j) Sc≤j
        c<m : c < m
        c<m = lt.cat c<j (bound j)
        j' : Fin m
        j' = fin c ⦃ forget c<m ⦄
        c≤j' : c ≤ lower j'
        c≤j' = le.rx

fits : (a b : Nat) → ((i : Fin a) → lower i < b) → a ≤ b
fits Z     b h = lt.z<s
fits (S a) b h = s<s (h flast)

```

## The action on indices

A monotone equivalence `e` and its inverse are both strictly monotone, so both
are inflationary; the two inflations meet at `lower (f i) ≡ lower i`.

```agda

module low (e : Fin m ≃ Fin n) (mono : is-monotone (e .fst)) where
  private
    module E = Equiv e
    f = e .fst
    g = E.inv

  f-inj : {i i' : Fin m} → f i ≡ f i' → i ≡ i'
  f-inj {i} {i'} p = sym (E.unit i) ∙ ap g p ∙ E.unit i'

  str : (i i' : Fin m) → lower i < lower i' → lower (f i) < lower (f i')
  str i i' lt = ≤≠→< (mono→ {f = f} mono i i' (step lt)) ne
    where
      ne : ¬ (lower (f i) ≡ lower (f i'))
      ne p = lt.irrefl
        (subst (lower i <_)
          (sym (ap lower (f-inj (fin-path {x = f i} {y = f i'} p)))) lt)

  str-g : (k k' : Fin n) → lower k < lower k' → lower (g k) < lower (g k')
  str-g k k' lt with cmp (lower (g k')) (lower (g k))
  ... | inr gk<gk' = gk<gk'
  ... | inl gk'≤gk = ex-falso (lt-le-absurd lt k'≤k)
    where
      k'≤k : lower k' ≤ lower k
      k'≤k =
        subst (lower k' ≤_) (ap lower (E.counit k))
          (subst (_≤ lower (f (g k))) (ap lower (E.counit k'))
            (mono→ {f = f} mono (g k') (g k) gk'≤gk))

  infla-f : (i : Fin m) → lower i ≤ lower (f i)
  infla-f = inflation {s = f} str

  infla-g : (k : Fin n) → lower k ≤ lower (g k)
  infla-g = inflation {s = g} str-g

  low-pres : (i : Fin m) → lower (f i) ≡ lower i
  low-pres i = ≤-antisym rev (infla-f i)
    where
      rev : lower (f i) ≤ lower i
      rev = subst (lower (f i) ≤_) (ap lower (E.unit i)) (infla-g (f i))

  low-pres-g : (k : Fin n) → lower (g k) ≡ lower k
  low-pres-g k = sym (low-pres (g k)) ∙ ap lower (E.counit k)

```

## Gauntness

Any two monotone equivalences with the same endpoints have the same underlying
map, and a monotone equivalence forces its endpoints equal.

```agda

mono-unique : (e₁ e₂ : Fin m ≃ Fin n)
            → is-monotone (e₁ .fst) → is-monotone (e₂ .fst)
            → e₁ .fst ≡ e₂ .fst
mono-unique e₁ e₂ mono₁ mono₂ = funext λ i →
  fin-path {x = e₁ .fst i} {y = e₂ .fst i}
    (low.low-pres e₁ mono₁ i ∙ sym (low.low-pres e₂ mono₂ i))

mono-card : (e : Fin m ≃ Fin n) → is-monotone (e .fst) → m ≡ n
mono-card {m} {n} e mono = ≤-antisym (fits m n from-f) (fits n m from-g)
  where
    from-f : (i : Fin m) → lower i < n
    from-f i = subst (_< n) (low.low-pres e mono i) (bound (e .fst i))
    from-g : (k : Fin n) → lower k < m
    from-g k = subst (_< m) (low.low-pres-g e mono k) (bound (Equiv.inv e k))

```
