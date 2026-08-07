Mediation at the word model. A candidate pair `(θ⁻ , θ⁺)` mediates at a
triple when a word in the pair relates the two bracketings of the mixed
word there. The word is cut in front of one bracketing and gives the
other. `corr⁺` and `corr⁻` run the two recursions of `Word.Defect` over
the pair. They read the two measurements of the flanking edges that the
defect words read: the value of the leading edge at zero, and the
length of the zero plateau of the trailing edge. At the half-twists the two
families of correction words agree level by level. So the two defect
theorems say that the half-twist pair mediates at every triple.

Two triples carry the recognition. `(ε̂ , τ̂ , ε̂)` reads the correction
at level zero and returns `θ⁺ ≡ ε̂`. `(τ̂ , ε̂ , ε̂)` reads it at level
one, and `cancel-δ` then returns `θ⁻ ≡ τ̂`. Those two instances are the
two clauses of `Mediation`. So the pinning runs on the restricted
property, and the indexed property reaches it through `restrict`.
Neither proof reassociates a mixed word. A clause at a triple is the
corrected reassociation, and the unit laws of the two cuts with
`ev-inj` carry the rest.

The words form a set. So mediation at a fixed pair is a proposition,
the type of mediating pairs contracts, and the framed pairs contract
with it. The positive clause alone gives all of this. The negative
clause alone does not. At its own reducing triple it returns an
equation that the swapped pair `(ε̂ , τ̂)` also satisfies, and that pair
fails the clause at another triple. Each half-twist is an equivalence in its
own hand only. `τ̂` is not one in the positive hand, so the equivalence
condition reads one hand per component.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Word.Mediation where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Sigma
open import Core.Data.Empty using (¬_)
open import Core.Data.Nat
open import Core.Data.List
open import Core.Equiv
open import Core.Function.Embedding using (equiv→lc)
open import Core.HLevel.Base
  using (Π-is-prop; is-prop-×; ×-is-hlevel; Σ-prop-path)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
open import Bb.VirtualGraphs.Mediation
open import Bb.VirtualGraphs.Word.Carrier
open import Bb.VirtualGraphs.Word.Model
open import Bb.VirtualGraphs.Word.Defect
  using (w⁺; w⁻; pow⁺; guard; rise; zrunW; defect⁺; defect⁻; ⨾⁻-unitr)

open mediation BW (λ _ → τ̂) (λ _ → ε̂) BW-embedding BW-comp⁺ BW-comp⁻
  using ( _⨾⁺_; _⨾⁻_; pair; corr₀; corr₁; clause₀; clause₁; mediates₂
        ; is-eqv⁺; is-eqv⁻; is-eqv-pair; is-eqv-pair-is-prop
        ; framed; framed-is-prop )
```

## Unit laws and the double half-twist

The negative half-twist is a left unit of the negative cut. The negative cut
of the positive half-twist against itself is the double half-twist. That
descriptor reads every argument one step up, so it cancels on the right
of the positive cut.

```agda
τ-cut : ∀ x → τ̂ ⨾⁻ x ≡ x
τ-cut = comp-unitl

ε-cut-ε : ε̂ ⨾⁻ ε̂ ≡ δ̂
ε-cut-ε = comp-unitr δ̂

cancel-δ : ∀ A B → A ⨾⁺ δ̂ ≡ B ⨾⁺ δ̂ → A ≡ B
cancel-δ A B e = ev-inj A B λ n →
    ap (evW A) (sym (Nat.add.unitr n))
  ∙ sym (ev-comp A δ̂ (S n))
  ∙ ap (λ X → evW X (S n)) e
  ∙ ev-comp B δ̂ (S n)
  ∙ ap (evW B) (Nat.add.unitr n)
```

## The correction words of a candidate pair

`w⁺` and `w⁻` are words in the two half-twists under the two cuts. `corr⁺`
and `corr⁻` run the same two recursions over a candidate pair. The
double half-twist inside `w⁺` is the negative cut of the positive half-twist
against itself, so over a pair it becomes `θ⁺ ⨾⁻ θ⁺`. At level zero the
leading word is the second component. At level one it is the second
clause's own correction word. Both hold on the nose.

```agda
corr⁺ : W → W → Nat → W
corr⁺ θ⁻ θ⁺ Z     = θ⁺
corr⁺ θ⁻ θ⁺ (S a) = θ⁻ ⨾⁺ (corr⁺ θ⁻ θ⁺ a ⨾⁺ (θ⁺ ⨾⁻ θ⁺))

pow : W → W → Nat → W
pow θ⁻ θ⁺ Z     = θ⁺
pow θ⁻ θ⁺ (S n) = θ⁻ ⨾⁺ pow θ⁻ θ⁺ n

fence : W → Nat → W → W
fence θ⁺ Z     x = x
fence θ⁺ (S j) x = fence θ⁺ j x ⨾⁻ θ⁺

corr⁻ : W → W → Nat → W
corr⁻ θ⁻ θ⁺ k = fence θ⁺ k (pow θ⁻ θ⁺ (S k))

corr⁺-zero : ∀ θ⁻ θ⁺ → corr⁺ θ⁻ θ⁺ Z ≡ corr₀ (θ⁻ , θ⁺)
corr⁺-zero θ⁻ θ⁺ = refl

corr⁺-one : ∀ θ⁻ θ⁺ → corr⁺ θ⁻ θ⁺ (S Z) ≡ corr₁ (θ⁻ , θ⁺)
corr⁺-one θ⁻ θ⁺ = refl
```

At the half-twists the two families agree, level by level.

```agda
corr⁺-w⁺ : ∀ a → corr⁺ τ̂ ε̂ a ≡ w⁺ a
corr⁺-w⁺ Z     = refl
corr⁺-w⁺ (S a) =
    ap (λ x → τ̂ ⨾⁺ (x ⨾⁺ (ε̂ ⨾⁻ ε̂))) (corr⁺-w⁺ a)
  ∙ ap (λ d → τ̂ ⨾⁺ (w⁺ a ⨾⁺ d)) ε-cut-ε

pow-pow⁺ : ∀ n → pow τ̂ ε̂ n ≡ pow⁺ n τ̂
pow-pow⁺ Z     = refl
pow-pow⁺ (S n) = ap (τ̂ ⨾⁺_) (pow-pow⁺ n)

fence-guard : ∀ j x → fence ε̂ j x ≡ guard j x
fence-guard Z     x = refl
fence-guard (S j) x = ap (_⨾⁻ ε̂) (fence-guard j x)

corr⁻-w⁻ : ∀ k → corr⁻ τ̂ ε̂ k ≡ w⁻ k
corr⁻-w⁻ k =
  ap (fence ε̂ k) (pow-pow⁺ (S k)) ∙ fence-guard k (pow⁺ (S k) τ̂)
```

## The indexed property

A pair mediates when its two correction words relate the two
bracketings of the mixed word at every triple. The two placements are
the ones the defect analysis leaves standing. The leading correction
reads the value of the leading edge at zero. The trailing one reads the
length of the zero plateau of the trailing edge. The correction
families agree at the half-twists, so the two defect theorems give the two
clauses there.

```agda
mediates⁺ : W → W → Type
mediates⁺ θ⁻ θ⁺ =
  ∀ f g h → f ⨾⁺ (g ⨾⁻ h) ≡ corr⁺ θ⁻ θ⁺ (rise f) ⨾⁺ ((f ⨾⁺ g) ⨾⁻ h)

mediates⁻ : W → W → Type
mediates⁻ θ⁻ θ⁺ =
  ∀ f g h → (f ⨾⁺ g) ⨾⁻ h ≡ (f ⨾⁺ (g ⨾⁻ h)) ⨾⁻ corr⁻ θ⁻ θ⁺ (zrunW h)

mediates : W × W → Type
mediates p = mediates⁺ (p .fst) (p .snd) × mediates⁻ (p .fst) (p .snd)

mediates⁺-half-twists : mediates⁺ τ̂ ε̂
mediates⁺-half-twists f g h =
  defect⁺ f g h ∙ ap (λ x → x ⨾⁺ ((f ⨾⁺ g) ⨾⁻ h)) (sym (corr⁺-w⁺ (rise f)))

mediates⁻-half-twists : mediates⁻ τ̂ ε̂
mediates⁻-half-twists f g h =
  defect⁻ f g h ∙ ap ((f ⨾⁺ (g ⨾⁻ h)) ⨾⁻_) (sym (corr⁻-w⁻ (zrunW h)))

mediates-half-twists : mediates (τ̂ , ε̂)
mediates-half-twists = mediates⁺-half-twists , mediates⁻-half-twists
```

## The two triples

The leading index is zero at `(ε̂ , τ̂ , ε̂)` and one at `(τ̂ , ε̂ , ε̂)`,
so those two instances of the indexed property are the two clauses.

```agda
restrict : ∀ θ⁻ θ⁺ → mediates⁺ θ⁻ θ⁺ → mediates₂ tt (θ⁻ , θ⁺)
restrict θ⁻ θ⁺ M = M ε̂ τ̂ ε̂ , M τ̂ ε̂ ε̂

half-twists : mediates₂ tt (τ̂ , ε̂)
half-twists = restrict τ̂ ε̂ mediates⁺-half-twists
```

## Recognition

The first clause pins the second component through the unit laws of the
two cuts. Both bracketings there compute to the positive half-twist. The
second clause pins the first component through the same laws, and
`cancel-δ` returns it from the composite with the double half-twist.

```agda
module recognize (θ⁻ θ⁺ : W) (M : mediates₂ tt (θ⁻ , θ⁺)) where
  pin⁺ : θ⁺ ≡ ε̂
  pin⁺ = sym step
    where
    lhs : ε̂ ⨾⁺ (τ̂ ⨾⁻ ε̂) ≡ ε̂
    lhs = comp-unitl (τ̂ ⨾⁻ ε̂) ∙ τ-cut ε̂

    rhs : θ⁺ ⨾⁺ ((ε̂ ⨾⁺ τ̂) ⨾⁻ ε̂) ≡ θ⁺
    rhs =
        ap (λ x → θ⁺ ⨾⁺ (x ⨾⁻ ε̂)) (comp-unitl τ̂)
      ∙ ap (θ⁺ ⨾⁺_) (τ-cut ε̂)
      ∙ comp-unitr θ⁺

    step : ε̂ ≡ θ⁺
    step = sym lhs ∙ M .fst ∙ rhs

  pin⁻ : θ⁻ ≡ τ̂
  pin⁻ = sym (cancel-δ τ̂ θ⁻ step)
    where
    rhs : corr₁ (θ⁻ , θ⁺) ⨾⁺ ((τ̂ ⨾⁺ ε̂) ⨾⁻ ε̂) ≡ θ⁻ ⨾⁺ δ̂
    rhs =
        ap (λ x → corr₁ (θ⁻ , θ⁺) ⨾⁺ (x ⨾⁻ ε̂)) (comp-unitr τ̂)
      ∙ ap (corr₁ (θ⁻ , θ⁺) ⨾⁺_) (τ-cut ε̂)
      ∙ comp-unitr (corr₁ (θ⁻ , θ⁺))
      ∙ ap (λ u → θ⁻ ⨾⁺ (u ⨾⁺ (u ⨾⁻ u))) pin⁺
      ∙ ap (θ⁻ ⨾⁺_) (ap (ε̂ ⨾⁺_) ε-cut-ε ∙ comp-unitl δ̂)

    step : τ̂ ⨾⁺ δ̂ ≡ θ⁻ ⨾⁺ δ̂
    step = sym (ap (τ̂ ⨾⁺_) ε-cut-ε) ∙ M .snd ∙ rhs

  pair-path : _≡_ {A = W × W} (θ⁻ , θ⁺) (τ̂ , ε̂)
  pair-path i = pin⁻ i , pin⁺ i

recognize₂ : (p : pair tt) → mediates₂ tt p → p ≡ (τ̂ , ε̂)
recognize₂ p M = recognize.pair-path (p .fst) (p .snd) M

recognize⁺ : (p : W × W) → mediates⁺ (p .fst) (p .snd) → p ≡ (τ̂ , ε̂)
recognize⁺ p M = recognize₂ p (restrict (p .fst) (p .snd) M)
```

The words form a set, so pairs of words form one. Every form of the
property is then a proposition. Each pinning matches the witnesses at a
pair to the identifications of that pair and the half-twists, and it
contracts the pairs that carry the property.

```agda
WW-set : is-set (W × W)
WW-set = ×-is-hlevel (S (S Z)) W-set W-set

mediates₂-is-prop : ∀ p → is-prop (mediates₂ tt p)
mediates₂-is-prop p = is-prop-× (W-set _ _) (W-set _ _)

mediates⁺-is-prop : ∀ θ⁻ θ⁺ → is-prop (mediates⁺ θ⁻ θ⁺)
mediates⁺-is-prop θ⁻ θ⁺ =
  Π-is-prop λ f → Π-is-prop λ g → Π-is-prop λ h → W-set _ _

mediates⁻-is-prop : ∀ θ⁻ θ⁺ → is-prop (mediates⁻ θ⁻ θ⁺)
mediates⁻-is-prop θ⁻ θ⁺ =
  Π-is-prop λ f → Π-is-prop λ g → Π-is-prop λ h → W-set _ _

mediates-is-prop : ∀ p → is-prop (mediates p)
mediates-is-prop p =
  is-prop-× (mediates⁺-is-prop (p .fst) (p .snd))
            (mediates⁻-is-prop (p .fst) (p .snd))

recognition₂ : ∀ p → mediates₂ tt p ≃ (p ≡ (τ̂ , ε̂))
recognition₂ p =
  iso→equiv (recognize₂ p)
            (λ e → subst (mediates₂ tt) (sym e) half-twists)
            (λ M → mediates₂-is-prop p _ M)
            (λ e → WW-set p (τ̂ , ε̂) _ e)

mediation₂-contr : is-contr (Σ p ∶ pair tt , mediates₂ tt p)
mediation₂-contr .center = (τ̂ , ε̂) , half-twists
mediation₂-contr .paths (p , M) =
  sym (Σ-prop-path mediates₂-is-prop (recognize₂ p M))

recognition : ∀ p → mediates p ≃ (p ≡ (τ̂ , ε̂))
recognition p =
  iso→equiv (λ M → recognize⁺ p (M .fst))
            (λ e → subst mediates (sym e) mediates-half-twists)
            (λ M → mediates-is-prop p _ M)
            (λ e → WW-set p (τ̂ , ε̂) _ e)

mediation-contr : is-contr (Σ p ∶ W × W , mediates p)
mediation-contr .center = (τ̂ , ε̂) , mediates-half-twists
mediation-contr .paths (p , M) =
  sym (Σ-prop-path mediates-is-prop (recognize⁺ p (M .fst)))

recognition⁺ : ∀ p → mediates⁺ (p .fst) (p .snd) ≃ (p ≡ (τ̂ , ε̂))
recognition⁺ p =
  iso→equiv (recognize⁺ p)
            (λ e → subst (λ q → mediates⁺ (q .fst) (q .snd))
                         (sym e) mediates⁺-half-twists)
            (λ M → mediates⁺-is-prop (p .fst) (p .snd) _ M)
            (λ e → WW-set p (τ̂ , ε̂) _ e)

mediation⁺-contr : is-contr (Σ p ∶ W × W , mediates⁺ (p .fst) (p .snd))
mediation⁺-contr .center = (τ̂ , ε̂) , mediates⁺-half-twists
mediation⁺-contr .paths (p , M) =
  sym (Σ-prop-path (λ q → mediates⁺-is-prop (q .fst) (q .snd))
                   (recognize⁺ p M))
```

## Which hand reads the equivalence

Each half-twist is a two-sided unit of its own hand here, so each is an
equivalence there. The negative half-twist is not one in the positive hand.
`ν̂` reads one at zero and translates by one above it. So `ν̂ ⨾⁺ τ̂` and
`ε̂ ⨾⁺ τ̂` are one word while `ν̂` and `ε̂` are two, and the equivalence
condition on a pair reads each component in its own hand.

```agda
half-twist⁺-is-eqv⁺ : is-eqv⁺ {tt} ε̂
half-twist⁺-is-eqv⁺ =
    (λ _ → subst is-equiv (sym (funext λ h → comp-unitr h)) id-equiv)
  , (λ _ → subst is-equiv (sym (funext λ h → comp-unitl h)) id-equiv)

half-twist⁻-is-eqv⁻ : is-eqv⁻ {tt} τ̂
half-twist⁻-is-eqv⁻ =
    (λ _ → subst is-equiv (sym (funext λ h → ⨾⁻-unitr h)) id-equiv)
  , (λ _ → subst is-equiv (sym (funext λ h → τ-cut h)) id-equiv)

half-twist-pair-is-eqv : is-eqv-pair tt (τ̂ , ε̂)
half-twist-pair-is-eqv = half-twist⁻-is-eqv⁻ , half-twist⁺-is-eqv⁺

ν̂ : W
ν̂ = S Z ∷ [] , S Z , tt

ν-cut : ν̂ ⨾⁺ τ̂ ≡ τ̂
ν-cut = ev-inj (ν̂ ⨾⁺ τ̂) τ̂ λ n →
  ev-comp ν̂ τ̂ n ∙ ap (evW ν̂) (Nat.add.+suc n Z ∙ ap S (Nat.add.unitr n))

ν≢ε : ¬ (ν̂ ≡ ε̂)
ν≢ε e = subst w-nil (sym e) tt

half-twist⁻-not-eqv⁺ : ¬ is-eqv⁺ {tt} τ̂
half-twist⁻-not-eqv⁺ (pe , _) =
  ν≢ε (equiv→lc (pe tt) (ν-cut ∙ sym (comp-unitl τ̂)))
```

## The framed pairs

The equivalence condition holds at the half-twist pair and the two clauses
pin any pair to it, so the framed pairs contract at the one object and
the family over the objects is a proposition.

```agda
framed-contr : (x : ⊤) → is-contr (framed x)
framed-contr _ .center = (τ̂ , ε̂) , (half-twist-pair-is-eqv , half-twists)
framed-contr _ .paths (p , E , M) =
  sym (Σ-prop-path
        (λ q → is-prop-× (is-eqv-pair-is-prop tt q) (mediates₂-is-prop q))
        (recognize₂ p M))

has-framing-is-prop : is-prop ((x : ⊤) → framed x)
has-framing-is-prop = framed-is-prop framed-contr
```

## The negative clause on its own

At `(τ̂ , ε̂ , τ̂)` the negative clause returns one equation. The positive
cut of the pair is the negative half-twist. The swapped pair `(ε̂ , τ̂)`
satisfies that equation, so the equation does not pin. The swapped pair
does fail the clause itself, at `(τ̂ , ε̂ , ε̂)`. There its correction
word collapses to the negative half-twist and the trailing cut becomes a
unit.

```agda
head⁻ : ∀ θ⁻ θ⁺ → mediates⁻ θ⁻ θ⁺ → θ⁻ ⨾⁺ θ⁺ ≡ τ̂
head⁻ θ⁻ θ⁺ M = sym step
  where
  lhs : (τ̂ ⨾⁺ ε̂) ⨾⁻ τ̂ ≡ τ̂
  lhs = ap (_⨾⁻ τ̂) (comp-unitr τ̂) ∙ τ-cut τ̂

  rhs : (τ̂ ⨾⁺ (ε̂ ⨾⁻ τ̂)) ⨾⁻ corr⁻ θ⁻ θ⁺ (zrunW τ̂) ≡ θ⁻ ⨾⁺ θ⁺
  rhs =
      ap (λ x → (τ̂ ⨾⁺ x) ⨾⁻ (θ⁻ ⨾⁺ θ⁺)) bicyclic-collapse
    ∙ ap (_⨾⁻ (θ⁻ ⨾⁺ θ⁺)) (comp-unitr τ̂)
    ∙ τ-cut (θ⁻ ⨾⁺ θ⁺)

  step : τ̂ ≡ θ⁻ ⨾⁺ θ⁺
  step = sym lhs ∙ M τ̂ ε̂ τ̂ ∙ rhs

swap-head : ε̂ ⨾⁺ τ̂ ≡ τ̂
swap-head = comp-unitl τ̂

corr⁻-swap : corr⁻ ε̂ τ̂ (S Z) ≡ τ̂
corr⁻-swap =
  ap (_⨾⁻ τ̂) (comp-unitl (ε̂ ⨾⁺ τ̂) ∙ comp-unitl τ̂) ∙ τ-cut τ̂

swap-not-mediates⁻ : ¬ mediates⁻ ε̂ τ̂
swap-not-mediates⁻ M = bicyclic-persists (sym step)
  where
  lhs : (τ̂ ⨾⁺ ε̂) ⨾⁻ ε̂ ≡ ε̂
  lhs = ap (_⨾⁻ ε̂) (comp-unitr τ̂) ∙ τ-cut ε̂

  rhs : (τ̂ ⨾⁺ (ε̂ ⨾⁻ ε̂)) ⨾⁻ corr⁻ ε̂ τ̂ (zrunW ε̂) ≡ τ̂ ⨾⁺ δ̂
  rhs =
      ap (λ x → (τ̂ ⨾⁺ x) ⨾⁻ corr⁻ ε̂ τ̂ (S Z)) ε-cut-ε
    ∙ ap ((τ̂ ⨾⁺ δ̂) ⨾⁻_) corr⁻-swap
    ∙ ⨾⁻-unitr (τ̂ ⨾⁺ δ̂)

  step : ε̂ ≡ τ̂ ⨾⁺ δ̂
  step = sym lhs ∙ M τ̂ ε̂ ε̂ ∙ rhs

swap-not-mediates : ¬ mediates (ε̂ , τ̂)
swap-not-mediates M = swap-not-mediates⁻ (M .snd)
```
