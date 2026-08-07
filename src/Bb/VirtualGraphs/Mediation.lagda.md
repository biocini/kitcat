Mediation over a candidate pair of endo-edges, and canonicalization
in the positive hand.

`Tower` withholds the mixed word whose junctions run positive then
negative, so its two bracketings need not agree. A candidate pair
mediates at such a word when a word in the pair, cut in front of one
bracketing, gives the other. Two triples of half-twists carry the
statement here. The self-referential form reads the same two
corrections at the triples the pair builds out of itself, so its
clauses name no half-twist family.

An endo-edge is an equivalence in a hand when both translations by it
in that hand are equivalences of types. From an equivalence in the
positive hand, canonicalization returns a right unit of that cut,
again an equivalence.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.VirtualGraphs.Mediation where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; is-contr→is-prop)
open import Core.Transport.J using (subst)
open import Core.HLevel.Base using (Π-is-prop; is-prop-×)
open import Core.Equiv.Base using (_≃_; is-equiv; module Equiv)
open import Core.Equiv.Properties
  using (comp-equiv; sym-equiv; is-equiv-is-prop; equiv-lc; equiv-rc)

open import Bb.VirtualGraphs.Type
open import Bb.VirtualGraphs.Embedding
open import Bb.VirtualGraphs.Framing
open import Bb.VirtualGraphs.Tower
```

## Equivalences in the positive hand

An endo-edge at `x` is an equivalence in the positive hand when both
of its translations there are equivalences of types. One translation
cuts it after an edge into `x`, at every source. The other cuts it
before an edge out of `x`, at every target. One equivalence per
object stands in each family. `is-equiv` is a proposition, so both
families are.

Three edges meet at a positive cut, and two of them decide the third.
Where the trailing factor and the whole cut are equivalences in this
hand, so is the leading factor. Each half moves the associator across
a translation and cancels the trailing factor's own translation
against it.

```agda
module mediation⁺ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx : (x : ob) → hom x x)
  (S : reflect-is-embedding G) (C⁺ : framing⁻.is-composable⁺ G rx) where

  open tower⁺ G rx S C⁺ public

  is-eqv⁺ : ∀ {x} → hom x x → Type (o ⊔ h)
  is-eqv⁺ {x} e = ((w : ob) → is-equiv λ (f : hom w x) → f ⨾⁺ e)
                × ((y : ob) → is-equiv λ (g : hom x y) → e ⨾⁺ g)

  eqv-2-out-of-3 : ∀ {x} (f g : hom x x)
                 → is-eqv⁺ g → is-eqv⁺ (f ⨾⁺ g) → is-eqv⁺ f
  eqv-2-out-of-3 {x} f g (gp , gq) (cp , cq) = post , pre
    where
      post : (w : ob) → is-equiv λ (u : hom w x) → u ⨾⁺ f
      post w =
        equiv-lc (λ u → u ⨾⁺ f) (λ u → u ⨾⁺ g) (gp w)
          (subst is-equiv (funext λ u → sym (assoc⁺ u f g)) (cp w))

      pre : (y : ob) → is-equiv λ (u : hom x y) → f ⨾⁺ u
      pre y =
        equiv-rc (λ u → g ⨾⁺ u) (λ u → f ⨾⁺ u) (gq y)
          (subst is-equiv (funext λ u → assoc⁺ f g u) (cq y))
```

Canonicalization at such an edge: `canon` is the edge that the
translation after `e` sends to `e`. It cuts onto `e` without moving
it. It is a right unit of the positive cut at every edge into the
object, and 2-out-of-3 returns it as an equivalence in this hand
again.

The construction is Kraus, *Internal ∞-Categorical Models of
Dependent Type Theory*, §5.2 (`resources/kraus-infty-cwf/notes.tex`
l.869-889), and its companion formalization's `module I`
(`resources/kraus-infty-cwf/Identities.agda:298-339`). `canon` is his
`I`, `canon-cut` his `e⋄I`, `canon-unitr` his `l-ntrl`, and
`canon-is-eqv` the second half of his `I-is-idpt+eqv`.
`eqv-2-out-of-3` is his lemma of that name (`Identities.agda:238-290`)
and `is-eqv⁺` is his `is-eqv` (`Identities.agda:111-113`) read in one
hand. Kraus credits `I` to Capriotti and Kraus (POPL 2018,
`resources/capriotti-kraus-semi-segal`) and to work of Harpaz and
Lurie. He composes applicatively and this library diagrammatically,
so his left neutrality reads here as right neutrality of the positive
cut.

```agda
  module canonical {x : ob} (e : hom x x) (p : is-eqv⁺ e) where
    post : (w : ob) → hom w x ≃ hom w x
    post w = (λ f → f ⨾⁺ e) , p .fst w

    canon : hom x x
    canon = Equiv.inv (post x) e

    canon-cut : canon ⨾⁺ e ≡ e
    canon-cut = Equiv.counit (post x) e

    canon-unitr : ∀ {w} (f : hom w x) → f ⨾⁺ canon ≡ f
    canon-unitr {w} f =
        sym (Equiv.unit (post w) (f ⨾⁺ canon))
      ∙ ap (Equiv.inv (post w)) (assoc⁺ f canon e ∙ ap (f ⨾⁺_) canon-cut)
      ∙ Equiv.unit (post w) f

    canon-is-eqv : is-eqv⁺ canon
    canon-is-eqv =
      eqv-2-out-of-3 canon e p (subst (is-eqv⁺ {x}) (sym canon-cut) p)
```

## Equivalences in the negative hand

The mirror reads both translations through the negative cut.

```agda
module mediation⁻ {o h} (G : virtual-graph o h) (open virtual-graph G)
  (corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G) (C⁻ : framing⁺.is-composable⁻ G corx) where

  open tower⁻ G corx S C⁻ public

  is-eqv⁻ : ∀ {x} → hom x x → Type (o ⊔ h)
  is-eqv⁻ {x} e = ((w : ob) → is-equiv λ (f : hom w x) → f ⨾⁻ e)
                × ((y : ob) → is-equiv λ (g : hom x y) → e ⨾⁻ g)
```

## The two clauses

A candidate at an object is a pair of endo-edges there. The first
component stands where `rx` stands and the second where `corx` does.
`corr₀` and `corr₁` are two words in the pair: the second component
alone, and the first component cut before a word in the second.

Each clause takes one triple of half-twists and corrects the mixed word
there. `clause₀` reads the triple `(corx x , rx x , corx x)` and
corrects with `corr₀`. `clause₁` reads `(rx x , corx x , corx x)` and
corrects with `corr₁`. In both, the right bracketing is the left one
with the correction word cut in front of it. `mediates₂` asks for the
two clauses together, and for no other triple.

The equivalence condition reads each component in one hand: the first
in the negative hand, the second in the positive one.

```agda
module mediation {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx) where

  open tower G rx corx S C⁺ C⁻ public
  open mediation⁺ G rx S C⁺ public using (is-eqv⁺; eqv-2-out-of-3; module canonical)
  open mediation⁻ G corx S C⁻ public using (is-eqv⁻)

  pair : ob → Type h
  pair x = hom x x × hom x x

  corr₀ : ∀ {x} → pair x → hom x x
  corr₀ p = p .snd

  corr₁ : ∀ {x} → pair x → hom x x
  corr₁ p = p .fst ⨾⁺ (p .snd ⨾⁺ (p .snd ⨾⁻ p .snd))

  clause₀ : (x : ob) → pair x → Type h
  clause₀ x p =
      corx x ⨾⁺ (rx x ⨾⁻ corx x)
    ≡ corr₀ p ⨾⁺ ((corx x ⨾⁺ rx x) ⨾⁻ corx x)

  clause₁ : (x : ob) → pair x → Type h
  clause₁ x p =
      rx x ⨾⁺ (corx x ⨾⁻ corx x)
    ≡ corr₁ p ⨾⁺ ((rx x ⨾⁺ corx x) ⨾⁻ corx x)

  mediates₂ : (x : ob) → pair x → Type h
  mediates₂ x p = clause₀ x p × clause₁ x p

  is-eqv-pair : (x : ob) → pair x → Type (o ⊔ h)
  is-eqv-pair x p = is-eqv⁻ (p .fst) × is-eqv⁺ (p .snd)

  is-eqv-pair-is-prop : (x : ob) (p : pair x) → is-prop (is-eqv-pair x p)
  is-eqv-pair-is-prop x p =
    is-prop-×
      (is-prop-× (Π-is-prop λ _ → is-equiv-is-prop _)
                 (Π-is-prop λ _ → is-equiv-is-prop _))
      (is-prop-× (Π-is-prop λ _ → is-equiv-is-prop _)
                 (Π-is-prop λ _ → is-equiv-is-prop _))
```

A framing at an object is a candidate there with the equivalence
condition and the two clauses. Where every object carries a
contractible one, the whole family is a proposition.

```agda
  framed : (x : ob) → Type (o ⊔ h)
  framed x = Σ p ∶ pair x , (is-eqv-pair x p × mediates₂ x p)

  framed-is-prop : (∀ x → is-contr (framed x)) → is-prop (∀ x → framed x)
  framed-is-prop c = Π-is-prop λ x → is-contr→is-prop (c x)
```

## The self-referential clauses

The self-referential form puts the candidate in every slot of the two
triples: each `corx` becomes the second component and each `rx` the
first. The correction words read the pair alone already, so they
carry over unchanged. Nothing the clauses state names a half-twist family.
Both half-twist families still enter through the two cut hypotheses.
`is-composable⁺` closes the term half at `var`, and `is-composable⁻`
closes the coterm half at `covar`.

```agda
module self {o h} (G : virtual-graph o h) (open virtual-graph G)
  (rx corx : (x : ob) → hom x x)
  (S : reflect-is-embedding G)
  (C⁺ : framing⁻.is-composable⁺ G rx)
  (C⁻ : framing⁺.is-composable⁻ G corx) where

  open mediation G rx corx S C⁺ C⁻ public
    using ( _⨾⁺_; _⨾⁻_; pair; corr₀; corr₁
          ; is-eqv⁺; is-eqv⁻; is-eqv-pair; is-eqv-pair-is-prop )

  selfclause₀ : (x : ob) → pair x → Type h
  selfclause₀ x p =
      p .snd ⨾⁺ (p .fst ⨾⁻ p .snd)
    ≡ corr₀ p ⨾⁺ ((p .snd ⨾⁺ p .fst) ⨾⁻ p .snd)

  selfclause₁ : (x : ob) → pair x → Type h
  selfclause₁ x p =
      p .fst ⨾⁺ (p .snd ⨾⁻ p .snd)
    ≡ corr₁ p ⨾⁺ ((p .fst ⨾⁺ p .snd) ⨾⁻ p .snd)

  selfmediates₂ : (x : ob) → pair x → Type h
  selfmediates₂ x p = selfclause₀ x p × selfclause₁ x p

  framed : (x : ob) → Type (o ⊔ h)
  framed x = Σ p ∶ pair x , (is-eqv-pair x p × selfmediates₂ x p)

  framed-is-prop : (∀ x → is-contr (framed x)) → is-prop (∀ x → framed x)
  framed-is-prop c = Π-is-prop λ x → is-contr→is-prop (c x)
```
