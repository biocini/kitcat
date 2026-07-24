Lane Biocini
July 2026

Countermodel: the embedding is irreducible structure. Over the
one-object graph whose edges are the endofunctions of `Bool`, two
distinct embeddings — one reading the context forward, one backward,
realizing a composition and its opposite — each satisfy pull- and
push-fiber contractibility, readback, both unit-action equivalences,
idempotence of the derived identity composite, and interchange. The
axiom package therefore never determines its embedding: the Σ-type
pairing an embedding with the package is not a proposition.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.OpTwist where

open import Core.Type
open import Core.Base
open import Core.Kan
open import Core.Transport
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Data.Nat.Type
open import Core.Data.Bool
open import Core.Equiv.Base using (is-equiv; id-equiv)
open import Core.HLevel.Base using (Π-is-hlevel)

open import Cat.Depreciated.Type
```

## The one-object endofunction graph

Composition of endofunctions is strictly associative and strictly
unital, so the collapse identities below hold judgmentally.

```agda
op-graph : reflexive-graph 0ℓ 0ℓ
op-graph .reflexive-graph.ob = ⊤
op-graph .reflexive-graph.edge _ _ = Bool → Bool
op-graph .reflexive-graph.rx _ = λ x → x

open virtual op-graph

hom-set : is-set (Bool → Bool)
hom-set = Π-is-hlevel (S (S Z)) (λ _ → Bool.set)

composite-set : ∀ {x y} → is-set (composite x y)
composite-set = Π-is-hlevel (S (S Z)) (λ _ → hom-set)
```

## The two embeddings

The forward embedding runs the arc `a`, then the morphism, then `b`.
The reverse embedding reads the context backwards — well-typed only
because a single object makes every edge composable with every other —
and so realizes the opposite composition on the same carrier.

```agda
emb-fwd : ∀ {x y} → hom x y → composite x y
emb-fwd g γ x = γ .snd .snd (g (γ .fst .snd x))

emb-rev : ∀ {x y} → hom x y → composite x y
emb-rev g γ x = γ .fst .snd (g (γ .snd .snd x))
```

## Fiber collapse

For any embedding whose evaluation at the identity context restores
the morphism, the fiber over an image point is contractible: reading
a path of composites at the identity context recovers a path of
morphisms, and composites form a set.

```agda
module kernel
  (emb : ∀ {x y} → hom x y → composite x y)
  (rd : (g : Bool → Bool) → ev (emb g) ≡ g)
  where

  image-contr : (k : Bool → Bool) → is-contr (fiber emb (emb k))
  image-contr k .center = k , refl
  image-contr k .paths (j , p) i =
    q i , is-prop→PathP (λ i' → composite-set (emb (q i')) (emb k)) refl p i
    where
      q : k ≡ j
      q = sym (sym (rd j) ∙ happly p (ov-idn tt , un-idn tt) ∙ rd k)
```

## The axiom package

Everything the representable apparatus asks of an embedding, stated
generically: contractibility of both one-sided fibers, readback, the
two unit actions as equivalences, idempotence of the derived identity
composite, and interchange.

```agda
record axioms (emb : ∀ {x y} → hom x y → composite x y) : Type 0ℓ where
  open representable op-graph emb

  field
    pull-contr : (f g : Bool → Bool) → is-contr (fiber emb (emb f ▾ g))
    push-contr : (f g : Bool → Bool) → is-contr (fiber emb (f ▴ emb g))
    readback   : (g : Bool → Bool) → ev (emb g) ≡ g
    eqvl       : is-equiv (λ (b : Bool → Bool) → pre (λ x → x) b)
    eqvr       : is-equiv (λ (a : Bool → Bool) → post (λ x → x) a)

  _⨾_ : (Bool → Bool) → (Bool → Bool) → Bool → Bool
  f ⨾ g = pull-contr f g .center .fst

  field
    idem        : ((λ x → x) ⨾ (λ x → x)) ≡ (λ x → x)
    interchange : (f g : Bool → Bool) → (emb f ▾ g) ≡ (f ▴ emb g)
```

## Both embeddings satisfy the package

Strict associativity puts each one-sided composite judgmentally in
the image — of `g ∘ f` for the forward embedding, of `f ∘ g` for the
reverse — so every field except the fiber contractions is `refl`, and
those are the collapse lemma at the appropriate composite.

```agda
module fwd = kernel emb-fwd (λ g → refl)
module rev = kernel emb-rev (λ g → refl)

pkg-fwd : axioms emb-fwd
pkg-fwd .axioms.pull-contr f g  = fwd.image-contr (λ x → g (f x))
pkg-fwd .axioms.push-contr f g  = fwd.image-contr (λ x → g (f x))
pkg-fwd .axioms.readback g      = refl
pkg-fwd .axioms.eqvl            = id-equiv
pkg-fwd .axioms.eqvr            = id-equiv
pkg-fwd .axioms.idem            = refl
pkg-fwd .axioms.interchange f g = refl

pkg-rev : axioms emb-rev
pkg-rev .axioms.pull-contr f g  = rev.image-contr (λ x → f (g x))
pkg-rev .axioms.push-contr f g  = rev.image-contr (λ x → f (g x))
pkg-rev .axioms.readback g      = refl
pkg-rev .axioms.eqvl            = id-equiv
pkg-rev .axioms.eqvr            = id-equiv
pkg-rev .axioms.idem            = refl
pkg-rev .axioms.interchange f g = refl
```

## The separation

The carrier is noncommutative, and a single context witnesses it:
with `a` constantly `true` and `b` negation, the forward embedding of
the identity evaluates to `false` where the reverse gives `true`.
Hence the two package-carrying inhabitants of the Σ-type admit no
path, and the type of axiom-satisfying embeddings is not
propositional.

```agda
discrim : Bool → Type
discrim true  = ⊥
discrim false = ⊤

false≢true : false ≡ true → ⊥
false≢true p = subst discrim p tt

op-ctx : ctx tt tt
op-ctx = (tt , (λ _ → true)) , (tt , Bool.not)

fwd≢rev : Path (∀ {x y} → hom x y → composite x y) emb-fwd emb-rev → ⊥
fwd≢rev p = false≢true (λ i → p i (λ x → x) op-ctx true)

emb-not-prop : is-prop (Σ axioms) → ⊥
emb-not-prop h = fwd≢rev (ap fst (h (emb-fwd , pkg-fwd) (emb-rev , pkg-rev)))
```
