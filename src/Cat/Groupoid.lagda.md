Lane Biocini
March 2026

The path groupoid of a type, as a Cat.Type category.

For any type `A`, the yon-unbiased embedding
`emb q w p z r = pcom (sym p) q r` gives the ternary
composition structure. The identity `refl` absorbs via
`Path.unitl` and `Path.unitr`. Composition is path
concatenation. Interchange follows from `pcom.lsplit`
and `pcom.rsplit`.

The `category` record is from `Cat.Type`; the ternary embedding
and its equivalence are from `Core.Groupoid.Virtual`. The
instance bridges the two, so it lives in its own module and keeps
`Cat.Type` free of the groupoid dependency.

kept at the top of this file to stay self-contained.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Groupoid where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Sub
open import Core.Kan
open import Core.Path.Base
open import Core.Equiv.Base using (is-equiv; eqv-fibers; iso→equiv)
open import Core.Equiv.Properties using (comp-equiv)
open import Core.Function.Embedding
open import Core.Groupoid.Virtual
open import Cat.Type
```

## The contractible spine tail

Fixing `p : x ≡ y` and `ι : y ≡ z`, a path `q : x ≡ z` together with a
square `PathP (λ i → x ≡ ι i) p q` is contractible data: the center is
`(p ∙ ι , slide p ι)`, and the contraction is one cube whose faces are
`slide p ι` (`k = i0`), `θ` (`k = i1`), the constant `x` (`j = i0`),
and `ι` itself (`j = i1`), over the base `p`. All edge overlaps agree
definitionally.

```agda
spine-tail : ∀ {u} {H : Type u} {x y z : H}
             (p : x ≡ y) (ι : y ≡ z)
           → is-contr (Σ q ∶ (x ≡ z) , PathP (λ i → x ≡ ι i) p q)
spine-tail {x = x} p ι .center = (p ∙ ι) , slide p ι
spine-tail {x = x} p ι .paths (q , θ) k =
  (λ j → κ k i1 j) , λ i j → κ k i j
  where
    κ : I → I → I → _
    κ k i j = hfil (∂ k ∨ ∂ j) i λ where
      l (l = i0) → p j
      l (k = i0) → slide p ι l j
      l (k = i1) → θ l j
      l (j = i0) → x
      l (j = i1) → ι l
```

## The path groupoid

`E`, its equivalence, and the currying glue are unchanged from March.

```agda
module _ {u} (A : Type u) where
  private
    E : {x y : A} → x ≡ y
      → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
    E = yon-unbiased.emb {A = λ _ → A}

    E-equiv : {x y : A} → is-equiv (E {x} {y})
    E-equiv = yon-unbiased.emb-equiv {A = λ _ → A}

    uncurryE : {x y : A}
      → (∀ w → w ≡ x → ∀ v → y ≡ v → w ≡ v)
      → (γ : (Σ w ∶ A , w ≡ x) × (Σ v ∶ A , y ≡ v))
      → γ .fst .fst ≡ γ .snd .fst
    uncurryE G γ =
      G (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

    curryE : {x y : A}
      → ((γ : (Σ w ∶ A , w ≡ x) × (Σ v ∶ A , y ≡ v))
          → γ .fst .fst ≡ γ .snd .fst)
      → ∀ w → w ≡ x → ∀ v → y ≡ v → w ≡ v
    curryE F w a v b = F ((w , a) , (v , b))

    uncurryE-equiv : {x y : A} → is-equiv (uncurryE {x} {y})
    uncurryE-equiv =
      iso→equiv uncurryE curryE (λ _ → refl) (λ _ → refl) .snd

    emb-equiv : {x y : A}
      → is-equiv (λ (f : x ≡ y) → uncurryE (E f))
    emb-equiv = comp-equiv E-equiv uncurryE-equiv

    gpd-interchange
      : {x y z : A} (f : x ≡ y) (g : y ≡ z)
        (w : A) (a : w ≡ x) (v : A) (b : z ≡ v)
      → E f w a v (E g _ refl v b)
      ≡ E g w (E f w a _ refl) v b
    gpd-interchange f g w a v b =
      pcom.lsplit a f (pcom refl g b)
      ∙ pcom.lr
          (pcom (sym a) f refl) (pcom refl g b)
      ∙ sym (pcom.rsplit
              (pcom (sym a) f refl) g b)

    gpd-post-eval
      : {x y : A} (f : x ≡ y)
      → E f x refl y refl ≡ f
    gpd-post-eval f = pcom.unit f

  path-Rx : reflexive-graph u u
  path-Rx .reflexive-graph.ob = A
  path-Rx .reflexive-graph.edge = _≡_
  path-Rx .reflexive-graph.rx x = refl

  open virtual path-Rx

  private
    gpd-emb : ∀ {x y : A} → x ≡ y → composite x y
    gpd-emb f = uncurryE (E f)

  open representable path-Rx gpd-emb

  private
    -- interchange, packaged as a path between composites.
    -- `gpd-emb f ▾ g` and `f ▴ gpd-emb g` unfold to the two sides of
    -- the March equation by Σ-η.
    ι : ∀ {x y z : A} (f : x ≡ y) (g : y ≡ z)
      → gpd-emb f ▾ g ≡ f ▴ gpd-emb g
    ι f g = funext λ γ →
      gpd-interchange f g
        (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

    -- the field, proven in its own shape: the March equation at the
    -- representing paths, conjugated by the ▿/▵ lines of the witness
    -- identifications — the one-sided composites in ι's type collapse
    -- to the ternary orders against the embedded factors
    ι♭ : ∀ {x y z : A} {F : composite x y} {G : composite y z}
       → fiber gpd-emb F → fiber gpd-emb G → F ▿ G ≡ F ▵ G
    ι♭ (m , p) (n , q) =
      sym (λ i → p i ▿ q i) ∙ ι m n ∙ (λ i → p i ▵ q i)

    -- the record's `spine`, with `interchange f g` computed from `ι♭`
    Spine : ∀ {x y z : A} (f : x ≡ y) (g : y ≡ z) → Type u
    Spine {x} {y} {z} f g =
      Σ k ∶ (x ≡ z) ,
      Σ p ∶ (gpd-emb k ≡ gpd-emb f ▾ g) ,
      Σ q ∶ (gpd-emb k ≡ f ▴ gpd-emb g) ,
        PathP (λ i → gpd-emb k ≡ ι♭ (nrm f) (nrm g) i) p q

    spine-contr-impl
      : ∀ {x y z : A} (f : x ≡ y) (g : y ≡ z) → is-contr (Spine f g)
    spine-contr-impl f g = reshape c
      where
        c = Σ-contr-contr (eqv-fibers emb-equiv (gpd-emb f ▾ g))
              λ (k , p) → spine-tail p (ι♭ (nrm f) (nrm g))

        reshape : is-contr (Σ λ (k , p) →
                    Σ q ∶ (gpd-emb k ≡ f ▴ gpd-emb g) ,
                      PathP (λ i → gpd-emb k ≡ ι♭ (nrm f) (nrm g) i) p q)
                → is-contr (Spine f g)
        reshape c .center =
          c .center .fst .fst , c .center .fst .snd ,
          c .center .snd .fst , c .center .snd .snd
        reshape c .paths (k , p , q , θ) i =
          φ i .fst .fst , φ i .fst .snd , φ i .snd .fst , φ i .snd .snd
          where φ = c .paths ((k , p) , (q , θ))

  gpd-axioms : category-axioms path-Rx
  gpd-axioms .category-axioms.emb = gpd-emb
  gpd-axioms .category-axioms.interchange♭ = ι♭
  gpd-axioms .category-axioms.spine-contr = spine-contr-impl
  gpd-axioms .category-axioms.unit = gpd-post-eval

  ∞-groupoid : category u u
  ∞-groupoid .category.structure = path-Rx
  ∞-groupoid .category.axioms = gpd-axioms
