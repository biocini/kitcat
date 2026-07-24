Lane Biocini
July 2026

Monoidal categories, presented through representable tensor
embeddings. The axioms assert two things and no more: the tensor's
normal forms exist uniquely (`⊗₀-pull-contr`, contractibility of the
embedding's fiber over the one-sided composite), and the two nesting
orders of a pair of composites are identified by *declared* structure
— two independent fields `ι⁺` and `ι⁻`, with no axiom relating them.
Every comparison consuming such an identification is derived once,
over an arbitrary one, and instantiated at either field; the loop
`ω = ι⁺ ∙ sym ι⁻` measuring their discrepancy is a definition. The
prior presentation, which fixes a single identification inside the
contractibility axiom, is archived as `Cat.Depreciated.Monoidal.Legacy`; it is
recovered from this record by keeping either field alone, and the
comparison of the two presentations lives in
`Cat.Depreciated.Monoidal.Properties`. The morphism grade repeats the shape one
level up: `monoidal-axioms₁` carries the displaced embedding, one
displaced interchange field over each of `ι⁺`/`ι⁻`, contractibility
of the displaced pull fiber — `⊗₁-wit` at the level-0 pull centers —
the displaced readback law, and the enrichment law; `theory₁`
extracts the hom-grade tensor and proves the displaced spine over
any interchange pair by the same two lemmas as at grade 0, with the
displaced tail supplied by the singleton over a line of path types.
The bundle `monoidal` coalesces the grades.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Depreciated.Monoidal where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base
open import Core.Transport.J using (J; subst)
open import Core.Transport.Properties using (is-contr-is-prop; SinglP-contr)
open import Core.Equiv.Base using (is-equiv; iso→equiv; _≃_; id-equiv)
open import Core.Function.Embedding
  using (image-fibers-contr→is-embedding; equiv→lc)

open import Cat.Depreciated.Type
open import Cat.Depreciated.Base
open import Cat.Depreciated.Groupoid using (spine-tail)
```

## Level 0: the tensor context calculus

`virtual`, transcribed: the over-slot is a left tensorand, the
under-slot a right tensorand; `ov-idn` and `un-idn` both collapse to
the unit `I`. `⊗₀-res` is constant because the anonymous endpoints of
the arc have been erased.

```agda
module tensor-virtual {o h} (C : category o h) (I : category.ob C) where
  private module C = category C

  ⊗₀-ctx : Type o
  ⊗₀-ctx = C.ob × C.ob

  ⊗₀-emp : C.ob → C.ob → ⊗₀-ctx
  ⊗₀-emp l r = l , r

  ⊗₀-res : ⊗₀-ctx → Type o
  ⊗₀-res _ = C.ob

  ⊗₀-composite : Type o
  ⊗₀-composite = (γ : ⊗₀-ctx) → ⊗₀-res γ

  ⊗₀-ev : ⊗₀-composite → C.ob
  ⊗₀-ev F = F (I , I)
```

## The representable tensor

Token-for-token transcription of `Cat.Depreciated.Type.representable` under the
dictionary hom ↦ ob, idn ↦ I. `⊗₀-emb x (l , r)` is the two-sided
tensor action: the left factor `l`, the cell `x` in the middle slot,
the right factor `r`.

```agda
module tensor-representable {o h} (C : category o h) (I : category.ob C)
  (⊗₀-emb : category.ob C → tensor-virtual.⊗₀-composite C I) where

  open tensor-virtual C I
  private module C = category C

  is-⊗₀-representable : ⊗₀-composite → Type o
  is-⊗₀-representable = fiber ⊗₀-emb

  _⊨₀_ : ⊗₀-composite → C.ob → Type o
  F ⊨₀ s = ⊗₀-emb s ≡ F

  ⊗₀-pre : C.ob → C.ob → C.ob
  ⊗₀-pre y r = ⊗₀-emb y (I , r)

  ⊗₀-post : C.ob → C.ob → C.ob
  ⊗₀-post x l = ⊗₀-emb x (l , I)

  ⊗₀-sub : C.ob → ⊗₀-ctx → ⊗₀-ctx
  ⊗₀-sub y (l , r) = l , ⊗₀-pre y r

  ⊗₀-cosub : C.ob → ⊗₀-ctx → ⊗₀-ctx
  ⊗₀-cosub x (l , r) = ⊗₀-post x l , r

  ⊗₀-nrm : (x : C.ob) → is-⊗₀-representable (⊗₀-emb x)
  ⊗₀-nrm x = x , refl

  _▾₀_ : ⊗₀-composite → C.ob → ⊗₀-composite
  (F ▾₀ y) γ = F (⊗₀-sub y γ)
  infixl 30 _▾₀_

  _▴₀_ : C.ob → ⊗₀-composite → ⊗₀-composite
  (x ▴₀ G) γ = G (⊗₀-cosub x γ)
  infixl 30 _▴₀_

  _▿₀_ : ⊗₀-composite → ⊗₀-composite → ⊗₀-composite
  (F ▿₀ G) γ = F (γ .fst , G (I , γ .snd))
  infixl 30 _▿₀_

  _▵₀_ : ⊗₀-composite → ⊗₀-composite → ⊗₀-composite
  (F ▵₀ G) γ = G (F (γ .fst , I) , γ .snd)
  infixl 30 _▵₀_
```

## `monoidal-axioms₀`

The field list: the unit, the embedding, the two interchange
structures in witness form, the contractibility of the pull fiber,
and the readback law. The pull fiber never mentions an interchange
path, and no field relates `ι⁺` to `ι⁻`: their discrepancy `ω` is
derived, and whatever invariant it generates in an instance is an
output of that instance, never an input to the record.

```agda
record monoidal-axioms₀ {o h} (C : category o h) : Type₊ o where
  private module C = category C

  field
    I      : C.ob
    ⊗₀-emb : C.ob → tensor-virtual.⊗₀-composite C I

  open tensor-virtual C I public
  open tensor-representable C I ⊗₀-emb public

  field
    ι⁺ ι⁻ : {A B : ⊗₀-composite}
          → is-⊗₀-representable A → is-⊗₀-representable B
          → A ▿₀ B ≡ A ▵₀ B
    ⊗₀-pull-contr : (x y : C.ob) → is-contr (fiber ⊗₀-emb (⊗₀-emb x ▾₀ y))
    ⊗₀-unit       : (x : C.ob) → ⊗₀-ev (⊗₀-emb x) ≡ x

  ι⁺-pt : (x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y
  ι⁺-pt x y = ι⁺ (⊗₀-nrm x) (⊗₀-nrm y)

  ι⁻-pt : (x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y
  ι⁻-pt x y = ι⁻ (⊗₀-nrm x) (⊗₀-nrm y)

  ω : {A B : ⊗₀-composite}
    → is-⊗₀-representable A → is-⊗₀-representable B
    → A ▿₀ B ≡ A ▿₀ B
  ω U V = ι⁺ U V ∙ sym (ι⁻ U V)

  ω-pt : (x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ ⊗₀-emb x ▾₀ y
  ω-pt x y = ι⁺-pt x y ∙ sym (ι⁻-pt x y)
```

## `theory₀`: cells that consume no interchange path

The pull-side chain. The tensor and its pre-side comparison project
from the contractibility field, and nothing in this group mentions
`ι⁺` or `ι⁻`.

```agda
module theory₀ {o h} {C : category o h} (M₀ : monoidal-axioms₀ C) where
  open monoidal-axioms₀ M₀
  private module C = category C

  _⊗₀_ : C.ob → C.ob → C.ob
  x ⊗₀ y = ⊗₀-pull-contr x y .center .fst
  infixr 40 _⊗₀_

  ⊗₀-emb-comp : (x y : C.ob) → ⊗₀-emb (x ⊗₀ y) ≡ ⊗₀-emb x ▾₀ y
  ⊗₀-emb-comp x y = ⊗₀-pull-contr x y .center .snd

  _●₀_ : ∀ {F G : ⊗₀-composite}
      → is-⊗₀-representable F → is-⊗₀-representable G
      → is-⊗₀-representable (F ▿₀ G)
  (m , p) ●₀ (n , q) = m ⊗₀ n , ⊗₀-emb-comp m n ∙ (λ i → p i ▿₀ q i)
  infixr 40 _●₀_

  ⊗₀-cast-path : ∀ {x y k} → (⊗₀-emb x ▾₀ y) ⊨₀ k → x ⊗₀ y ≡ k
  ⊗₀-cast-path {x} {y} {k} α = ap fst (⊗₀-pull-contr x y .paths (k , α))

  ⊗₀-cast-path⁻¹ : ∀ {x y k} → x ⊗₀ y ≡ k → (⊗₀-emb x ▾₀ y) ⊨₀ k
  ⊗₀-cast-path⁻¹ {x} {y} p = ap ⊗₀-emb (sym p) ∙ ⊗₀-emb-comp x y

  ⊗₀-comp-eq-ev : ∀ x y → x ⊗₀ y ≡ ⊗₀-ev (⊗₀-emb x ▾₀ y)
  ⊗₀-comp-eq-ev x y = sym (⊗₀-unit (x ⊗₀ y)) ∙ ap ⊗₀-ev (⊗₀-emb-comp x y)

  ⊗₀-comp-eq-pre : ∀ x y → x ⊗₀ y ≡ ⊗₀-pre x y
  ⊗₀-comp-eq-pre x y = ⊗₀-comp-eq-ev x y ∙ ap (⊗₀-pre x) (⊗₀-unit y)

  ⊗₀-idem : I ⊗₀ I ≡ I
  ⊗₀-idem = ⊗₀-comp-eq-pre I I ∙ ⊗₀-unit I

  ⊗₀-pre-distr : ∀ x y r → ⊗₀-pre (x ⊗₀ y) r ≡ ⊗₀-pre x (⊗₀-pre y r)
  ⊗₀-pre-distr x y r = happly (⊗₀-emb-comp x y) (I , r)

  ▾₀-comp : ∀ (F : ⊗₀-composite) y z → F ▾₀ (y ⊗₀ z) ≡ (F ▾₀ y) ▾₀ z
  ▾₀-comp F y z = ap (F ▿₀_) (⊗₀-emb-comp y z)

  ⊗₀-ob≃total-representable : C.ob ≃ (Σ F ∶ ⊗₀-composite , is-⊗₀-representable F)
  ⊗₀-ob≃total-representable = iso→equiv to fro ob-ret rep-sec
    where
      to : C.ob → Σ F ∶ ⊗₀-composite , is-⊗₀-representable F
      to x = ⊗₀-emb x , ⊗₀-nrm x

      fro : (Σ F ∶ ⊗₀-composite , is-⊗₀-representable F) → C.ob
      fro (_ , a , _) = a

      ob-ret : ∀ x → fro (to x) ≡ x
      ob-ret x = refl

      rep-sec : ∀ s → to (fro s) ≡ s
      rep-sec (_ , a , p) = J (λ F' p' → to a ≡ (F' , a , p')) refl p
```

## Cells over an interchange path

Developed once, over an arbitrary identification of the two nesting
orders, and instantiated at either field. The post-side comparison is
the pre-side comparison extended along the identification, so the
compatibility square is the concatenation filler and `⊗₀-coh→∙` holds
by `refl`; the full spine over the identification is a theorem
(`spine-tail` extending the pull center). The statements in this
module are independent of which identification is supplied — only the
produced paths differ across the two fields, by evaluated `ω`.

```agda
  module over-interchange
    (ι : (x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y) where

    ⊗₀-emb-comp-op : (x y : C.ob) → ⊗₀-emb (x ⊗₀ y) ≡ x ▴₀ ⊗₀-emb y
    ⊗₀-emb-comp-op x y = ⊗₀-emb-comp x y ∙ ι x y

    ⊗₀-emb-comp-coh
      : (x y : C.ob)
      → PathP (λ i → ⊗₀-emb (x ⊗₀ y) ≡ ι x y i)
              (⊗₀-emb-comp x y) (⊗₀-emb-comp-op x y)
    ⊗₀-emb-comp-coh x y = slide (⊗₀-emb-comp x y) (ι x y)

    ⊗₀-coh→∙ : ∀ x y → ⊗₀-emb-comp x y ∙ ι x y ≡ ⊗₀-emb-comp-op x y
    ⊗₀-coh→∙ x y = refl

    ⊗₀-spine-contr
      : (x y : C.ob)
      → is-contr (Σ s ∶ C.ob ,
          Σ p ∶ (⊗₀-emb s ≡ ⊗₀-emb x ▾₀ y) ,
          Σ q ∶ (⊗₀-emb s ≡ x ▴₀ ⊗₀-emb y) ,
            PathP (λ i → ⊗₀-emb s ≡ ι x y i) p q)
    ⊗₀-spine-contr x y = reshape c
      where
        c = Σ-contr-contr (⊗₀-pull-contr x y)
              λ (k , p) → spine-tail p (ι x y)

        reshape
          : is-contr (Σ λ (k , p) →
              Σ q ∶ (⊗₀-emb k ≡ x ▴₀ ⊗₀-emb y) ,
                PathP (λ i → ⊗₀-emb k ≡ ι x y i) p q)
          → is-contr (Σ s ∶ C.ob ,
              Σ p ∶ (⊗₀-emb s ≡ ⊗₀-emb x ▾₀ y) ,
              Σ q ∶ (⊗₀-emb s ≡ x ▴₀ ⊗₀-emb y) ,
                PathP (λ i → ⊗₀-emb s ≡ ι x y i) p q)
        reshape c' .center =
          c' .center .fst .fst , c' .center .fst .snd ,
          c' .center .snd .fst , c' .center .snd .snd
        reshape c' .paths (k , p , q , θ) i =
          φ i .fst .fst , φ i .fst .snd , φ i .snd .fst , φ i .snd .snd
          where φ = c' .paths ((k , p) , (q , θ))

    _○₀_ : ∀ {F G : ⊗₀-composite}
          → is-⊗₀-representable F → is-⊗₀-representable G
          → is-⊗₀-representable (F ▵₀ G)
    (m , p) ○₀ (n , q) = m ⊗₀ n , ⊗₀-emb-comp-op m n ∙ (λ i → p i ▵₀ q i)

    ⊗₀-push-contr : ∀ x y → is-contr (fiber ⊗₀-emb (x ▴₀ ⊗₀-emb y))
    ⊗₀-push-contr x y =
      subst (λ F → is-contr (fiber ⊗₀-emb F)) (ι x y) (⊗₀-pull-contr x y)
```

### The unit-law chain

```agda
    ⊗₀-comp-eq-post : ∀ x y → x ⊗₀ y ≡ ⊗₀-post y x
    ⊗₀-comp-eq-post x y =
      sym (⊗₀-unit (x ⊗₀ y)) ∙ ap ⊗₀-ev (⊗₀-emb-comp-op x y)
      ∙ ap (⊗₀-post y) (⊗₀-unit x)

    ⊗₀-pre-is-post : ∀ x y → ⊗₀-pre x y ≡ ⊗₀-post y x
    ⊗₀-pre-is-post x y = sym (⊗₀-comp-eq-pre x y) ∙ ⊗₀-comp-eq-post x y

    ⊗₀-absorb-l : ∀ r → ⊗₀-pre I r ≡ r
    ⊗₀-absorb-l r = ⊗₀-pre-is-post I r ∙ ⊗₀-unit r

    ⊗₀-absorb-r : ∀ l → ⊗₀-post I l ≡ l
    ⊗₀-absorb-r l = sym (⊗₀-pre-is-post l I) ∙ ⊗₀-unit l

    ⊗₀-idn-▴ : ∀ (F : ⊗₀-composite) → I ▴₀ F ≡ F
    ⊗₀-idn-▴ F = funext λ (l , r) → ap (λ t → F (t , r)) (⊗₀-absorb-r l)

    ▾₀-idn : ∀ (F : ⊗₀-composite) → F ▾₀ I ≡ F
    ▾₀-idn F = funext λ (l , r) → ap (λ t → F (l , t)) (⊗₀-absorb-l r)

    ⊗₀-emb-image-contr : ∀ x → is-contr (fiber ⊗₀-emb (⊗₀-emb x))
    ⊗₀-emb-image-contr x =
      subst (λ F → is-contr (fiber ⊗₀-emb F))
        (⊗₀-idn-▴ (⊗₀-emb x)) (⊗₀-push-contr I x)

    ⊗₀-emb-idn-absorb : ∀ x → ⊗₀-emb I ▾₀ x ≡ ⊗₀-emb x
    ⊗₀-emb-idn-absorb x = ι I x ∙ ⊗₀-idn-▴ (⊗₀-emb x)

    ⊗₀-emb-post : ∀ x l r → ⊗₀-emb x (l , r) ≡ ⊗₀-emb I (⊗₀-post x l , r)
    ⊗₀-emb-post x l r =
      ap (λ t → ⊗₀-emb x (l , t)) (sym (⊗₀-absorb-l r))
      ∙ happly (ι x I) (l , r)

    ⊗₀-emb-pre : ∀ x l r → ⊗₀-emb x (l , r) ≡ ⊗₀-emb I (l , ⊗₀-pre x r)
    ⊗₀-emb-pre x l r =
      ap (λ t → ⊗₀-emb x (t , r)) (sym (⊗₀-absorb-r l))
      ∙ sym (happly (ι I x) (l , r))

    ⊗₀-emb-normal : ∀ x l r → ⊗₀-emb x (l , r) ≡ ⊗₀-post r (⊗₀-post x l)
    ⊗₀-emb-normal x l r =
      ⊗₀-emb-post x l r
      ∙ ap (λ t → ⊗₀-emb I (⊗₀-post x l , t)) (sym (⊗₀-unit r))
      ∙ happly (ι I r) (⊗₀-post x l , I)
      ∙ ap (λ t → ⊗₀-emb r (t , I)) (⊗₀-absorb-r (⊗₀-post x l))

    ⊗₀-post-distr : ∀ x y l → ⊗₀-post (x ⊗₀ y) l ≡ ⊗₀-post y (⊗₀-post x l)
    ⊗₀-post-distr x y l = happly (⊗₀-emb-comp-op x y) (l , I)

    ⊗₀-unit-is-prop
      : (e : C.ob)
      → is-equiv (λ l → ⊗₀-emb e (l , e))
      → ⊗₀-post e e ≡ e
      → e ≡ I
    ⊗₀-unit-is-prop e re idpt = sym (⊗₀-unit e) ∙ post-e-absorb I
      where
        e-idem : e ⊗₀ e ≡ e
        e-idem = ⊗₀-comp-eq-post e e ∙ idpt

        post-e-idpt : ∀ l → ⊗₀-post e (⊗₀-post e l) ≡ ⊗₀-post e l
        post-e-idpt l = sym (⊗₀-post-distr e e l) ∙ ap (λ t → ⊗₀-post t l) e-idem

        post-e-absorb : ∀ l → ⊗₀-post e l ≡ l
        post-e-absorb l = equiv→lc re
          (⊗₀-emb-normal e (⊗₀-post e l) e
          ∙ post-e-idpt (⊗₀-post e l)
          ∙ sym (⊗₀-emb-normal e l e))

    ⊗₀-unit-eqvl : is-equiv (λ (r : C.ob) → ⊗₀-pre I r)
    ⊗₀-unit-eqvl = subst is-equiv (funext λ r → sym (⊗₀-absorb-l r)) id-equiv

    ⊗₀-unit-eqvr : is-equiv (λ (l : C.ob) → ⊗₀-post I l)
    ⊗₀-unit-eqvr = subst is-equiv (funext λ l → sym (⊗₀-absorb-r l)) id-equiv
```

## The representability calculus

The embedding property is landed through `ι⁺`, and `is-contr-is-prop`
certifies the element is the same through `ι⁻`: everything below is
insensitive to the choice. The calculus and the associativity block
are the archived forms unchanged.

```agda
  ⊗₀-emb-image-contr : ∀ x → is-contr (fiber ⊗₀-emb (⊗₀-emb x))
  ⊗₀-emb-image-contr = over-interchange.⊗₀-emb-image-contr ι⁺-pt

  image-contr-invariant
    : ∀ x → over-interchange.⊗₀-emb-image-contr ι⁺-pt x
          ≡ over-interchange.⊗₀-emb-image-contr ι⁻-pt x
  image-contr-invariant x = is-contr-is-prop _ _ _

  is-⊗₀-representable-prop : ∀ F → is-prop (is-⊗₀-representable F)
  is-⊗₀-representable-prop = image-fibers-contr→is-embedding ⊗₀-emb-image-contr

  ⊗₀-rep-contr : ∀ {F} → is-⊗₀-representable F → is-contr (is-⊗₀-representable F)
  ⊗₀-rep-contr {F} u .center = u
  ⊗₀-rep-contr {F} u .paths = is-⊗₀-representable-prop F u

  ⊗₀-repr-unique : ∀ {F} (u v : is-⊗₀-representable F) → u .fst ≡ v .fst
  ⊗₀-repr-unique {F} u v = ap fst (is-⊗₀-representable-prop F u v)

  ⊗₀-repr-lc : ∀ {F} {U V : is-⊗₀-representable F}
            → (κ : U ≡ V) → ap fst κ ≡ ⊗₀-repr-unique U V
  ⊗₀-repr-lc {F} {U} {V} κ =
    ap (ap fst) (is-contr→is-set (⊗₀-rep-contr U) U V κ
      (is-⊗₀-representable-prop F U V))

  ⊗₀-repr-refl : ∀ {F} {m : C.ob} (p q : ⊗₀-emb m ≡ F)
              → p ≡ q → ⊗₀-repr-unique (m , p) (m , q) ≡ refl
  ⊗₀-repr-refl {F} {m} p q =
    J (λ q' _ → ⊗₀-repr-unique (m , p) (m , q') ≡ refl)
      (sym (⊗₀-repr-lc (refl {x = m , p})))

  ⊗₀-repr-cast : ∀ {F} {m : C.ob} {p q : ⊗₀-emb m ≡ F}
              → (V : is-⊗₀-representable F) → p ≡ q
              → ⊗₀-repr-unique (m , p) V ≡ ⊗₀-repr-unique (m , q) V
  ⊗₀-repr-cast {m = m} V e i = ⊗₀-repr-unique (m , e i) V

  ⊗₀-repr-ap : ∀ {F G} (Ĝ : is-⊗₀-representable F → is-⊗₀-representable G)
              (U V : is-⊗₀-representable F)
            → ⊗₀-repr-unique (Ĝ U) (Ĝ V)
            ≡ ap (λ u → Ĝ u .fst) (is-⊗₀-representable-prop F U V)
  ⊗₀-repr-ap Ĝ U V = sym (⊗₀-repr-lc (λ i → Ĝ (is-⊗₀-representable-prop _ U V i)))

  ⊗₀-repr-∙ : ∀ {F} (U V W : is-⊗₀-representable F)
           → ⊗₀-repr-unique U V ∙ ⊗₀-repr-unique V W ≡ ⊗₀-repr-unique U W
  ⊗₀-repr-∙ {F} U V W =
      sym (ap-comp fst (is-⊗₀-representable-prop F U V)
            (is-⊗₀-representable-prop F V W))
    ∙ ⊗₀-repr-lc
        (is-⊗₀-representable-prop F U V ∙ is-⊗₀-representable-prop F V W)

  _↝_ : ∀ {F G : ⊗₀-composite}
      → is-⊗₀-representable F → F ≡ G → is-⊗₀-representable G
  (m , p) ↝ e = m , p ∙ e

  -- a witness slid along its transport path by the composition
  -- filler: the fst is constant, at m = i0 the slide is the witness
  -- itself (path eta) and at m = i1 the transport U ↝ e (the fill's
  -- lid) — both definitional
  ↝-fill
    : ∀ {F G : ⊗₀-composite}
    → (U : is-⊗₀-representable F) (e : F ≡ G) (m : Core.Base.I)
    → is-⊗₀-representable (e m)
  ↝-fill (m₀ , p) e m = m₀ , λ i → cat.fill p e i m

  -- ↝ preserves fst definitionally, so the slid line's shadow is
  -- the shadow of the slid propositionality path — no transport
  ↝-repr : ∀ {F G} (U V : is-⊗₀-representable F) (e : F ≡ G)
         → ⊗₀-repr-unique (U ↝ e) (V ↝ e) ≡ ⊗₀-repr-unique U V
  ↝-repr {F} U V e = sym (⊗₀-repr-lc (λ i → is-⊗₀-representable-prop F U V i ↝ e))

  ap-⊗₀-emb-lc : ∀ {m n : C.ob} {r s : m ≡ n}
              → ap ⊗₀-emb r ≡ ap ⊗₀-emb s → r ≡ s
  ap-⊗₀-emb-lc {n = n} {r} {s} h =
    total-contr-unique (⊗₀-emb-image-contr n) r s (sq r)
      (subst (λ t → PathP (λ i → ⊗₀-emb (s i) ≡ ⊗₀-emb n) t refl)
        (sym h) (sq s))
    where
      sq : (t : _ ≡ n)
        → PathP (λ i → ⊗₀-emb (t i) ≡ ⊗₀-emb n) (ap ⊗₀-emb t) refl
      sq t i j = ⊗₀-emb (t (i ∨ j))
```

### Associativity

```agda
  -- opaque: consumers only ever transport along this path or read
  -- its boundary off the type; keeping the underlying hcom tower
  -- sealed lets level-1 witness families over it compare as
  -- neutrals instead of normalizing the embedding proof at a
  -- generic interval point
  opaque
    assoc-σ●₀ : ∀ {F G H : ⊗₀-composite}
             → (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
               (W : is-⊗₀-representable H)
             → U ●₀ (V ●₀ W) ≡ (U ●₀ V) ●₀ W
    assoc-σ●₀ U V W = is-⊗₀-representable-prop _ (U ●₀ (V ●₀ W)) ((U ●₀ V) ●₀ W)

  assoc●₀ : ∀ {F G H : ⊗₀-composite}
         → (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
           (W : is-⊗₀-representable H)
         → fst (U ●₀ (V ●₀ W)) ≡ fst ((U ●₀ V) ●₀ W)
  assoc●₀ U V W = ap fst (assoc-σ●₀ U V W)

  ⊗₀-assoc : ∀ x y z → x ⊗₀ (y ⊗₀ z) ≡ (x ⊗₀ y) ⊗₀ z
  ⊗₀-assoc x y z = assoc●₀ (⊗₀-nrm x) (⊗₀-nrm y) (⊗₀-nrm z)
```

### The unitors

The σ-lines transport along `▾₀-idn`/`⊗₀-emb-idn-absorb`, which pass
through the absorptions — so the statement types themselves depend on
the supplied identification, and the unitors come out relative to it
even though their fst-shadow types do not. Whether the two fields'
unitors agree is stated below, not assumed.

```agda
  module unitors
    (ι : (x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y) where

    open over-interchange ι

    opaque
      unitr-σ●₀ : ∀ x → ((⊗₀-nrm x ●₀ ⊗₀-nrm I) ↝ ▾₀-idn (⊗₀-emb x)) ≡ ⊗₀-nrm x
      unitr-σ●₀ x =
        is-⊗₀-representable-prop _
          ((⊗₀-nrm x ●₀ ⊗₀-nrm I) ↝ ▾₀-idn (⊗₀-emb x)) (⊗₀-nrm x)

      unitl-σ●₀ : ∀ x → ((⊗₀-nrm I ●₀ ⊗₀-nrm x) ↝ ⊗₀-emb-idn-absorb x) ≡ ⊗₀-nrm x
      unitl-σ●₀ x =
        is-⊗₀-representable-prop _
          ((⊗₀-nrm I ●₀ ⊗₀-nrm x) ↝ ⊗₀-emb-idn-absorb x) (⊗₀-nrm x)

    ⊗₀-unitr : ∀ x → x ⊗₀ I ≡ x
    ⊗₀-unitr x = ap fst (unitr-σ●₀ x)

    ⊗₀-unitl : ∀ x → I ⊗₀ x ≡ x
    ⊗₀-unitl x = ap fst (unitl-σ●₀ x)
```

## The comparison boundary

The absorption coherence is stated one identification at a time:
`Cat.Depreciated.Monoidal.Legacy.Twist.twist-reduces-to-omega` shows that
demanding it over an identification and its composite with a loop
family forces the loop family to `refl` at unit arguments, so no
single statement covers both fields without trivializing `ω` there.
The agreement types for the unitors are the record's boundary between
derived and contentful: their inhabitation in an instance is exactly
the vanishing of the discrepancy on the unit line, conjectured
equivalent to the `θ I ≡ refl` normalization in derived form.

```agda
  module absorb-coh
    (ι : (x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y) where

    open over-interchange ι

    lhs : (x r : C.ob) → ⊗₀-pre I (⊗₀-pre x r) ≡ ⊗₀-pre x r
    lhs x r = ⊗₀-absorb-l (⊗₀-pre x r)

    rhs : (x r : C.ob) → ⊗₀-pre I (⊗₀-pre x r) ≡ ⊗₀-pre x r
    rhs x r =
        happly (ι I x) (I , r)
      ∙ ap (λ t → ⊗₀-emb x (t , r)) (⊗₀-absorb-r I)

  unitr-agreement : Type o
  unitr-agreement =
    ∀ x → unitors.⊗₀-unitr ι⁺-pt x ≡ unitors.⊗₀-unitr ι⁻-pt x

  unitl-agreement : Type o
  unitl-agreement =
    ∀ x → unitors.⊗₀-unitl ι⁺-pt x ≡ unitors.⊗₀-unitl ι⁻-pt x
```

## Level 1: the displayed context calculus

Carried for the redevelopment of the morphism grade; unchanged from
the archived presentation. A morphism of tensor contexts is a
left-flank map paired with a right-flank map; a `⊗₁-composite` is a
family of homs over all such maps, displayed over a pair of
object-composites. The frames are quantified visibly, as `Cat.Depreciated.Type`
keeps the anonymous endpoints inside the context: a hidden-Π-headed
composite type would have its inhabitants eta-expanded with frame
metas wherever they meet an inference-mode position, while a visible
Π is never expanded. `_$₁_` recovers application with the frames read
off the context argument's type.

```agda
module tensor-virtual₁ {o h} (C : category o h) (I : category.ob C) where
  private module C = category C
  private module Ct = theory C
  open tensor-virtual C I

  ⊗₁-ctx : ⊗₀-ctx → ⊗₀-ctx → Type h
  ⊗₁-ctx (l , r) (l' , r') = C.hom l l' × C.hom r r'

  ⊗₁-ov-idn : C.hom I I
  ⊗₁-ov-idn = C.idn I

  ⊗₁-un-idn : C.hom I I
  ⊗₁-un-idn = C.idn I

  ⊗₁-composite : ⊗₀-composite → ⊗₀-composite → Type (o ⊔ h)
  ⊗₁-composite F F' = ∀ γ γ' → ⊗₁-ctx γ γ' → C.hom (F γ) (F' γ')

  -- application, with the frames read off the context's type
  _$₁_ : ∀ {F F'} → ⊗₁-composite F F'
       → ∀ {γ γ'} → ⊗₁-ctx γ γ' → C.hom (F γ) (F' γ')
  _$₁_ η {γ} {γ'} δ = η γ γ' δ
  infixl 90 _$₁_

  -- evaluation at the identity context
  ⊗₁-ev : ∀ {F F'} → ⊗₁-composite F F' → C.hom (⊗₀-ev F) (⊗₀-ev F')
  ⊗₁-ev η = η $₁ (⊗₁-ov-idn , ⊗₁-un-idn)

  _⊗₁-ctx-⨾_ : ∀ {γ γ' γ''}
             → ⊗₁-ctx γ γ' → ⊗₁-ctx γ' γ'' → ⊗₁-ctx γ γ''
  (α , β) ⊗₁-ctx-⨾ (α' , β') = (α Ct.⨾ α') , (β Ct.⨾ β')
  infixr 40 _⊗₁-ctx-⨾_

  -- the context category's identity, at any frame
  ⊗₁-ctx-idn : ∀ {γ} → ⊗₁-ctx γ γ
  ⊗₁-ctx-idn {γ = (l , r)} = (C.idn l , C.idn r)
```

## The displayed representable layer

```agda
module tensor-representable₁ {o h} (C : category o h) (I : category.ob C)
  (⊗₀-emb : category.ob C → tensor-virtual.⊗₀-composite C I)
  (⊗₁-emb : ∀ {x x'} → category.hom C x x'
          → tensor-virtual₁.⊗₁-composite C I (⊗₀-emb x) (⊗₀-emb x'))
  where

  open tensor-virtual C I
  open tensor-virtual₁ C I
  open tensor-representable C I ⊗₀-emb
  private module C = category C
  private module Ct = theory C

  is-⊗₁-representable : ∀ {x x'} → ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x') → Type (o ⊔ h)
  is-⊗₁-representable = fiber ⊗₁-emb

  _⊨₁_ : ∀ {x x'} → ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x')
       → C.hom x x' → Type (o ⊔ h)
  η ⊨₁ σ = ⊗₁-emb σ ≡ η

  ⊗₁-pre : ∀ {y y'} → C.hom y y' → ∀ {r r'} → C.hom r r'
        → C.hom (⊗₀-pre y r) (⊗₀-pre y' r')
  ⊗₁-pre ψ β = ⊗₁-emb ψ $₁ (⊗₁-ov-idn , β)

  ⊗₁-post : ∀ {x x'} → C.hom x x' → ∀ {l l'} → C.hom l l'
        → C.hom (⊗₀-post x l) (⊗₀-post x' l')
  ⊗₁-post φ α = ⊗₁-emb φ $₁ (α , ⊗₁-un-idn)

  ⊗₁-sub : ∀ {y y'} (ψ : C.hom y y') {γ γ'}
        → ⊗₁-ctx γ γ' → ⊗₁-ctx (⊗₀-sub y γ) (⊗₀-sub y' γ')
  ⊗₁-sub ψ (α , β) = α , ⊗₁-pre ψ β

  ⊗₁-cosub : ∀ {x x'} (φ : C.hom x x') {γ γ'}
          → ⊗₁-ctx γ γ' → ⊗₁-ctx (⊗₀-cosub x γ) (⊗₀-cosub x' γ')
  ⊗₁-cosub φ (α , β) = ⊗₁-post φ α , β

  ⊗₁-nrm : ∀ {x x'} (φ : C.hom x x') → is-⊗₁-representable (⊗₁-emb φ)
  ⊗₁-nrm φ = φ , refl

  -- a displaced witness pairs a hom with the image of a level-0
  -- witness path: ⊗₁-wit U U' η is the fiber of ⊗₁-emb displaced
  -- along the witness paths of U and U'; at ⊗₀-nrm endpoints the
  -- witness paths are constant and ⊗₁-wit-nrm is the plain ⊗₁-nrm
  -- fiber point
  ⊗₁-wit
    : ∀ {F F' : ⊗₀-composite}
    → is-⊗₀-representable F → is-⊗₀-representable F'
    → ⊗₁-composite F F' → Type (o ⊔ h)
  ⊗₁-wit U U' η =
    Σ σ ∶ C.hom (U .fst) (U' .fst) ,
    PathP (λ i → ⊗₁-composite (U .snd i) (U' .snd i)) (⊗₁-emb σ) η

  ⊗₁-wit-nrm
    : ∀ {x x'} (φ : C.hom x x')
    → ⊗₁-wit (⊗₀-nrm x) (⊗₀-nrm x') (⊗₁-emb φ)
  ⊗₁-wit-nrm φ = φ , refl

  _▾₁_ : ∀ {F F' : ⊗₀-composite} {y y'}
       → ⊗₁-composite F F' → C.hom y y'
       → ⊗₁-composite (F ▾₀ y) (F' ▾₀ y')
  (η ▾₁ ψ) γ γ' δ = η $₁ ⊗₁-sub ψ δ
  infixl 30 _▾₁_

  _▴₁_ : ∀ {x x'} {G G' : ⊗₀-composite}
         → C.hom x x' → ⊗₁-composite G G'
         → ⊗₁-composite (x ▴₀ G) (x' ▴₀ G')
  (φ ▴₁ η) γ γ' δ = η $₁ ⊗₁-cosub φ δ
  infixl 30 _▴₁_

  _▿₁_ : ∀ {F F' G G' : ⊗₀-composite}
        → ⊗₁-composite F F' → ⊗₁-composite G G'
        → ⊗₁-composite (F ▿₀ G) (F' ▿₀ G')
  (η ▿₁ ζ) γ γ' (α , β) = η $₁ (α , ζ $₁ (⊗₁-ov-idn , β))
  infixl 30 _▿₁_

  _▵₁_ : ∀ {F F' G G' : ⊗₀-composite}
         → ⊗₁-composite F F' → ⊗₁-composite G G'
         → ⊗₁-composite (F ▵₀ G) (F' ▵₀ G')
  (η ▵₁ ζ) γ γ' (α , β) = ζ $₁ (η $₁ (α , ⊗₁-un-idn) , β)
  infixl 30 _▵₁_

  -- vertical composite of hom-composites, with the second factor
  -- read at the identity frame
  _⨾₁_ : ∀ {F F' F''} → ⊗₁-composite F F' → ⊗₁-composite F' F''
       → ⊗₁-composite F F''
  (η ⨾₁ η') γ γ' δ = η $₁ δ Ct.⨾ η' $₁ ⊗₁-ctx-idn
  infixr 40 _⨾₁_
```

## `monoidal-axioms₁`

The displaced record over a chosen `monoidal-axioms₀`: the displaced
embedding, one displaced interchange field over each of the level-0
fields — each a `PathP` between the ternary orders over its own
level-0 line, taking displaced witnesses so it applies at a generic
interval point of any level-0 witness line — the contractibility of
the displaced pull fiber, stated as `⊗₁-wit` at the level-0 pull
centers, the displaced readback law, and the enrichment law
`⊗₁-emb-⨾`, the one field with no object-level shadow. As at the
object grade, no field relates the two displaced interchange
structures.

```agda
record monoidal-axioms₁ {o h} {C : category o h}
  (M₀ : monoidal-axioms₀ C) : Type₊ (o ⊔ h) where
  open monoidal-axioms₀ M₀
  open tensor-virtual₁ C I public
  private module C = category C
  private module Ct = theory C

  field
    ⊗₁-emb : ∀ {x x'} → C.hom x x' → ⊗₁-composite (⊗₀-emb x) (⊗₀-emb x')

  open tensor-representable₁ C I ⊗₀-emb ⊗₁-emb public

  field
    ι⁺₁ : ∀ {A A' B B' : ⊗₀-composite}
            {U : is-⊗₀-representable A} {U' : is-⊗₀-representable A'}
            {V : is-⊗₀-representable B} {V' : is-⊗₀-representable B'}
            {η : ⊗₁-composite A A'} {ζ : ⊗₁-composite B B'}
        → ⊗₁-wit U U' η → ⊗₁-wit V V' ζ
        → PathP (λ i → ⊗₁-composite (ι⁺ U V i) (ι⁺ U' V' i))
                (η ▿₁ ζ) (η ▵₁ ζ)

    ι⁻₁ : ∀ {A A' B B' : ⊗₀-composite}
            {U : is-⊗₀-representable A} {U' : is-⊗₀-representable A'}
            {V : is-⊗₀-representable B} {V' : is-⊗₀-representable B'}
            {η : ⊗₁-composite A A'} {ζ : ⊗₁-composite B B'}
        → ⊗₁-wit U U' η → ⊗₁-wit V V' ζ
        → PathP (λ i → ⊗₁-composite (ι⁻ U V i) (ι⁻ U' V' i))
                (η ▿₁ ζ) (η ▵₁ ζ)

    ⊗₁-pull-contr
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
      → is-contr (⊗₁-wit (⊗₀-pull-contr x y .center)
                         (⊗₀-pull-contr x' y' .center)
                         (⊗₁-emb φ ▾₁ ψ))

    ⊗₁-unit
      : ∀ {x x'} (φ : C.hom x x')
      → PathP (λ i → C.hom (⊗₀-unit x i) (⊗₀-unit x' i))
              (⊗₁-ev (⊗₁-emb φ)) φ

    ⊗₁-emb-⨾
      : ∀ {x x' x''} (φ₁ : C.hom x x') (φ₂ : C.hom x' x'')
          {γ γ' γ''} (δ₁ : ⊗₁-ctx γ γ') (δ₂ : ⊗₁-ctx γ' γ'')
      → ⊗₁-emb (φ₁ Ct.⨾ φ₂) $₁ (δ₁ ⊗₁-ctx-⨾ δ₂)
      ≡ ⊗₁-emb φ₁ $₁ δ₁ Ct.⨾ ⊗₁-emb φ₂ $₁ δ₂

  ι⁺₁-pt : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
         → PathP (λ i → ⊗₁-composite (ι⁺-pt x y i) (ι⁺-pt x' y' i))
                 (⊗₁-emb φ ▾₁ ψ) (φ ▴₁ ⊗₁-emb ψ)
  ι⁺₁-pt φ ψ = ι⁺₁ (⊗₁-wit-nrm φ) (⊗₁-wit-nrm ψ)

  ι⁻₁-pt : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
         → PathP (λ i → ⊗₁-composite (ι⁻-pt x y i) (ι⁻-pt x' y' i))
                 (⊗₁-emb φ ▾₁ ψ) (φ ▴₁ ⊗₁-emb ψ)
  ι⁻₁-pt φ ψ = ι⁻₁ (⊗₁-wit-nrm φ) (⊗₁-wit-nrm ψ)
```

## `theory₁`

The hom-grade tensor projects from the displaced pull fiber, exactly
as the object-grade tensor projects from its own. The cells consuming
a displaced interchange pair are developed over an arbitrary one; the
displaced tail is the singleton over the line of path types sitting
over the level-0 compatibility square — `spine-tail` is this lemma's
one-dimensional case — so the displaced spine over any pair is again
two library lemmas and a reshaping, with no new Kan filling.

```agda
module theory₁ {o h} {C : category o h} {M₀ : monoidal-axioms₀ C}
  (M₁ : monoidal-axioms₁ M₀) where
  open monoidal-axioms₀ M₀
  open monoidal-axioms₁ M₁
  open theory₀ M₀
  private module C = category C

  _⊗₁_ : ∀ {x x'} → C.hom x x' → ∀ {y y'} → C.hom y y'
       → C.hom (x ⊗₀ y) (x' ⊗₀ y')
  φ ⊗₁ ψ = ⊗₁-pull-contr φ ψ .center .fst
  infixr 40 _⊗₁_

  ⊗₁-emb-comp : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
              → PathP (λ i → ⊗₁-composite (⊗₀-emb-comp x y i)
                                           (⊗₀-emb-comp x' y' i))
                      (⊗₁-emb (φ ⊗₁ ψ)) (⊗₁-emb φ ▾₁ ψ)
  ⊗₁-emb-comp φ ψ = ⊗₁-pull-contr φ ψ .center .snd

  module over-interchange₁
    (ι₀ : (x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y)
    (ι₁ : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        → PathP (λ i → ⊗₁-composite (ι₀ x y i) (ι₀ x' y' i))
                (⊗₁-emb φ ▾₁ ψ) (φ ▴₁ ⊗₁-emb ψ)) where

    open over-interchange ι₀

    private
      tail
        : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
        → is-contr (Σ Q ∶ PathP (λ i → ⊗₁-composite (⊗₀-emb-comp-op x y i)
                                                     (⊗₀-emb-comp-op x' y' i))
                                (⊗₁-emb (φ ⊗₁ ψ)) (φ ▴₁ ⊗₁-emb ψ) ,
            PathP (λ i → PathP (λ j → ⊗₁-composite (⊗₀-emb-comp-coh x y i j)
                                                    (⊗₀-emb-comp-coh x' y' i j))
                               (⊗₁-emb (φ ⊗₁ ψ)) (ι₁ φ ψ i))
                  (⊗₁-emb-comp φ ψ) Q)
      tail {x} {x'} φ {y} {y'} ψ =
        SinglP-contr
          {A = λ i → PathP (λ j → ⊗₁-composite (⊗₀-emb-comp-coh x y i j)
                                                (⊗₀-emb-comp-coh x' y' i j))
                           (⊗₁-emb (φ ⊗₁ ψ)) (ι₁ φ ψ i)}
          (⊗₁-emb-comp φ ψ)

    ⊗₁-emb-comp-op
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
      → PathP (λ i → ⊗₁-composite (⊗₀-emb-comp-op x y i)
                                   (⊗₀-emb-comp-op x' y' i))
              (⊗₁-emb (φ ⊗₁ ψ)) (φ ▴₁ ⊗₁-emb ψ)
    ⊗₁-emb-comp-op φ ψ = tail φ ψ .center .fst

    ⊗₁-emb-comp-coh
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
      → PathP (λ i → PathP (λ j → ⊗₁-composite (⊗₀-emb-comp-coh x y i j)
                                                (⊗₀-emb-comp-coh x' y' i j))
                           (⊗₁-emb (φ ⊗₁ ψ)) (ι₁ φ ψ i))
              (⊗₁-emb-comp φ ψ) (⊗₁-emb-comp-op φ ψ)
    ⊗₁-emb-comp-coh φ ψ = tail φ ψ .center .snd

    ⊗₁-spine-contr
      : ∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
      → is-contr (Σ σ ∶ C.hom (x ⊗₀ y) (x' ⊗₀ y') ,
          Σ P ∶ PathP (λ i → ⊗₁-composite (⊗₀-emb-comp x y i)
                                           (⊗₀-emb-comp x' y' i))
                      (⊗₁-emb σ) (⊗₁-emb φ ▾₁ ψ) ,
          Σ Q ∶ PathP (λ i → ⊗₁-composite (⊗₀-emb-comp-op x y i)
                                           (⊗₀-emb-comp-op x' y' i))
                      (⊗₁-emb σ) (φ ▴₁ ⊗₁-emb ψ) ,
            PathP (λ i → PathP (λ j → ⊗₁-composite (⊗₀-emb-comp-coh x y i j)
                                                    (⊗₀-emb-comp-coh x' y' i j))
                               (⊗₁-emb σ) (ι₁ φ ψ i))
                  P Q)
    ⊗₁-spine-contr {x} {x'} φ {y} {y'} ψ = reshape c
      where
        c = Σ-contr-contr (⊗₁-pull-contr φ ψ)
              λ (σ , P) →
                SinglP-contr
                  {A = λ i → PathP (λ j → ⊗₁-composite (⊗₀-emb-comp-coh x y i j)
                                                        (⊗₀-emb-comp-coh x' y' i j))
                                   (⊗₁-emb σ) (ι₁ φ ψ i)}
                  P

        reshape
          : is-contr (Σ λ (σ , P) →
              Σ Q ∶ PathP (λ i → ⊗₁-composite (⊗₀-emb-comp-op x y i)
                                               (⊗₀-emb-comp-op x' y' i))
                          (⊗₁-emb σ) (φ ▴₁ ⊗₁-emb ψ) ,
                PathP (λ i → PathP (λ j → ⊗₁-composite (⊗₀-emb-comp-coh x y i j)
                                                        (⊗₀-emb-comp-coh x' y' i j))
                                   (⊗₁-emb σ) (ι₁ φ ψ i))
                      P Q)
          → is-contr (Σ σ ∶ C.hom (x ⊗₀ y) (x' ⊗₀ y') ,
              Σ P ∶ PathP (λ i → ⊗₁-composite (⊗₀-emb-comp x y i)
                                               (⊗₀-emb-comp x' y' i))
                          (⊗₁-emb σ) (⊗₁-emb φ ▾₁ ψ) ,
              Σ Q ∶ PathP (λ i → ⊗₁-composite (⊗₀-emb-comp-op x y i)
                                               (⊗₀-emb-comp-op x' y' i))
                          (⊗₁-emb σ) (φ ▴₁ ⊗₁-emb ψ) ,
                PathP (λ i → PathP (λ j → ⊗₁-composite (⊗₀-emb-comp-coh x y i j)
                                                        (⊗₀-emb-comp-coh x' y' i j))
                                   (⊗₁-emb σ) (ι₁ φ ψ i))
                      P Q)
        reshape c' .center =
          c' .center .fst .fst , c' .center .fst .snd ,
          c' .center .snd .fst , c' .center .snd .snd
        reshape c' .paths (σ , P , Q , Θ) i =
          φ' i .fst .fst , φ' i .fst .snd , φ' i .snd .fst , φ' i .snd .snd
          where φ' = c' .paths ((σ , P) , (Q , Θ))
```

## The bundle

Mirroring `category = structure + axioms`.

```agda
record monoidal {o h} (C : category o h) : Type₊ (o ⊔ h) where
  field
    axioms₀ : monoidal-axioms₀ C
    axioms₁ : monoidal-axioms₁ axioms₀

  open monoidal-axioms₀ axioms₀ public
  open monoidal-axioms₁ axioms₁ public
  open theory₀ axioms₀ public
  open theory₁ axioms₁ public
```
