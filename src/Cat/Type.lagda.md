Lane Biocini
July 2026

A formulation of category presented through a representable embedding
`emb` into two-sided *composite* operators.

The records take the name `category`; speaking properly they are
wild categories, types of morphisms never truncated to a set, but
enjoying many nice properties compared to the ordinary definition.

In particular we show that higher coherences arise automatically without
forcing truncation assumptions, and prove that no hidden truncation
assumption obtains.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Type where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Nat
open import Core.Kan
open import Core.Path.Base
open import Core.Transport.Base using (contr-ind; is-prop→PathP)
open import Core.Transport.Properties using (is-contr-is-prop)
open import Core.Transport.J using (J; subst)
open import Core.Equiv.Base using (iso→equiv; _≃_; is-equiv)
open import Core.Function.Embedding
  using (equiv→lc; image-fibers-contr→is-embedding)
```

First we start with the data of a reflexive graph.

```agda
record Rx u v : Type₊ (u ⊔ v) where
  field
    ob : Type u
    edge : ob → ob → Type v
    rx : (x : ob) → edge x x

module virtual-structure {o h} (structure : Rx o h) where
  private module structure = Rx structure

  ob = structure.ob
  hom = structure.edge
  idn = structure.rx
```

`over x = Σ w , hom w x` is a *cofamily-arrow* (cofHom) into `x` (here
an object over `x`).

`ov-idn y = (y , idn y)` is the identity cofamily-arrow — the *center*
in the path instance `over x` is the singleton `Σ w , w ≡ x` and
`ov-idn` is its center of contraction; wild categories posit the
center without the contractibility. It is the universal element the
representable actions read at.

```agda
  over : ob → Type (o ⊔ h)
  over x = Σ w ∶ ob , hom w x

  ov-ctr : ∀ {x y} → hom x y → over y
  ov-ctr {x} f = x , f

  ov-idn : (a : ob) → over a
  ov-idn a = a , idn a
```

`under y = Σ v , hom y v` is a family-arrow (fHom) out of `y`, an
object under `y`. We likewise define a center.

```agda
  under : ob → Type (o ⊔ h)
  under y = Σ v ∶ ob , hom y v

  un-ctr : ∀ {x y} → hom x y → under x
  un-ctr {y} f = y , f

  un-idn : (y : ob) → under y
  un-idn y = y , idn y
```

A context `ctx x y = over x × under y` pairs the two. This bears some
unpacking: the overarrow pins an arrow to x, the underarrow pins an object
out of y, so we're considering two arrows that might factor through an `x -> y`
if the latter exists.



```
  ctx : ob → ob → Type (o ⊔ h)
  ctx x y = over x × under y

  -- the "empty context" in this case are two morphisms that do not share any index
  emp : ∀ {w x y z} → hom w x → hom y z → ctx x y
  emp h k = ov-ctr h , un-ctr k
```

`res γ` is the *result family* over a context. One can think of it in terms
of virtual double categories in a way that ought to be clear in a moment.

Here we fix the type of morphisms that range over the anonymous
witnesses of the over and under parts of the context - allowing us to
more concretely pose the question about what arrows factor in between
the over and under arrows to compose the full arc.

This allows us to formalize the notion of what it means to be a composite: a
composite between two objects is inhabited when any context based at the objects
yields an arc between the anonymous endpoints of the context. This condition must
be total: any context must be suitable as to induce it.

```
  res : ∀ {x y} → ctx x y → Type h
  res γ = hom (γ .fst .fst) (γ .snd .fst)

  composite : ob → ob → Type (o ⊔ h)
  composite x y = (γ : ctx x y) → res γ

  ev : ∀ {x y} → composite x y → hom x y
  ev {x} {y} α = α (ov-idn x , un-idn y)
```

We now require a function which allows us to demonstrate a composite exists
for any hom, i.e. fixing a morphism that given pre and post composable morphisms
always yields an arc between the anonymous endpoints -- at least ostensibly (it ought
to be this one, otherwise, we would have to account for some other morphism qualifying
as a middle factor of the arc).

We then say that a composite is representable when at least one morphism exists
such that it embeds into the composite fixed at its objects. The connection to
VDCs will be direct when we demonstrate that is-representable is a proposition,
and how the type of morphisms fixed at a composite x y admits only one inhabitant
under the total space.

`emb` is the two-sided Yoneda/CPS embedding f ↦ λ(a,b). b∘f∘a.

```agda
record category-axioms {o h} (S : Rx o h) : Type (o ⊔ h) where
  open virtual-structure S

  field
    emb : ∀ {x y} → hom x y → composite x y

  is-representable : ∀ {x y} → composite x y → Type (o ⊔ h)
  is-representable = fiber emb

  _⊨_ : ∀ {x y} → composite x y → hom x y → Type (o ⊔ h)
  α ⊨ s = emb s ≡ α

  ⊨ctr : ∀ {x y} (s : hom x y) → emb s ⊨ s
  ⊨ctr s = refl

  pre : ∀ {y z} (g : hom y z) {v} → hom z v → hom y v
  pre {y} g {v} b = emb g (ov-idn y , un-ctr b)

  post : ∀ {x y} (f : hom x y) {w} → hom w x → hom w y
  post {y = y} f {w} a = emb f (ov-ctr a , un-idn y)

  sub : ∀ {x y z} → hom y z → ctx x z → ctx x y
  sub g (c , (v , b)) = c , (v , pre g b)

  cosub : ∀ {x y z} → hom x y → ctx x z → ctx y z
  cosub g ((w , b) , β) = (w , post g b) , β

  _·_ : ∀ {x y z} → composite x y → hom y z → composite x z
  (α · g) γ = α (sub g γ)
  infixl 30 _·_

  _·ᵒᵖ_ : ∀ {x y z} → hom x y → composite y z → composite x z
  (f ·ᵒᵖ β) γ = β (cosub f γ)

  _·'_ : ∀ {x y z} → composite x y → composite y z → composite x z
  _·'_ {y = y} β α γ = β (γ .fst , (γ .snd .fst , α (ov-idn y , γ .snd)))
  infixl 30 _·'_

  _·''_ : ∀ {x y z} → composite x y → composite y z → composite x z
  _·''_ {y = y} β α γ = α ((γ .fst .fst , β (γ .fst , un-idn y)) , γ .snd)
  infixl 30 _·''_

  field
    interchange♭
      : ∀ {x y z} {A : composite x y} {B : composite y z}
      → is-representable A
      → is-representable B
      → A ·' B ≡ A ·'' B

  nrm : ∀ {x y} (f : hom x y) → is-representable (emb f)
  nrm f = f , refl

  interchange : ∀ {x y z} (f : hom x y) (g : hom y z) → emb f · g ≡ f ·ᵒᵖ emb g
  interchange f g = interchange♭ (nrm f) (nrm g)

  spine : ∀ {x y z} (f : hom x y) (g : hom y z) → Type (o ⊔ h)
  spine f g =
    Σ k ∶ hom _ _ ,
    Σ p ∶ (emb k ≡ emb f · g) ,
    Σ q ∶ (emb k ≡ f ·ᵒᵖ emb g) ,
      PathP (λ i → emb k ≡ interchange f g i) p q

  field
    spine-contr : ∀ {x y z} (f : hom x y) (g : hom y z) → is-contr (spine f g)
    unit        : ∀ {x y} (f : hom x y) → ev (emb f) ≡ f

record category (o h : Level) : Type₊ (o ⊔ h) where
  field
    structure : Rx o h
    axioms    : category-axioms structure

  open virtual-structure structure public
  open category-axioms axioms public

module theory {o h} (C : category o h) where
  open category C

  hom≃total-representable
    : ∀ {x y} → hom x y ≃ (Σ α ∶ composite x y , is-representable α)
  hom≃total-representable {x} {y} = iso→equiv fwd bwd hom-ret rep-sec
    where
      fwd : hom x y → Σ F ∶ composite x y , is-representable F
      fwd f = emb f , (f , refl)

      bwd : (Σ α ∶ composite x y , is-representable α) → hom x y
      bwd (_ , a , _) = a

      hom-ret : ∀ f → bwd (fwd f) ≡ f
      hom-ret f = refl

      rep-sec : ∀ s → fwd (bwd s) ≡ s
      rep-sec (_ , a , p) = J (λ F' p' → fwd a ≡ (F' , a , p')) refl p

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = spine-contr f g .center .fst
  infixr 40 _⨾_

  emb-comp : ∀ {x y z} (f : hom x y) (g : hom y z) → emb (f ⨾ g) ≡ emb f · g
  emb-comp f g = spine-contr f g .center .snd .fst

  emb-comp-op : ∀ {x y z} (f : hom x y) (g : hom y z) → emb (f ⨾ g) ≡ f ·ᵒᵖ emb g
  emb-comp-op  f g = spine-contr f g .center .snd .snd .fst

  _●_ : ∀ {x y z} {A : composite x y} {B : composite y z}
      → is-representable A → is-representable B → is-representable (A ·' B)
  (m , p) ● (n , q) = m ⨾ n , emb-comp m n ∙ (λ i → p i ·' q i)

  _●''_ : ∀ {x y z} {A : composite x y} {B : composite y z}
        → is-representable A → is-representable B → is-representable (A ·'' B)
  (m , p) ●'' (n , q) = m ⨾ n , emb-comp-op m n ∙ (λ i → p i ·'' q i)

  ι-mult-r : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
             (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
           → Type (o ⊔ h)
  ι-mult-r {Cc = Cc} U V W =
    ap (λ X → X ·' Cc) (interchange♭ U V) ≡ interchange♭ U (V ● W)

  ι-mult-l : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
             (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
           → Type (o ⊔ h)
  ι-mult-l {A = A} U V W =
    ap (λ X → A ·'' X) (interchange♭ V W) ≡ interchange♭ (U ●'' V) W

  private
    fwd : ∀ {x y z} (f : hom x y) (g : hom y z) → fiber emb (emb f · g) → spine f g
    fwd f g (h , r) = h , r , r ∙ interchange f g , transpose (cat.fill r (interchange f g))

    bwd : ∀ {x y z} (f : hom x y) (g : hom y z) → fiber emb (f ·ᵒᵖ emb g) → spine f g
    bwd f g (h , r) =
      h , r ∙ sym ι , r , sym (transpose (cat.fill r (sym ι)))
      where ι = interchange f g

  pull-contr : ∀ {x y z} (f : hom x y) (g : hom y z) → is-contr (fiber emb (emb f · g))
  pull-contr f g .center  = f ⨾ g , emb-comp f g
  pull-contr f g .paths u i = φ i .fst , φ i .snd .fst  where
    φ : spine-contr f g .center ≡ fwd f g u
    φ = spine-contr f g .paths (fwd f g u)

  push-contr : ∀ {x y z} (f : hom x y) (g : hom y z) → is-contr (fiber emb (f ·ᵒᵖ emb g))
  push-contr f g .center  = f ⨾ g , emb-comp-op f g
  push-contr f g .paths u i = (φ i .fst) , φ i .snd .snd .fst where
    φ : spine-contr f g .center ≡ bwd f g u
    φ = spine-contr f g .paths (bwd f g u)
```

The following lemmas depend on unit

```
  comp-eq-ev : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾ g ≡ ev (emb f · g)
  comp-eq-ev f g = sym (unit (f ⨾ g)) ∙ ap (λ α → ev α) (emb-comp f g)

  comp-eq-pre : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾ g ≡ pre f g
  comp-eq-pre f g = comp-eq-ev f g ∙ ap (λ t → pre f t) (unit g)

  comp-eq-post : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾ g ≡ post g f
  comp-eq-post f g =
    sym (unit (f ⨾ g)) ∙ ap (λ α → ev α) (emb-comp-op f g) ∙ ap (λ t → post g t) (unit f)

  idem : ∀ {x} → idn x ⨾ idn x ≡ idn x
  idem {x} = comp-eq-pre (idn x) (idn x) ∙ unit (idn x)

  pre-is-post : ∀ {x y z} (f : hom x y) (g : hom y z) → pre f g ≡ post g f
  pre-is-post f g = sym (comp-eq-pre f g) ∙ comp-eq-post f g

  absorb-l : ∀ {x v} (b : hom x v) → pre (idn x) b ≡ b
  absorb-l b = pre-is-post (idn _) b ∙ unit b

  absorb-r : ∀ {w x} (a : hom w x) → post (idn x) a ≡ a
  absorb-r a = sym (pre-is-post a (idn _)) ∙ unit a

  idn-·ᵒᵖ : ∀ {x y} (β : composite x y) → idn x ·ᵒᵖ β ≡ β
  idn-·ᵒᵖ β = funext λ γ →
    ap (λ α → β (α , γ .snd)) (ap (γ .fst .fst ,_) (absorb-r (γ .fst .snd)))

  emb-image-contr : ∀ {x y} (f : hom x y) → is-contr (fiber emb (emb f))
  emb-image-contr {x} f =
    subst (λ α → is-contr (fiber emb α)) (idn-·ᵒᵖ (emb f)) (push-contr (idn x) f)

  ·-idn : ∀ {x y} (α : composite x y) → α · idn y ≡ α
  ·-idn α = funext λ γ →
    ap (λ β → α (γ .fst , β)) (ap (γ .snd .fst ,_) (absorb-l (γ .snd .snd)))

  emb-idn-absorb : ∀ {x y} (f : hom x y) → emb (idn x) · f ≡ emb f
  emb-idn-absorb {x} f = interchange (idn x) f ∙ idn-·ᵒᵖ (emb f)

  emb-post
    : ∀ {x y} (f : hom x y) {w} (a : hom w x) {v} (b : hom y v)
    → emb f ((w , a) , (v , b)) ≡ emb (idn y) ((w , post f a) , (v , b))
  emb-post {x} {y} f {w} a {v} b =
    ap (λ b' → emb f ((w , a) , (v , b'))) (sym (absorb-l b))
    ∙ λ i → interchange f (idn y) i (emp a b)

  emb-normal : ∀ {x y} (f : hom x y) {w} (a : hom w x) {v} (b : hom y v)
             → emb f (ov-ctr a , un-ctr b) ≡ post b (post f a)
  emb-normal {x} {y} f {w} a {v} b =
    emb-post f a b
    ∙ ap (λ b' → emb (idn y) ((w , post f a) , (v , b'))) (sym (unit b))
    ∙ (λ i → interchange (idn y) b i ((w , post f a) , un-idn v))
    ∙ ap (post b) (absorb-r (post f a))

  pre-distr : ∀ {x y z} (f : hom x y) (g : hom y z) {v} (b : hom z v)
            → pre (f ⨾ g) b ≡ pre f (pre g b)
  pre-distr {x} f g b = happly (emb-comp f g) (ov-idn x , un-ctr b)

  post-distr : ∀ {x y z} (f : hom x y) (g : hom y z) {w} (a : hom w x)
             → post (f ⨾ g) a ≡ post g (post f a)
  post-distr {z = z} f g a = happly (emb-comp-op f g) (ov-ctr a , un-idn z)



  is-representable-prop : ∀ {x y} (α : composite x y) → is-prop (is-representable α)
  is-representable-prop = image-fibers-contr→is-embedding emb-image-contr

  rep-contr : ∀ {x y} {α : composite x y} → is-representable α → is-contr (is-representable α)
  rep-contr {α = α} u .center = u
  rep-contr {α = α} u .paths  = is-representable-prop α u

  ●-coh : ∀ {x y z} {A : composite x y} {B : composite y z}
          (U : is-representable A) (V : is-representable B)
        → PathP (λ i → is-representable (interchange♭ U V i)) (U ● V) (U ●'' V)
  ●-coh U V = is-prop→PathP (λ i → is-representable-prop (interchange♭ U V i)) (U ● V) (U ●'' V)

  interchange-natural                                           -- was ι-comm
    : ∀ {x y z w} {A : composite x y} {B : composite y z} {Cc : composite z w}
      (U : is-representable A) (V : is-representable B) (W : is-representable Cc)
    → ap (λ X → X ·' Cc) (interchange♭ U V) ∙ interchange♭ (U ●'' V) W
    ≡ interchange♭ (U ● V) W ∙ ap (λ X → X ·'' Cc) (interchange♭ U V)
  interchange-natural {Cc = Cc} U V W =
    Path.commutes
      (ap (λ X → X ·' Cc) (interchange♭ U V)) (interchange♭ (U ●'' V) W)
      (interchange♭ (U ● V) W) (ap (λ X → X ·'' Cc) (interchange♭ U V))
      (λ j i → interchange♭ (●-coh U V i) W j)



  -- to prove P of all representations of α, prove it of the one you hold
  -- rind : ∀ {u} {x y} {α : composite x y} (U : is-representable α)
  --        (P : (s : hom x y) → α => s → Type u)
  --      → P (U .fst) (U .snd)
  --      → ∀ {s} (p : α => s) → P s p
  -- rind U P base {s} p = contr-ind (rep-contr U) (λ V → P (V .fst) (V .snd)) base (s , p)

  -- cast : ∀ {x y} {α : composite x y} (U : is-representable α) {s} → α => s → U .fst ≡ s
  -- cast U = rind U (λ s _ → U .fst ≡ s) refl

  ⟨_,_⟩ : ∀ {x y} {α : composite x y} (u v : is-representable α) → u .fst ≡ v .fst
  ⟨_,_⟩ {α = α} u v = ap fst (is-representable-prop α u v)



  module _ where
  _⨾_=>_ : ∀ {x y z} → hom x y → hom y z → hom x z → Type (o ⊔ h)
  _⨾_=>_ {x} {y} {z} f g s = emb f · g ≡ emb s

  fst-lc : ∀ {x y} {α : composite x y} {U V : is-representable α}
         → (κ : U ≡ V) → ap fst κ ≡ ⟨ U , V ⟩
  fst-lc {α = α} {U} {V} κ =
    ap (ap fst) (is-contr→is-set (rep-contr U) U V κ (is-representable-prop α U V))

  ⟨⟩-refl : ∀ {x y} {α : composite x y} {m : hom x y} (p q : emb m ≡ α)
          → p ≡ q → ⟨ (m , p) , (m , q) ⟩ ≡ refl
  ⟨⟩-refl {α} {m} p q =
    J (λ q' _ → ⟨ (m , p) , (m , q') ⟩ ≡ refl) (sym (fst-lc (refl {x = m , p})))

  -- theory material, next to ⟨⟩-refl
  ⟨⟩-cast
    : ∀ {x y} {α : composite x y} {m : hom x y} {p q : emb m ≡ α}
      (V : is-representable α) → p ≡ q → ⟨ (m , p) , V ⟩ ≡ ⟨ (m , q) , V ⟩
  ⟨⟩-cast {m = m} V e i = ⟨ (m , e i) , V ⟩

  ⟨⟩-ap : ∀ {x y x' y'} {α : composite x y} {β : composite x' y'}
          (Ĝ : is-representable α → is-representable β) (U V : is-representable α)
        → ⟨ Ĝ U , Ĝ V ⟩ ≡ ap (λ u → Ĝ u .fst) (is-representable-prop α U V)
  ⟨⟩-ap Ĝ U V = sym (fst-lc (λ i → Ĝ (is-representable-prop _ U V i)))

  ⟨⟩-∙ : ∀ {x y} {α : composite x y} (U V W : is-representable α)
       → ⟨ U , V ⟩ ∙ ⟨ V , W ⟩ ≡ ⟨ U , W ⟩
  ⟨⟩-∙ {α = α} U V W =
      sym (ap-comp fst (is-representable-prop α U V) (is-representable-prop α V W))
    ∙ fst-lc (is-representable-prop α U V ∙ is-representable-prop α V W)

  _⊳_ : ∀ {x y} {A B : composite x y} → is-representable A → A ≡ B → is-representable B
  (m , p) ⊳ e = m , p ∙ e

  ⊳-⟨⟩ : ∀ {x y} {α β : composite x y} (U V : is-representable α) (e : α ≡ β)
       → ⟨ U ⊳ e , V ⊳ e ⟩ ≡ ⟨ U , V ⟩
  ⊳-⟨⟩ (m , p) (n , q) =
    J (λ _ e' → ⟨ (m , p) ⊳ e' , (n , q) ⊳ e' ⟩ ≡ ⟨ (m , p) , (n , q) ⟩)
      (λ i → ⟨ (m , Path.unitr p i) , (n , Path.unitr q i) ⟩)

  rep-unique : ∀ {x y} {α : composite x y} {f g : hom x y} → emb f ≡ α → emb g ≡ α → f ≡ g
  rep-unique {α = α} p q = ap fst (is-representable-prop α (_ , p) (_ , q))

  ap-emb-lc : ∀ {x y} {m n : hom x y} {r s : m ≡ n} → ap emb r ≡ ap emb s → r ≡ s
  ap-emb-lc {n = n} {r} {s} h =
    total-contr-unique (emb-image-contr n) r s (sq r)
      (subst (λ t → PathP (λ i → emb (s i) ≡ emb n) t refl) (sym h) (sq s))
    where sq : (t : _ ≡ n) → PathP (λ i → emb (t i) ≡ emb n) (ap emb t) refl
          sq t i j = emb (t (i ∨ j))

  emb-comp-coh
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → PathP
        (λ i → emb (f ⨾ g) ≡ interchange f g i)
        (emb-comp f g)
        (emb-comp-op f g)
  emb-comp-coh f g = spine-contr f g .center .snd .snd .snd

  coh→∙ : ∀ {x y z} (f : hom x y) (g : hom y z)
        → emb-comp f g ∙ interchange f g ≡ emb-comp-op f g
  coh→∙ f g =
      Path.commutes (emb-comp f g) (interchange f g) refl (emb-comp-op f g) (emb-comp-coh f g)
    ∙ Path.unitl (emb-comp-op f g)
```

Associativity can be recovered through the strictness of composite composition

```

  ·-comp : ∀ {x y z w} (α : composite x y) (g : hom y z) (h : hom z w)
         → α · (g ⨾ h) ≡ (α · g) · h
  ·-comp α g h = ap (α ·'_) (emb-comp g h)

  E₃ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w) → composite x w
  E₃ f g h = emb f · g · h

  data 𝓔 {x} : Nat → ∀ {y z} → hom x y → hom y z → Type (o ⊔ h) where
    root : 𝓔 Z (idn x) (idn x)
    ext  : ∀ {n y z w} {s : hom x y} {g : hom y z}
         → 𝓔 n s g → (h : hom z w)
         → 𝓔 (S n) (s ⨾ g) h



  assoc-σ● : ∀ {w x y z} {A : composite w x} {B : composite x y} {C : composite y z}
           → (U : is-representable A) (V : is-representable B) (W : is-representable C)
           → U ● (V ● W) ≡ (U ● V) ● W
  assoc-σ● U V W = is-representable-prop _ (U ● (V ● W)) ((U ● V) ● W)

  assoc● : ∀ {w x y z} {A : composite w x} {B : composite x y} {C : composite y z}
         → (U : is-representable A) (V : is-representable B) (W : is-representable C)
         → fst (U ● (V ● W)) ≡ fst ((U ● V) ● W)
  assoc● U V W = ap fst (assoc-σ● U V W)

  assoc : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
        → f ⨾ (g ⨾ h) ≡ (f ⨾ g) ⨾ h
  assoc f g h = assoc● (nrm f) (nrm g) (nrm h)

  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn y ≡ f
  unitr f = ⟨ (nrm f ● nrm (idn _)) ⊳ ·-idn (emb f) , nrm f ⟩

  unitl : ∀ {x y} (f : hom x y) → idn x ⨾ f ≡ f
  unitl f = ⟨ (nrm (idn _) ● nrm f) ⊳ emb-idn-absorb f , nrm f ⟩

opᴿ : ∀ {o h} → Rx o h → Rx o h
opᴿ structure .Rx.ob       = structure .Rx.ob
opᴿ structure .Rx.edge x y = structure .Rx.edge y x
opᴿ structure .Rx.rx       = structure .Rx.rx

module op {o h} (C : category o h) where
  open category C
  module V  = virtual-structure structure
  module Vᵒ = virtual-structure (opᴿ structure)
  module A  = category-axioms axioms

  σ  : ∀ {x y} → Vᵒ.ctx x y → V.ctx y x  ;  σ  γ = γ .snd , γ .fst
  σ' : ∀ {x y} → V.ctx y x → Vᵒ.ctx x y  ;  σ' δ = δ .snd , δ .fst

  ⟲ : ∀ {x y} → V.composite y x → Vᵒ.composite x y  ;  ⟲ F γ = F (σ γ)
  ⟳ : ∀ {x y} → Vᵒ.composite x y → V.composite y x  ;  ⟳ G δ = G (σ' δ)

  -- both by Σ-η + function η
  ⟲⟳ : ∀ {x y} (G : Vᵒ.composite x y) → ⟲ (⟳ G) ≡ G  ;  ⟲⟳ _ = refl
  ⟳⟲ : ∀ {x y} (F : V.composite y x) → ⟳ (⟲ F) ≡ F  ;  ⟳⟲ _ = refl

  Spineᵒ : ∀ {x y z} (f : Vᵒ.hom x y) (g : Vᵒ.hom y z) → Type (o ⊔ h)
  Spineᵒ {x} {z = z} f g =
    Σ k ∶ Vᵒ.hom x z ,
    Σ p ∶ (⟲ (A.emb k) ≡ ⟲ (g A.·ᵒᵖ A.emb f)) ,
    Σ q ∶ (⟲ (A.emb k) ≡ ⟲ (A.emb g A.· f)) ,
      PathP (λ i → ⟲ (A.emb k) ≡ ap ⟲ (sym (A.interchange g f)) i) p q

  to  : ∀ {x y z} {f : Vᵒ.hom x y} {g : Vᵒ.hom y z} → A.spine g f → Spineᵒ f g
  to  (k , p , q , θ) = k , ap ⟲ q , ap ⟲ p , λ i j → ⟲ (θ (~ i) j)

  fro : ∀ {x y z} {f : Vᵒ.hom x y} {g : Vᵒ.hom y z} → Spineᵒ f g → A.spine g f
  fro (k , p , q , θ) = k , ap ⟳ q , ap ⟳ p , λ i j → ⟳ (θ (~ i) j)

  op-axioms : category-axioms (opᴿ structure)
  op-axioms .category-axioms.emb f = ⟲ (A.emb f)
  op-axioms .category-axioms.interchange♭ (m , p) (n , q) =
    ap ⟲ (sym (A.interchange♭ (n , ap ⟳ q) (m , ap ⟳ p)))
  op-axioms .category-axioms.spine-contr f g .center = to (A.spine-contr g f .center)
  op-axioms .category-axioms.spine-contr f g .paths t = ap to (A.spine-contr g f .paths (fro t))
  op-axioms .category-axioms.unit f = A.unit f


op : ∀ {o h} → category o h → category o h
op C .category.structure = opᴿ (C .category.structure)
op C .category.axioms    = op.op-axioms C

op-invol : ∀ {o h} (C : category o h) → op (op C) ≡ C
op-invol C = refl
