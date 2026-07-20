Lane Biocini
July 2026

The derived theory of a `Cat.Type` category.

The contractible spine makes `emb` an embedding with propositional
fibers, so `hom x y` is equivalent to the total space of
representable composites. Composition `_⨾_` is extracted from the
spine's center, and associativity and the unit laws are theorems
rather than axioms.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.J using (J; subst)
open import Core.Equiv.Base using (iso→equiv; _≃_)
open import Core.Function.Embedding using (image-fibers-contr→is-embedding)

open import Cat.Type

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

  emb-comp : ∀ {x y z} (f : hom x y) (g : hom y z) → emb (f ⨾ g) ≡ emb f ▾ g
  emb-comp f g = spine-contr f g .center .snd .fst

  emb-comp-op : ∀ {x y z} (f : hom x y) (g : hom y z) → emb (f ⨾ g) ≡ f ▴ emb g
  emb-comp-op  f g = spine-contr f g .center .snd .snd .fst

  _●_ : ∀ {x y z} {A : composite x y} {B : composite y z}
      → is-representable A → is-representable B → is-representable (A ▿ B)
  (m , p) ● (n , q) = m ⨾ n , emb-comp m n ∙ (λ i → p i ▿ q i)

  _○_ : ∀ {x y z} {A : composite x y} {B : composite y z}
        → is-representable A → is-representable B → is-representable (A ▵ B)
  (m , p) ○ (n , q) = m ⨾ n , emb-comp-op m n ∙ (λ i → p i ▵ q i)

  private
    fwd : ∀ {x y z} (f : hom x y) (g : hom y z) → fiber emb (emb f ▾ g) → spine f g
    fwd f g (h , r) = h , r , r ∙ interchange f g , transpose (cat.fill r (interchange f g))

    bwd : ∀ {x y z} (f : hom x y) (g : hom y z) → fiber emb (f ▴ emb g) → spine f g
    bwd f g (h , r) =
      h , r ∙ sym ι , r , sym (transpose (cat.fill r (sym ι)))
      where ι = interchange f g

  pull-contr : ∀ {x y z} (f : hom x y) (g : hom y z) → is-contr (fiber emb (emb f ▾ g))
  pull-contr f g .center  = f ⨾ g , emb-comp f g
  pull-contr f g .paths u i = φ i .fst , φ i .snd .fst  where
    φ : spine-contr f g .center ≡ fwd f g u
    φ = spine-contr f g .paths (fwd f g u)

  push-contr : ∀ {x y z} (f : hom x y) (g : hom y z) → is-contr (fiber emb (f ▴ emb g))
  push-contr f g .center  = f ⨾ g , emb-comp-op f g
  push-contr f g .paths u i = (φ i .fst) , φ i .snd .snd .fst where
    φ : spine-contr f g .center ≡ bwd f g u
    φ = spine-contr f g .paths (bwd f g u)

  -- a composite witness: s represents the two-sided composite of f and g
  _⨾_=>_ : ∀ {x y z} → hom x y → hom y z → hom x z → Type (o ⊔ h)
  _⨾_=>_ f g s = (emb f ▾ g) ⊨ s

  cast-path
    : ∀ {x y z} {f : hom x y} {g : hom y z} {s : hom x z}
    → f ⨾ g => s → f ⨾ g ≡ s
  cast-path {f = f} {g} {s} α =
    ap fst (pull-contr f g .paths (s , α))

  cast-path⁻¹
    : ∀ {x y z} {f : hom x y} {g : hom y z} {s : hom x z}
    → f ⨾ g ≡ s → f ⨾ g => s
  cast-path⁻¹ {f = f} {g} {s} p =
    ap emb (sym p) ∙ emb-comp f g
```

The following lemmas depend on unit

```
  comp-eq-ev : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾ g ≡ ev (emb f ▾ g)
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

  idn-▴ : ∀ {x y} (β : composite x y) → idn x ▴ β ≡ β
  idn-▴ β = funext λ γ →
    ap (λ α → β (α , γ .snd)) (ap (γ .fst .fst ,_) (absorb-r (γ .fst .snd)))

  emb-image-contr : ∀ {x y} (f : hom x y) → is-contr (fiber emb (emb f))
  emb-image-contr {x} f =
    subst (λ α → is-contr (fiber emb α)) (idn-▴ (emb f)) (push-contr (idn x) f)

  ▾-idn : ∀ {x y} (α : composite x y) → α ▾ idn y ≡ α
  ▾-idn α = funext λ γ →
    ap (λ β → α (γ .fst , β)) (ap (γ .snd .fst ,_) (absorb-l (γ .snd .snd)))

  emb-idn-absorb : ∀ {x y} (f : hom x y) → emb (idn x) ▾ f ≡ emb f
  emb-idn-absorb {x} f = interchange (idn x) f ∙ idn-▴ (emb f)

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

  repr-unique : ∀ {x y} {α : composite x y} (u v : is-representable α) → u .fst ≡ v .fst
  repr-unique {α = α} u v = ap fst (is-representable-prop α u v)

  repr-lc : ∀ {x y} {α : composite x y} {U V : is-representable α}
          → (κ : U ≡ V) → ap fst κ ≡ repr-unique U V
  repr-lc {α = α} {U} {V} κ =
    ap (ap fst) (is-contr→is-set (rep-contr U) U V κ (is-representable-prop α U V))

  repr-refl : ∀ {x y} {α : composite x y} {m : hom x y} (p q : emb m ≡ α)
            → p ≡ q → repr-unique (m , p) (m , q) ≡ refl
  repr-refl {α} {m} p q =
    J (λ q' _ → repr-unique (m , p) (m , q') ≡ refl) (sym (repr-lc (refl {x = m , p})))

  repr-cast
    : ∀ {x y} {α : composite x y} {m : hom x y} {p q : emb m ≡ α}
      (V : is-representable α) → p ≡ q → repr-unique (m , p) V ≡ repr-unique (m , q) V
  repr-cast {m = m} V e i = repr-unique (m , e i) V

  repr-ap : ∀ {x y x' y'} {α : composite x y} {β : composite x' y'}
            (Ĝ : is-representable α → is-representable β) (U V : is-representable α)
          → repr-unique (Ĝ U) (Ĝ V) ≡ ap (λ u → Ĝ u .fst) (is-representable-prop α U V)
  repr-ap Ĝ U V = sym (repr-lc (λ i → Ĝ (is-representable-prop _ U V i)))

  repr-∙ : ∀ {x y} {α : composite x y} (U V W : is-representable α)
         → repr-unique U V ∙ repr-unique V W ≡ repr-unique U W
  repr-∙ {α = α} U V W =
      sym (ap-comp fst (is-representable-prop α U V) (is-representable-prop α V W))
    ∙ repr-lc (is-representable-prop α U V ∙ is-representable-prop α V W)

  _↝_ : ∀ {x y} {A B : composite x y} → is-representable A → A ≡ B → is-representable B
  (m , p) ↝ e = m , p ∙ e

  -- a witness slid along its transport path by the composition
  -- filler: the fst is constant, at m = i0 the slide is the witness
  -- itself (path eta) and at m = i1 the transport U ↝ e (the fill's
  -- lid) — both definitional, so a calculus projection applied along
  -- the slide is a straightening square with strict endpoints, and
  -- its displaced mate is the same slide one level up
  ↝-fill
    : ∀ {x y} {A B : composite x y}
    → (U : is-representable A) (e : A ≡ B) (m : I)
    → is-representable (e m)
  ↝-fill (m₀ , p) e m = m₀ , λ i → cat.fill p e i m

  ↝-repr : ∀ {x y} {α β : composite x y} (U V : is-representable α) (e : α ≡ β)
         → repr-unique (U ↝ e) (V ↝ e) ≡ repr-unique U V
  ↝-repr (m , p) (n , q) =
    J (λ _ e' → repr-unique ((m , p) ↝ e') ((n , q) ↝ e') ≡ repr-unique (m , p) (n , q))
      (λ i → repr-unique (m , Path.unitr p i) (n , Path.unitr q i))

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

  ▾-comp : ∀ {x y z w} (α : composite x y) (g : hom y z) (h : hom z w)
         → α ▾ (g ⨾ h) ≡ (α ▾ g) ▾ h
  ▾-comp α g h = ap (α ▿_) (emb-comp g h)

  -- opaque: consumers' families project its slices at generic
  -- interval points, and the sealed head keeps those comparisons
  -- syntactic; the boundary still reduces by the type-directed rule
  opaque
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

  -- the unitor σ-lines, sealed like assoc-σ●: consumers read the
  -- boundary off the type, and witness families over these lines
  -- compare as neutrals; the unitors are their fst-shadows
  opaque
    unitr-σ● : ∀ {x y} (f : hom x y)
             → ((nrm f ● nrm (idn y)) ↝ ▾-idn (emb f)) ≡ nrm f
    unitr-σ● f =
      is-representable-prop _
        ((nrm f ● nrm (idn _)) ↝ ▾-idn (emb f)) (nrm f)

    unitl-σ● : ∀ {x y} (f : hom x y)
             → ((nrm (idn x) ● nrm f) ↝ emb-idn-absorb f) ≡ nrm f
    unitl-σ● f =
      is-representable-prop _
        ((nrm (idn _) ● nrm f) ↝ emb-idn-absorb f) (nrm f)

  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn y ≡ f
  unitr f = ap fst (unitr-σ● f)

  unitl : ∀ {x y} (f : hom x y) → idn x ⨾ f ≡ f
  unitl f = ap fst (unitl-σ● f)
```
