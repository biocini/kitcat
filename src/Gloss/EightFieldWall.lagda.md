Gloss: machine-checked evidence for T11 in docs/theorems.md.
Self-contained modulo Core.*; Cat.* definitions frozen at 9133396.

Spike: the ruled 8-field `hcategory-axioms₈` — the five base fields
plus the three coherence cells (`absorb-lcoh`, `absorb-rcoh`,
`couple-D₀`) — with the full op story (Route-B `compose-contrᵒ`, the
θ bridges, the discharge of the three cells, and `op-invol`). Tracked
Gloss evidence (T11). Gate-by-gate validation of Lane's design.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Gloss.EightFieldWall where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
  using (is-contr→is-prop; is-contr→is-set; _∙_; module Path)
open import Core.Transport.J using (J; subst)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Transport.Properties using (is-contr-is-prop; is-prop→is-set)
open import Core.Equiv.Base using (iso→equiv; _≃_; is-equiv)
open import Core.Function.Embedding
  using ( equiv→lc; equiv→lc-section
        ; is-embedding→ap-equiv; is-equiv→is-embedding
        ; image-fibers-contr→is-embedding )
open import Core.HLevel.Base using (retract→is-hlevel)
open import Core.Coherence.Base using (coh-project; coh-project₃)
open import Core.Path.Base using (ap-comp)
open import Core.Data.Nat.Type using (Z)
open import Core.Data.Sigma.Base using (swap)
```

## Frozen `Cat.Codep.Base` definitions

Verbatim copies of the `Cat.Codep.Base` structure record, coupling
provenance lemmas, and five-field axioms record (the bundle is not
needed — this file bundles its own `hcategory₈`). Self-contained
modulo `Core.*`; the live `Cat.*` sources may change, this may not.

```agda
-- Frozen from Cat.Codep.Base @ 9133396 (Gloss certificates inline
-- Cat.* definitions — the library may change; this evidence may not).
record hcategory-structure {o h} (ob : Type o) : Type (o ⊔ h ₊) where
  no-eta-equality
  field
    hom : ob → ob → Type h
    idn : (x : ob) → hom x x

  cofam : ob → Type (o ⊔ h)
  cofam x = Σ w ∶ ob , hom w x

  fam : ob → Type (o ⊔ h)
  fam y = Σ v ∶ ob , hom y v

  ctr : (y : ob) → cofam y
  ctr y = y , idn y

  ctx : ob → ob → Type (o ⊔ h)
  ctx x y = cofam x × fam y

  res : ∀ {x y} → ctx x y → Type h
  res γ = hom (γ .fst .fst) (γ .snd .fst)

  composite : ob → ob → Type (o ⊔ h)
  composite x y = (γ : ctx x y) → res γ

  field
    emb : ∀ {x y} → hom x y → composite x y

  -- The tightness predicate: a composite is representable when an
  -- `emb`-image.
  is-representable : ∀ {x y} → composite x y → Type (o ⊔ h)
  is-representable F = fiber emb F

  -- `pre g b` reads `emb g` with `b` in the family slot — the
  -- composite idn ; g ; b, `g` in the pre position: the action of
  -- `g` precomposing on `b`. `post f a` reads `emb f` with `a` in
  -- the cofamily slot — a ; f ; idn, `f` in the post position: the
  -- action of `f` postcomposing on `a`.
  pre : ∀ {y z} (g : hom y z) {v} → hom z v → hom y v
  pre {y} g {v} b = emb g (ctr y , (v , b))

  post : ∀ {x y} (f : hom x y) {w} → hom w x → hom w y
  post {x} {y} f {w} a = emb f ((w , a) , (y , idn y))

  sub : ∀ {x y z} → hom y z → ctx x z → ctx x y
  sub g (c , (v , b)) = c , (v , pre g b)

  _·_ : ∀ {x y z} → composite x y → hom y z → composite x z
  (F · g) γ = F (sub g γ)
  infixl 30 _·_

  -- `hom` ≃ the total space of the `emb`-fibers, unconditionally (the
  -- subtype reading needs `is-representable-prop`).
  hom≃representable
    : ∀ {x y} → hom x y ≃ (Σ F ∶ composite x y , is-representable F)
  hom≃representable {x} {y} = iso→equiv fwd bwd hom-ret rep-sec
    where
      fwd : hom x y → Σ F ∶ composite x y , is-representable F
      fwd f = emb f , (f , refl)

      bwd : (Σ F ∶ composite x y , is-representable F) → hom x y
      bwd (F , a , p) = a

      hom-ret : ∀ f → bwd (fwd f) ≡ f
      hom-ret f = refl

      rep-sec : ∀ s → fwd (bwd s) ≡ s
      rep-sec (F , a , p) = J (λ F' p' → fwd a ≡ (F' , a , p')) refl p

post-comp-from-coupling
  : ∀ {o h} {ob : Type o} (S : hcategory-structure {o} {h} ob)
    (open hcategory-structure S)
    (cc : ∀ {x y z} (f : hom x y) (g : hom y z)
        → is-contr (is-representable (emb f · g)))
    (ic : ∀ {x y z} (f : hom x y) (g : hom y z)
          {w} (a : hom w x) {v} (b : hom z v)
        → emb f ((w , a) , (v , pre g b)) ≡ emb g ((w , post f a) , (v , b)))
  → ∀ {x y z} (f : hom x y) (g : hom y z) {w} (a : hom w x)
  → post (cc f g .center .fst) a ≡ post g (post f a)
post-comp-from-coupling S cc ic {x} {y} {z} f g {w} a =
  happly (cc f g .center .snd) ((w , a) , (z , idn z))
  ∙ ic f g a (idn z)
  where open hcategory-structure S

comp-eq-from-coupling
  : ∀ {o h} {ob : Type o} (S : hcategory-structure {o} {h} ob)
    (open hcategory-structure S)
    (cc : ∀ {x y z} (f : hom x y) (g : hom y z)
        → is-contr (is-representable (emb f · g)))
    (ic : ∀ {x y z} (f : hom x y) (g : hom y z)
          {w} (a : hom w x) {v} (b : hom z v)
        → emb f ((w , a) , (v , pre g b)) ≡ emb g ((w , post f a) , (v , b)))
    (pe : ∀ {x y} (f : hom x y) → post f (idn x) ≡ f)
  → ∀ {x y z} (f : hom x y) (g : hom y z)
  → cc f g .center .fst ≡ post g f
comp-eq-from-coupling S cc ic pe f g =
  sym (pe (cc f g .center .fst))
  ∙ post-comp-from-coupling S cc ic f g (idn _)
  ∙ ap (λ t → post g t) (pe f)
  where open hcategory-structure S

idem-from-coupling
  : ∀ {o h} {ob : Type o} (S : hcategory-structure {o} {h} ob)
    (open hcategory-structure S)
    (cc : ∀ {x y z} (f : hom x y) (g : hom y z)
        → is-contr (is-representable (emb f · g)))
    (ic : ∀ {x y z} (f : hom x y) (g : hom y z)
          {w} (a : hom w x) {v} (b : hom z v)
        → emb f ((w , a) , (v , pre g b)) ≡ emb g ((w , post f a) , (v , b)))
    (pe : ∀ {x y} (f : hom x y) → post f (idn x) ≡ f)
  → ∀ {x} → cc (idn x) (idn x) .center .fst ≡ idn x
idem-from-coupling S cc ic pe {x} =
  comp-eq-from-coupling S cc ic pe (idn x) (idn x) ∙ pe (idn x)
  where open hcategory-structure S

record hcategory-axioms {o h} {ob : Type o}
  (S : hcategory-structure {o} {h} ob) : Type (o ⊔ h) where
  no-eta-equality
  open hcategory-structure S

  field
    compose-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (is-representable (emb f · g))
    interchange
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        {w} (a : hom w x) {v} (b : hom z v)
      → emb f ((w , a) , (v , pre g b))
      ≡ emb g ((w , post f a) , (v , b))
    post-eval
      : ∀ {x y} (f : hom x y) → post f (idn x) ≡ f
    unit-eqvl : ∀ {x} {v} → is-equiv (pre (idn x) {v})
    unit-eqvr : ∀ {x} {w} → is-equiv (post (idn x) {w})

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = compose-contr f g .center .fst
  infixr 40 _⨾_

  emb-comp : ∀ {x y z} (f : hom x y) (g : hom y z)
           → emb (f ⨾ g) ≡ emb f · g
  emb-comp f g = compose-contr f g .center .snd

  -- pre-comp is emb-comp read at the center — free (a happly), (fam₂).
  pre-comp : ∀ {y z w} (g : hom y z) (h : hom z w) {v} (b : hom w v)
           → pre (g ⨾ h) b ≡ pre g (pre h b)
  pre-comp {y} g h {v} b = happly (emb-comp g h) (ctr y , (v , b))

  sub-comp : ∀ {x y z w} (g : hom y z) (h : hom z w)
           → sub {x} (g ⨾ h) ≡ sub g ∘ sub h
  sub-comp g h = funext λ γ →
    ap (γ .fst ,_) (ap (γ .snd .fst ,_) (pre-comp g h (γ .snd .snd)))

  ·-comp : ∀ {x y z w} (F : composite x y) (g : hom y z) (h : hom z w)
         → F · (g ⨾ h) ≡ F · g · h
  ·-comp F g h = funext λ γ → ap F (happly (sub-comp g h) γ)

  -- Coupling derivations: the provenance lemmas at this record's fields.
  post-comp
    : ∀ {x y z} (f : hom x y) (g : hom y z) {w} (a : hom w x)
    → post (f ⨾ g) a ≡ post g (post f a)
  post-comp f g = post-comp-from-coupling S compose-contr interchange f g

  comp-eq : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾ g ≡ post g f
  comp-eq f g =
    comp-eq-from-coupling S compose-contr interchange post-eval f g

  idem : ∀ {x} → idn x ⨾ idn x ≡ idn x
  idem = idem-from-coupling S compose-contr interchange post-eval

  -- The eval axiom is self-mirror: pre f (idn y) and post f (idn x)
  -- both read emb f at the doubly-centered context.
  pre-eval : ∀ {x y} (f : hom x y) → pre f (idn y) ≡ f
  pre-eval f = post-eval f

  -- Unit fragment: the two unit equivalences cancel the identity's
  -- actions, and the identity absorbs on the left of `emb`.
  absorb-l : ∀ {x v} (b : hom x v) → pre (idn x) b ≡ b
  absorb-l {x} b = equiv→lc unit-eqvl pre-idn-idpt
    where
      pre-idn-idpt : pre (idn x) (pre (idn x) b) ≡ pre (idn x) b
      pre-idn-idpt =
        sym (subst (λ t → pre t b ≡ pre (idn x) (pre (idn x) b))
          idem (pre-comp (idn x) (idn x) b))

  absorb-r : ∀ {w x} (a : hom w x) → post (idn x) a ≡ a
  absorb-r {w} {x} a = equiv→lc unit-eqvr post-idn-idpt
    where
      post-idn-idpt : post (idn x) (post (idn x) a) ≡ post (idn x) a
      post-idn-idpt =
        sym (subst (λ t → post t a ≡ post (idn x) (post (idn x) a))
          idem (post-comp (idn x) (idn x) a))

  ·-idn : ∀ {x y} (F : composite x y) → F · idn y ≡ F
  ·-idn F = funext λ γ →
    ap (λ β → F (γ .fst , β)) (ap (γ .snd .fst ,_) (absorb-l (γ .snd .snd)))

  emb-idn-absorb : ∀ {x y} (f : hom x y) → emb (idn x) · f ≡ emb f
  emb-idn-absorb f = funext λ γ →
    interchange (idn _) f (γ .fst .snd) (γ .snd .snd)
    ∙ ap (λ a' → emb f ((γ .fst .fst , a') , γ .snd))
        (absorb-r (γ .fst .snd))

  emb-image-contr : ∀ {x y} (f : hom x y) → is-contr (fiber emb (emb f))
  emb-image-contr f =
    subst (λ T → is-contr (fiber emb T))
      (emb-idn-absorb f) (compose-contr (idn _) f)

  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn y ≡ f
  unitr f = ap fst (is-contr→is-prop (emb-image-contr f) lhs rhs)
    where
      lhs : fiber emb (emb f)
      lhs = (f ⨾ idn _) , (emb-comp f (idn _) ∙ ·-idn (emb f))
      rhs : fiber emb (emb f)
      rhs = f , refl

  unitl : ∀ {x y} (f : hom x y) → idn x ⨾ f ≡ f
  unitl f = ap fst (is-contr→is-prop (emb-image-contr f) lhs rhs)
    where
      lhs : fiber emb (emb f)
      lhs = (idn _ ⨾ f) , (emb-comp (idn _) f ∙ emb-idn-absorb f)
      rhs : fiber emb (emb f)
      rhs = f , refl

  emb-post
    : ∀ {x y} (f : hom x y) {w} (a : hom w x) {v} (b : hom y v)
    → emb f ((w , a) , (v , b)) ≡ emb (idn y) ((w , post f a) , (v , b))
  emb-post {x} {y} f {w} a {v} b =
    ap (λ b' → emb f ((w , a) , (v , b'))) (sym (absorb-l b))
    ∙ interchange f (idn y) a b

  unit-is-prop
    : ∀ {x} (e : hom x x)
    → (∀ {w} → is-equiv (λ (a : hom w x) → emb e ((w , a) , (x , e))))
    → post e e ≡ e
    → e ≡ idn x
  unit-is-prop {x} e re idpt = sym (post-eval e) ∙ post-e-absorb (idn x)
    where
      e-idem : e ⨾ e ≡ e
      e-idem = comp-eq e e ∙ idpt

      post-e-idpt : ∀ {w} (g : hom w x) → post e (post e g) ≡ post e g
      post-e-idpt g =
        sym (sym (ap (λ t → post t g) e-idem) ∙ post-comp e e g)

      post-e-squared
        : ∀ {w} (g : hom w x)
        → emb e ((w , g) , (x , e)) ≡ post e (post e g)
      post-e-squared {w} g =
        emb-post e g e
        ∙ sym (ap (λ b' → emb (idn x) ((w , post e g) , (x , b')))
            (post-eval e))
        ∙ interchange (idn x) e (post e g) (idn x)
        ∙ ap (λ t → post e t) (absorb-r (post e g))

      post-e-absorb : ∀ {w} (g : hom w x) → post e g ≡ g
      post-e-absorb g = equiv→lc re
        (post-e-squared (post e g)
         ∙ post-e-idpt (post e g)
         ∙ sym (post-e-squared g))

  -- `emb` is an embedding: `is-representable F` is a proposition. This
  -- upgrades `hom≃representable` to a subtype inclusion.
  is-representable-prop
    : ∀ {x y} (F : composite x y) → is-prop (is-representable F)
  is-representable-prop = image-fibers-contr→is-embedding emb-image-contr
```

## Frozen `Cat.Codep.Op` opposite machinery

The subset of `Cat.Codep.Op` this file consumes: `op-structure`, the
composite transposers `swap·`/`swap·'`, the Route-B `op-comp-path`/
`op-axioms`, and `op-structure-invol`. The unused parity witnesses and
`op`/`op-invol`/`op-axioms-invol` are omitted.

```agda
-- Frozen from Cat.Codep.Op @ 9133396 (Gloss certificates inline
-- Cat.* definitions — the library may change; this evidence may not).
module _ {o h} {ob : Type o} where
  open hcategory-structure

  op-structure
    : hcategory-structure {o} {h} ob → hcategory-structure {o} {h} ob
  op-structure S .hom x y = S .hom y x
  op-structure S .idn     = S .idn
  op-structure S .emb f γ = S .emb f (swap γ)

module _ {o h} {ob : Type o} (S : hcategory-structure {o} {h} ob) where
  private
    module S  = hcategory-structure S
    module Sᵒ = hcategory-structure (op-structure S)

  swap· : ∀ {x y} → S.composite y x → Sᵒ.composite x y
  swap· F γ = F (swap γ)

  swap·' : ∀ {x y} → Sᵒ.composite x y → S.composite y x
  swap·' G δ = G (swap δ)

module _ {o h} {ob : Type o} {S : hcategory-structure {o} {h} ob}
  (A : hcategory-axioms S) where
  private
    module S  = hcategory-structure S
    module Sᵒ = hcategory-structure (op-structure S)
    module A  = hcategory-axioms A

  op-comp-path
    : ∀ {x y z} (f : S.hom y x) (g : S.hom z y)
    → S.emb g S.· f ≡ swap·' S (Sᵒ.emb f Sᵒ.· g)
  op-comp-path f g = funext λ γ →
    A.interchange g f (γ .fst .snd) (γ .snd .snd)

  op-axioms : hcategory-axioms (op-structure S)
  op-axioms .hcategory-axioms.compose-contr f g .center =
    A._⨾_ g f , ap (swap· S) (A.emb-comp g f ∙ op-comp-path f g)
  op-axioms .hcategory-axioms.compose-contr f g .paths =
    is-contr→is-prop
      (retract→is-hlevel Z to fro (λ _ → refl)
        (subst (λ T → is-contr (fiber S.emb T))
          (op-comp-path f g) (A.compose-contr g f)))
      (op-axioms .hcategory-axioms.compose-contr f g .center)
    where
      to : fiber S.emb (swap·' S (Sᵒ.emb f Sᵒ.· g))
         → fiber Sᵒ.emb (Sᵒ.emb f Sᵒ.· g)
      to (m , p) = m , ap (swap· S) p

      fro : fiber Sᵒ.emb (Sᵒ.emb f Sᵒ.· g)
          → fiber S.emb (swap·' S (Sᵒ.emb f Sᵒ.· g))
      fro (m , q) = m , ap (swap·' S) q
  op-axioms .hcategory-axioms.interchange f g a b =
    sym (A.interchange g f b a)
  op-axioms .hcategory-axioms.post-eval f = A.post-eval f
  op-axioms .hcategory-axioms.unit-eqvl   = A.unit-eqvr
  op-axioms .hcategory-axioms.unit-eqvr   = A.unit-eqvl

module _ {o h} {ob : Type o} where
  open hcategory-structure

  op-structure-invol
    : (S : hcategory-structure {o} {h} ob)
    → op-structure (op-structure S) ≡ S
  op-structure-invol S i .hom = S .hom
  op-structure-invol S i .idn = S .idn
  op-structure-invol S i .emb = S .emb

```

## Frozen `Cat.Type` category record

The four-axiom `Cat.Type.category` record (with its derived `idn`/`noy`/
`yon`/`_⨾_`/`emb-composite`), frozen verbatim. The `Virtual` module and
`op`/`op-invol` are omitted — `gate4-type-instance` uses only the
record's projections.

```agda
-- Frozen from Cat.Type @ 9133396 (Gloss certificates inline Cat.*
-- definitions — the library may change; this evidence may not).
record category o h : Type₊ (o ⊔ h) where
  no-eta-equality
  field
    ob  : Type o
    hom : ob → ob → Type h
    emb : ∀ {x y} → hom x y
        → ∀ w → hom w x → ∀ z → hom y z → hom w z
    unit : ∀ {x} →
      Σ e ∶ hom x x
      , (∀ {z} → is-equiv (λ (h : hom x z) → emb e x e z h))
      × (∀ {w} → is-equiv (λ (g : hom w x) → emb e w g x e))

  idn : ∀ {x} → hom x x
  idn = unit .fst

  noy : ∀ {x y} → hom x y → ∀ z → hom y z → hom x z
  noy f z h = emb f _ idn z h

  yon : ∀ {x y} → hom x y → ∀ w → hom w x → hom w y
  yon f w g = emb f w g _ idn

  unit-eqvl : ∀ {x} {z : ob}
    → is-equiv (λ (h : hom x z) → noy idn z h)
  unit-eqvl = unit .snd .fst

  unit-eqvr : ∀ {x} {w : ob}
    → is-equiv (λ (g : hom w x) → yon idn w g)
  unit-eqvr = unit .snd .snd

  field
    compose-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr
          (fiber (emb {x} {z})
            (λ w a v b → emb f w a v (noy g v b)))

    interchange
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        w (a : hom w x) v (b : hom z v)
      → emb f w a v (noy g v b)
      ≡ emb g w (yon f w a) v b

    yon-eval
      : ∀ {x y} (f : hom x y) → yon f x idn ≡ f

  yon-idpt : ∀ {x} → yon (idn {x}) x idn ≡ idn
  yon-idpt = yon-eval idn

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = compose-contr f g .center .fst
  infixr 40 _⨾_

  emb-composite
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → emb (f ⨾ g)
    ≡ (λ w a v b → emb f w a v (noy g v b))
  emb-composite f g =
    compose-contr f g .center .snd

  {-# INLINE emb #-}
  {-# INLINE _⨾_ #-}

```

## Generic path helpers

```agda
sym-sym : ∀ {u} {A : Type u} {a b : A} (p : a ≡ b) → sym (sym p) ≡ p
sym-sym p = J (λ _ p → sym (sym p) ≡ p) refl p

sym-∙ : ∀ {u} {A : Type u} {a b d : A} (p : a ≡ b) (q : b ≡ d)
      → sym (p ∙ q) ≡ sym q ∙ sym p
sym-∙ {a = a} p q =
  J (λ _ q → sym (p ∙ q) ≡ sym q ∙ sym p)
    (ap sym (Path.unitr p) ∙ sym (Path.unitl (sym p))) q

-- Move a `sym q` factor across the equation: from p ∙ sym q ≡ r to
-- p ≡ r ∙ q.
move-r
  : ∀ {u} {A : Type u} {a b c : A}
    (p : a ≡ b) (q : c ≡ b) (r : a ≡ c)
  → p ∙ sym q ≡ r → p ≡ r ∙ q
move-r p q r H =
    sym (Path.unitr p)
  ∙ ap (p ∙_) (sym (Path.invl q))
  ∙ Path.assoc p (sym q) q
  ∙ ap (_∙ q) H
```

## GATE 1 — the 8-field record and the derived θ-core

`hcategory-axioms₈` is `hcategory-axioms` with the three coherence
cells spliced in after `absorb-r`. The five base fields and the
derived chain up through `absorb-l`/`absorb-r` are verbatim from
`Cat.Codep.Base` (reusing the provenance lemmas
`post-comp-from-coupling` etc.). The three cells sit in a second
`field` block, then the rest of the derived chain is verbatim, and
finally `θ-core` is derived from the three cells.

```agda
record hcategory-axioms₈ {o h} {ob : Type o}
  (S : hcategory-structure {o} {h} ob) : Type (o ⊔ h) where
  no-eta-equality
  open hcategory-structure S

  field
    compose-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (is-representable (emb f · g))
    interchange
      : ∀ {x y z} (f : hom x y) (g : hom y z)
        {w} (a : hom w x) {v} (b : hom z v)
      → emb f ((w , a) , (v , pre g b))
      ≡ emb g ((w , post f a) , (v , b))
    post-eval
      : ∀ {x y} (f : hom x y) → post f (idn x) ≡ f
    unit-eqvl : ∀ {x} {v} → is-equiv (pre (idn x) {v})
    unit-eqvr : ∀ {x} {w} → is-equiv (post (idn x) {w})

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = compose-contr f g .center .fst

  emb-comp : ∀ {x y z} (f : hom x y) (g : hom y z)
           → emb (f ⨾ g) ≡ emb f · g
  emb-comp f g = compose-contr f g .center .snd

  pre-comp : ∀ {y z w} (g : hom y z) (h : hom z w) {v} (b : hom w v)
           → pre (g ⨾ h) b ≡ pre g (pre h b)
  pre-comp {y} g h {v} b = happly (emb-comp g h) (ctr y , (v , b))

  sub-comp : ∀ {x y z w} (g : hom y z) (h : hom z w)
           → sub {x} (g ⨾ h) ≡ sub g ∘ sub h
  sub-comp g h = funext λ γ →
    ap (γ .fst ,_) (ap (γ .snd .fst ,_) (pre-comp g h (γ .snd .snd)))

  ·-comp : ∀ {x y z w} (F : composite x y) (g : hom y z) (h : hom z w)
         → F · (g ⨾ h) ≡ F · g · h
  ·-comp F g h = funext λ γ → ap F (happly (sub-comp g h) γ)

  post-comp
    : ∀ {x y z} (f : hom x y) (g : hom y z) {w} (a : hom w x)
    → post (f ⨾ g) a ≡ post g (post f a)
  post-comp f g = post-comp-from-coupling S compose-contr interchange f g

  comp-eq : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾ g ≡ post g f
  comp-eq f g =
    comp-eq-from-coupling S compose-contr interchange post-eval f g

  idem : ∀ {x} → idn x ⨾ idn x ≡ idn x
  idem = idem-from-coupling S compose-contr interchange post-eval

  pre-eval : ∀ {x y} (f : hom x y) → pre f (idn y) ≡ f
  pre-eval f = post-eval f

  -- Inlined (no `where`): anonymous modules from `where` clauses are
  -- illegal in a record before the last field, so the idempotency
  -- squares are written inline.
  absorb-l : ∀ {x v} (b : hom x v) → pre (idn x) b ≡ b
  absorb-l {x} b = equiv→lc unit-eqvl
    (sym (subst (λ t → pre t b ≡ pre (idn x) (pre (idn x) b))
      idem (pre-comp (idn x) (idn x) b)))

  absorb-r : ∀ {w x} (a : hom w x) → post (idn x) a ≡ a
  absorb-r {w} {x} a = equiv→lc unit-eqvr
    (sym (subst (λ t → post t a ≡ post (idn x) (post (idn x) a))
      idem (post-comp (idn x) (idn x) a)))

  field
    absorb-lcoh
      : ∀ {y z} (g : hom y z) {v} (b : hom z v)
      → absorb-l (pre g b)
      ≡ interchange (idn y) g (idn y) b
      ∙ ap (λ a' → emb g ((y , a') , (v , b))) (post-eval (idn y))
    absorb-rcoh
      : ∀ {x y} (f : hom x y) {w} (a : hom w x)
      → absorb-r (post f a)
      ≡ sym (interchange f (idn y) a (idn y))
      ∙ ap (λ b' → emb f ((w , a) , (y , b'))) (post-eval (idn y))
    couple-D₀
      : ∀ {x}
      → absorb-l (post (idn x) (idn x))
      ∙ sym (absorb-r (post (idn x) (idn x)))
      ≡ interchange (idn x) (idn x) (idn x) (idn x)

  ·-idn : ∀ {x y} (F : composite x y) → F · idn y ≡ F
  ·-idn F = funext λ γ →
    ap (λ β → F (γ .fst , β)) (ap (γ .snd .fst ,_) (absorb-l (γ .snd .snd)))

  emb-idn-absorb : ∀ {x y} (f : hom x y) → emb (idn x) · f ≡ emb f
  emb-idn-absorb f = funext λ γ →
    interchange (idn _) f (γ .fst .snd) (γ .snd .snd)
    ∙ ap (λ a' → emb f ((γ .fst .fst , a') , γ .snd))
        (absorb-r (γ .fst .snd))

  emb-image-contr : ∀ {x y} (f : hom x y) → is-contr (fiber emb (emb f))
  emb-image-contr f =
    subst (λ T → is-contr (fiber emb T))
      (emb-idn-absorb f) (compose-contr (idn _) f)

  unitr : ∀ {x y} (f : hom x y) → f ⨾ idn y ≡ f
  unitr f = ap fst (is-contr→is-prop (emb-image-contr f) lhs rhs)
    where
      lhs : fiber emb (emb f)
      lhs = (f ⨾ idn _) , (emb-comp f (idn _) ∙ ·-idn (emb f))
      rhs : fiber emb (emb f)
      rhs = f , refl

  unitl : ∀ {x y} (f : hom x y) → idn x ⨾ f ≡ f
  unitl f = ap fst (is-contr→is-prop (emb-image-contr f) lhs rhs)
    where
      lhs : fiber emb (emb f)
      lhs = (idn _ ⨾ f) , (emb-comp (idn _) f ∙ emb-idn-absorb f)
      rhs : fiber emb (emb f)
      rhs = f , refl

  emb-post
    : ∀ {x y} (f : hom x y) {w} (a : hom w x) {v} (b : hom y v)
    → emb f ((w , a) , (v , b)) ≡ emb (idn y) ((w , post f a) , (v , b))
  emb-post {x} {y} f {w} a {v} b =
    ap (λ b' → emb f ((w , a) , (v , b'))) (sym (absorb-l b))
    ∙ interchange f (idn y) a b

  is-representable-prop
    : ∀ {x y} (F : composite x y) → is-prop (is-representable F)
  is-representable-prop = image-fibers-contr→is-embedding emb-image-contr

  -- Spike-0: θ-core derived from the three cells by direct ∙-algebra.
  θ-core
    : ∀ {x}
    → ap (pre (idn x)) (post-eval (idn x))
    ≡ interchange (idn x) (idn x) (idn x) (idn x)
      ∙ ap (post (idn x)) (post-eval (idn x))
  θ-core {x} = sym i ∙ L
    where
      e : hom x x
      e = idn x

      D₀ : hom x x
      D₀ = pre e (idn x)

      IC : pre e D₀ ≡ post e D₀
      IC = interchange e e e e

      apPre : pre e D₀ ≡ pre e e
      apPre = ap (pre e) (post-eval e)

      apPost : post e D₀ ≡ post e e
      apPost = ap (post e) (post-eval e)

      L : absorb-l D₀ ≡ IC ∙ apPost
      L = absorb-lcoh e e

      R : absorb-r D₀ ≡ sym IC ∙ apPre
      R = absorb-rcoh e e

      CD : absorb-l D₀ ∙ sym (absorb-r D₀) ≡ IC
      CD = couple-D₀

      CD' : absorb-l D₀ ≡ IC ∙ absorb-r D₀
      CD' = move-r (absorb-l D₀) (absorb-r D₀) IC CD

      i : absorb-l D₀ ≡ apPre
      i = CD'
        ∙ ap (IC ∙_) R
        ∙ Path.assoc IC (sym IC) apPre
        ∙ ap (_∙ apPre) (Path.invr IC)
        ∙ Path.unitl apPre
```

## The 8-field bundle

```agda
record hcategory₈ (o h : Level) : Type ((o ⊔ h) ₊) where
  no-eta-equality
  field
    ob        : Type o
    structure : hcategory-structure {o} {h} ob
    axioms    : hcategory-axioms₈ structure
  open hcategory-structure structure public
  open hcategory-axioms₈ axioms public
```

## GATE-1 regression witnesses

```agda
module _ {o h} {ob : Type o} {S : hcategory-structure {o} {h} ob}
  (A₈ : hcategory-axioms₈ S) where
  private
    module S  = hcategory-structure S
    module A₈ = hcategory-axioms₈ A₈

  -- The @identity ap-leg reduction fires: absorb-lcoh's family slot
  -- holds the center, so emb reads as `post`.
  killcheck-apPost
    : ∀ {x}
    → ap (λ a' → S.emb (S.idn x) ((x , a') , (x , S.idn x)))
         (A₈.post-eval (S.idn x))
    ≡ ap (S.post (S.idn x)) (A₈.post-eval (S.idn x))
  killcheck-apPost = refl

  killcheck-apPre
    : ∀ {x}
    → ap (λ b' → S.emb (S.idn x) ((x , S.idn x) , (x , b')))
         (A₈.post-eval (S.idn x))
    ≡ ap (S.pre (S.idn x)) (A₈.post-eval (S.idn x))
  killcheck-apPre = refl
```

## GATE 2 — Route-B op axioms and the 8-field discharge

Working context: an 8-field axioms value `A₈` over `S`, with the
5-field projection `A₅`, the op structure `Sᵒ`, and the Route-B op
axioms `Aᵒᴮ`.

```agda
module gate2 {o h} {ob : Type o} {S : hcategory-structure {o} {h} ob}
  (A₈ : hcategory-axioms₈ S) where
  private
    module S  = hcategory-structure S
    module Sᵒ = hcategory-structure (op-structure S)
    module A₈ = hcategory-axioms₈ A₈

  -- 5-field projection of A₈. Its derived chain (idem, absorb-l, …) is
  -- definitionally A₈'s, since the fields agree by copattern.
  A₅ : hcategory-axioms S
  A₅ .hcategory-axioms.compose-contr = A₈.compose-contr
  A₅ .hcategory-axioms.interchange   = A₈.interchange
  A₅ .hcategory-axioms.post-eval     = A₈.post-eval
  A₅ .hcategory-axioms.unit-eqvl     = A₈.unit-eqvl
  A₅ .hcategory-axioms.unit-eqvr     = A₈.unit-eqvr

  private module A₅ = hcategory-axioms A₅
```

### Route-B `compose-contrᴮ` — definitional center

```agda
  compose-contrᴮ
    : ∀ {x y z} (f : Sᵒ.hom x y) (g : Sᵒ.hom y z)
    → is-contr (fiber Sᵒ.emb (Sᵒ.emb f Sᵒ.· g))
  compose-contrᴮ f g .center =
    A₅._⨾_ g f , ap (swap· S) (A₅.emb-comp g f ∙ op-comp-path A₅ f g)
  compose-contrᴮ f g .paths =
    is-contr→is-prop (op-axioms A₅ .hcategory-axioms.compose-contr f g)
      (compose-contrᴮ f g .center)

  Aᵒᴮ : hcategory-axioms (op-structure S)
  Aᵒᴮ .hcategory-axioms.compose-contr = compose-contrᴮ
  Aᵒᴮ .hcategory-axioms.interchange =
    op-axioms A₅ .hcategory-axioms.interchange
  Aᵒᴮ .hcategory-axioms.post-eval =
    op-axioms A₅ .hcategory-axioms.post-eval
  Aᵒᴮ .hcategory-axioms.unit-eqvl =
    op-axioms A₅ .hcategory-axioms.unit-eqvl
  Aᵒᴮ .hcategory-axioms.unit-eqvr =
    op-axioms A₅ .hcategory-axioms.unit-eqvr

  private module Aᵒᴮ = hcategory-axioms Aᵒᴮ
```

Regression witness: the op extraction is the base extraction swapped.

```agda
  ⨾ᴮ-def : ∀ {x y z} (f : Sᵒ.hom x y) (g : Sᵒ.hom y z)
         → Aᵒᴮ._⨾_ f g ≡ A₅._⨾_ g f
  ⨾ᴮ-def f g = refl
```

### The definitional parity facts

```agda
  pre-compᵒ-is-post-comp
    : ∀ {w x} (c : S.hom w x)
    → Aᵒᴮ.pre-comp (Sᵒ.idn x) (Sᵒ.idn x) c
    ≡ A₅.post-comp (S.idn x) (S.idn x) c
  pre-compᵒ-is-post-comp c = refl

  post-compᵒ-is-pre-comp
    : ∀ {x v} (c : S.hom x v)
    → Aᵒᴮ.post-comp (Sᵒ.idn x) (Sᵒ.idn x) c
    ≡ A₅.pre-comp (S.idn x) (S.idn x) c
  post-compᵒ-is-pre-comp {x} {v} c =
      sym (Path.assoc H IC' (sym IC'))
    ∙ ap (H ∙_) (Path.invr IC')
    ∙ Path.unitr H
    where
      H = A₅.pre-comp (S.idn x) (S.idn x) c
      IC' = A₅.interchange (S.idn x) (S.idn x) (S.idn x) c
```

### θ — `idemᵒ ≡ idem`, closed against the GATE-1 θ-core

```agda
  module θ-derivation {x : ob} where
    private
      e : S.hom x x
      e = S.idn x

      ee : S.hom x x
      ee = A₅._⨾_ e e

      H0 = happly (A₅.emb-comp e e) ((x , e) , (x , e))
      IC = A₅.interchange e e e e
      apPost = ap (S.post e) (A₅.post-eval e)
      apPre = ap (S.pre e) (A₅.post-eval e)

      κ : (H0 ∙ IC) ∙ sym IC ≡ H0
      κ = sym (Path.assoc H0 IC (sym IC))
        ∙ ap (H0 ∙_) (Path.invr IC)
        ∙ Path.unitr H0

      θ-core : apPre ≡ IC ∙ apPost
      θ-core = A₈.θ-core {x}

      M-B≡M-A : (((H0 ∙ IC) ∙ sym IC) ∙ apPre) ≡ ((H0 ∙ IC) ∙ apPost)
      M-B≡M-A =
          ap (_∙ apPre) κ
        ∙ ap (H0 ∙_) θ-core
        ∙ Path.assoc H0 IC apPost

      ξ : Aᵒᴮ.comp-eq e e ≡ A₅.comp-eq e e
      ξ = ap (sym (A₅.post-eval ee) ∙_) M-B≡M-A

    θ : Aᵒᴮ.idem {x} ≡ A₅.idem {x}
    θ = ap (_∙ A₅.post-eval e) ξ

  θ : ∀ {x} → Aᵒᴮ.idem {x} ≡ A₅.idem {x}
  θ {x} = θ-derivation.θ {x}
```

### The bridges

`bridge-l` relates the op record's `absorb-l` to the base `absorb-r`
(both `post (idn x) c ≡ c`); they differ only in `idemᵒ` vs `idem`
inside the idempotency square, bridged by `θ`. `bridge-r` relates the
op record's `absorb-r` to the base `absorb-l`, needing both `θ` and the
`Path.invr` collapse `post-compᵒ-is-pre-comp` on the r-side.

```agda
  bridge-l : ∀ {w x} (c : S.hom w x) → Aᵒᴮ.absorb-l c ≡ A₅.absorb-r c
  bridge-l {w} {x} c = ap Φ (θ {x})
    where
      Φ : (A₅._⨾_ (S.idn x) (S.idn x) ≡ S.idn x)
        → (S.post (S.idn x) c ≡ c)
      Φ z = equiv→lc A₅.unit-eqvr
        (sym (subst (λ t → S.post t c ≡ S.post (S.idn x) (S.post (S.idn x) c))
          z (A₅.post-comp (S.idn x) (S.idn x) c)))

  bridge-r : ∀ {x v} (c : S.hom x v) → Aᵒᴮ.absorb-r c ≡ A₅.absorb-l c
  bridge-r {x} {v} c =
      ap (λ z → Θ z (Aᵒᴮ.post-comp (S.idn x) (S.idn x) c)) (θ {x})
    ∙ ap (Θ (A₅.idem {x})) (post-compᵒ-is-pre-comp c)
    where
      Θ : (A₅._⨾_ (S.idn x) (S.idn x) ≡ S.idn x)
        → (S.pre (A₅._⨾_ (S.idn x) (S.idn x)) c
           ≡ S.pre (S.idn x) (S.pre (S.idn x) c))
        → (S.pre (S.idn x) c ≡ c)
      Θ z u = equiv→lc A₅.unit-eqvl
        (sym (subst (λ t → S.pre t c ≡ S.pre (S.idn x) (S.pre (S.idn x) c)) z u))
```

### `couple-D₀ᵒ` — the conjugated ap-sym image

```agda
  couple-D₀ᵒ
    : ∀ {x}
    → Aᵒᴮ.absorb-l (S.post (S.idn x) (S.idn x))
    ∙ sym (Aᵒᴮ.absorb-r (S.post (S.idn x) (S.idn x)))
    ≡ sym (A₅.interchange (S.idn x) (S.idn x) (S.idn x) (S.idn x))
  couple-D₀ᵒ {x} = (λ i → bridge-l D₀ i ∙ sym (bridge-r D₀ i)) ∙ conj
    where
      D₀ = S.post (S.idn x) (S.idn x)
      IC = A₅.interchange (S.idn x) (S.idn x) (S.idn x) (S.idn x)
      conj : A₅.absorb-r D₀ ∙ sym (A₅.absorb-l D₀) ≡ sym IC
      conj =
          ap (_∙ sym (A₅.absorb-l D₀)) (sym (sym-sym (A₅.absorb-r D₀)))
        ∙ sym (sym-∙ (A₅.absorb-l D₀) (sym (A₅.absorb-r D₀)))
        ∙ ap sym (A₈.couple-D₀ {x})
```

### The 8-field op axioms

```agda
  op-axioms₈ : hcategory-axioms₈ (op-structure S)
  op-axioms₈ .hcategory-axioms₈.compose-contr = compose-contrᴮ
  op-axioms₈ .hcategory-axioms₈.interchange =
    op-axioms A₅ .hcategory-axioms.interchange
  op-axioms₈ .hcategory-axioms₈.post-eval =
    op-axioms A₅ .hcategory-axioms.post-eval
  op-axioms₈ .hcategory-axioms₈.unit-eqvl =
    op-axioms A₅ .hcategory-axioms.unit-eqvl
  op-axioms₈ .hcategory-axioms₈.unit-eqvr =
    op-axioms A₅ .hcategory-axioms.unit-eqvr
  op-axioms₈ .hcategory-axioms₈.absorb-lcoh g b =
    bridge-l (S.post g b) ∙ A₈.absorb-rcoh g b
  op-axioms₈ .hcategory-axioms₈.absorb-rcoh f a =
    bridge-r (S.pre f a) ∙ A₈.absorb-lcoh f a
  op-axioms₈ .hcategory-axioms₈.couple-D₀ = couple-D₀ᵒ

  private module Aᵒ₈ = hcategory-axioms₈ op-axioms₈

  -- Regression witness for the 8-field op: extraction is base swapped.
  ⨾ᵒ₈-def : ∀ {x y z} (f : Sᵒ.hom x y) (g : Sᵒ.hom y z)
          → Aᵒ₈._⨾_ f g ≡ A₈._⨾_ g f
  ⨾ᵒ₈-def f g = refl
```

## GATE 3 — op-invol for the 8 fields

`op-axioms₈` exposed as a function, so the double op composes.

```agda
op-axioms₈-op
  : ∀ {o h} {ob : Type o} {S : hcategory-structure {o} {h} ob}
  → hcategory-axioms₈ S → hcategory-axioms₈ (op-structure S)
op-axioms₈-op A₈ = gate2.op-axioms₈ A₈
```

### Positive result: the five old fields lift

The five old components lift exactly as the Op module's
`op-axioms-invol`: `interchange` double sym-mirror cancels (`~~i = i`),
`post-eval` is self-mirror, the unit equivalences swap back, and
`compose-contr` is bridged by `is-prop→PathP` (its family is constant
along `op-structure-invol`, since `emb`/`pre`/`post` are). The four
non-`compose-contr` lifts are definitional (`refl`), checked here.

```agda
module gate3 {o h} {ob : Type o} {S : hcategory-structure {o} {h} ob}
  (A₈ : hcategory-axioms₈ S) where
  private
    module S  = hcategory-structure S
    module A₈ = hcategory-axioms₈ A₈

    OO : hcategory-axioms₈ (op-structure (op-structure S))
    OO = op-axioms₈-op (op-axioms₈-op A₈)
    module OO = hcategory-axioms₈ OO

  invol-interchange-def
    : ∀ {x y z} (f : S.hom x y) (g : S.hom y z)
      {w} (a : S.hom w x) {v} (b : S.hom z v)
    → OO.interchange f g a b ≡ A₈.interchange f g a b
  invol-interchange-def f g a b = refl

  invol-post-eval-def
    : ∀ {x y} (f : S.hom x y) → OO.post-eval f ≡ A₈.post-eval f
  invol-post-eval-def f = refl

  -- The double-op compose-contr changes value (Route-B center), but its
  -- fibre-of-`emb` family is constant along `op-structure-invol` and
  -- `is-contr`-propositional, so `is-prop→PathP` covers it.
  invol-compose-contr
    : ∀ {x y z} (f : S.hom x y) (g : S.hom y z)
    → PathP (λ i → is-contr (fiber S.emb (S.emb f S.· g)))
        (OO.compose-contr f g) (A₈.compose-contr f g)
  invol-compose-contr f g =
    is-prop→PathP
      {A = λ _ → is-contr (fiber S.emb (S.emb f S.· g))}
      (λ _ → is-contr-is-prop _)
      (OO.compose-contr f g) (A₈.compose-contr f g)
```

### WALL: the three cell components

The three cell components of the involution do NOT close. The `refl`
probe (attempt 1) reports, for the `absorb-lcoh` component, the exact
PathP goal (at outer dim `i`, inner dim `i₁`):

```text
-- Goal (both endpoints : S.hom y v, at dim i,i₁):
--   LHS =  (op-axioms-invol₈ i).absorb-l (pre g b)  i₁
--       =  equiv→lc (unit-eqvl (inv i))
--            (sym (subst (λ t → pre (inv i) t (pre (inv i) g b)
--                              ≡ pre (inv i) (idn (inv i) y)
--                                  (pre (inv i) (idn (inv i) y)
--                                    (pre (inv i) g b)))
--              (idem-from-coupling (op-structure-invol S i)
--                (compose-contr (inv i)) (interchange (inv i))
--                (post-eval (inv i)))
--              (happly (compose-contr (inv i) (idn y) (idn y) .center .snd)
--                (ctr (inv i) y , v , pre (inv i) g b))))  i₁
--   RHS =  S.emb g ((y , post-eval (inv i) (idn y) i₁) , (v , b))
-- where (inv i) := op-axioms-invol₈ A₈ i.
```

The family is `λ i → (inv i).absorb-l (pre g b) ≡ Dconst` — the RHS
`Dconst` is CONSTANT in `i` (interchange/post-eval/emb are), only the
LEFT endpoint `(inv i).absorb-l (pre g b)` moves, and it moves through
`compose-contr (inv i)` (via `idem`, via `emb-comp`/`pre-comp`) — the
`is-prop→PathP`-transported contractibility. By the moving-left-endpoint
square characterisation, the PathP reduces to the 2-cell telescope

```text
--   op(op).absorb-lcoh g b  ≡  qmove ∙ A₈.absorb-lcoh g b
```

with `qmove i = (inv i).absorb-l (pre g b)` the forced absorb-l motion.
Since `op(op).absorb-lcoh g b = bridge-lᴮ ∙ bridge-rᴬ ∙
A₈.absorb-lcoh g b` (the double-op unfolds the two bridges),
whiskering off `A₈.absorb-lcoh`
leaves the irreducible obligation

```text
--   bridge-lᴮ ∙ bridge-rᴬ  ≡  qmove          -- WALL
```

both sides paths `op(op).absorb-l (pre g b) ≡ A₈.absorb-l (pre g b)` in
the path space `pre (idn y) (pre g b) ≡ pre g b`.

WALL, route (a) — direct telescope: `bridge-lᴮ ∙ bridge-rᴬ ≡ qmove` is
a genuine 3-cell. The bridges are `ap _ θ` composites and `qmove` is a
transport of `absorb-l` along the `compose-contr` `is-prop→PathP`; they
do not agree by `∙`-algebra (nor definitionally — the `refl` probe
rejects). Not closable.

WALL, route (b) — `coh-project₃` (attempt 2): inapplicable.
`coh-project₃` frees a 3-cell only when both 2-cells are `ap (ap π)`
images of paths in
a CONTRACTIBLE fibre. But the target path space
`pre (idn y) (pre g b) ≡ pre g b` is NOT a proposition: via the `ap emb`
equivalence it is `emb (pre (idn y) c) ≡ emb c`, a path between two
DISTINCT `emb`-images in the wild composite Π-type `composite y v` — no
contractible fibre contains both endpoints, so there is no `π` through
which to project. And the `absorb-l` route factors through
`equiv→lc unit-eqvl` (a unit-equivalence cancellation), not an
`emb`-fibre projection, so it is not in the image of any `ap (ap π)`.

Both routes wall. The three cells are structurally identical
(`absorb-rcoh` is the `pre`/`post` mirror; `couple-D₀` the
doubly-centered instance), so all three carry the same 3-cell
obligation. This confirms the design memo's flag: `op-invol` for the
cells is the one unverified claim, and it needs either a new coherence
field (a chosen `bridge-lᴮ ∙ bridge-rᴬ ≡ qmove` datum) or a
representability overlay one rung up — not derivable by the machinery
available. The non-closing involution is left commented below.

```text
-- op-axioms-invol₈
--   : (A₈ : hcategory-axioms₈ S)
--   → PathP (λ i → hcategory-axioms₈ (op-structure-invol S i))
--       (op-axioms₈-op (op-axioms₈-op A₈)) A₈
-- op-axioms-invol₈ A₈ i .compose-contr f g = invol-compose-contr f g i
-- op-axioms-invol₈ A₈ i .interchange f g a b = A₈.interchange f g a b
-- op-axioms-invol₈ A₈ i .post-eval f = A₈.post-eval f
-- op-axioms-invol₈ A₈ i .unit-eqvl = A₈.unit-eqvl
-- op-axioms-invol₈ A₈ i .unit-eqvr = A₈.unit-eqvr
-- op-axioms-invol₈ A₈ i .absorb-lcoh g b = {! bridge-lᴮ ∙ bridge-rᴬ ≡ qmove !}
-- op-axioms-invol₈ A₈ i .absorb-rcoh f a = {! mirror !}
-- op-axioms-invol₈ A₈ i .couple-D₀     = {! doubly-centered !}
```

## GATE 4 — instance skeletons

### Walking-arrow style: prop homs discharge all three cells

If homs are propositions, hom-path spaces are propositions
(`is-prop→is-set`), so every 2-cell is inhabited — the three cells are
one-liners.

```agda
module prop-homs {o h} {ob : Type o} (S : hcategory-structure {o} {h} ob)
  (A₅ : hcategory-axioms S)
  (hom-prop : ∀ {x y} → is-prop (hcategory-structure.hom S x y))
  where
  private
    module S  = hcategory-structure S
    module A₅ = hcategory-axioms A₅

  hom-set : ∀ {x y} → is-set (S.hom x y)
  hom-set = is-prop→is-set hom-prop

  axioms₈ : hcategory-axioms₈ S
  axioms₈ .hcategory-axioms₈.compose-contr = A₅.compose-contr
  axioms₈ .hcategory-axioms₈.interchange   = A₅.interchange
  axioms₈ .hcategory-axioms₈.post-eval     = A₅.post-eval
  axioms₈ .hcategory-axioms₈.unit-eqvl     = A₅.unit-eqvl
  axioms₈ .hcategory-axioms₈.unit-eqvr     = A₅.unit-eqvr
  axioms₈ .hcategory-axioms₈.absorb-lcoh g b = hom-set _ _ _ _
  axioms₈ .hcategory-axioms₈.absorb-rcoh f a = hom-set _ _ _ _
  axioms₈ .hcategory-axioms₈.couple-D₀       = hom-set _ _ _ _
```

### The refactor equation's new shape

`assemble₈` is the new refactor shape: the five base axioms plus the
three coherence cells assemble into the 8-field record. Checked, not
merely statable.

```agda
assemble₈
  : ∀ {o h} {ob : Type o} (S : hcategory-structure {o} {h} ob)
    (A₅ : hcategory-axioms S)
    (open hcategory-structure S)
    (open hcategory-axioms A₅)
    (coh-l : ∀ {y z} (g : hom y z) {v} (b : hom z v)
           → absorb-l (pre g b)
           ≡ interchange (idn y) g (idn y) b
           ∙ ap (λ a' → emb g ((y , a') , (v , b))) (post-eval (idn y)))
    (coh-r : ∀ {x y} (f : hom x y) {w} (a : hom w x)
           → absorb-r (post f a)
           ≡ sym (interchange f (idn y) a (idn y))
           ∙ ap (λ b' → emb f ((w , a) , (y , b'))) (post-eval (idn y)))
    (coh-θ : ∀ {x}
           → absorb-l (post (idn x) (idn x))
           ∙ sym (absorb-r (post (idn x) (idn x)))
           ≡ interchange (idn x) (idn x) (idn x) (idn x))
  → hcategory-axioms₈ S
assemble₈ S A₅ coh-l coh-r coh-θ .hcategory-axioms₈.compose-contr =
  A₅ .hcategory-axioms.compose-contr
assemble₈ S A₅ coh-l coh-r coh-θ .hcategory-axioms₈.interchange =
  A₅ .hcategory-axioms.interchange
assemble₈ S A₅ coh-l coh-r coh-θ .hcategory-axioms₈.post-eval =
  A₅ .hcategory-axioms.post-eval
assemble₈ S A₅ coh-l coh-r coh-θ .hcategory-axioms₈.unit-eqvl =
  A₅ .hcategory-axioms.unit-eqvl
assemble₈ S A₅ coh-l coh-r coh-θ .hcategory-axioms₈.unit-eqvr =
  A₅ .hcategory-axioms.unit-eqvr
assemble₈ S A₅ coh-l coh-r coh-θ .hcategory-axioms₈.absorb-lcoh = coh-l
assemble₈ S A₅ coh-l coh-r coh-θ .hcategory-axioms₈.absorb-rcoh = coh-r
assemble₈ S A₅ coh-l coh-r coh-θ .hcategory-axioms₈.couple-D₀   = coh-θ
```

### Type instance: from a `Cat.Type` category

The structure transcription from `Cat.Type.category` is a clean
uncurry of the `emb` context (`noy`/`yon` = `pre`/`post`). Feeding the
materialised five-field axioms `A₅` and the three cells into
`assemble₈` yields the bundle — the literal
`category → coh-l → coh-r → coh-θ → hcategory₈` shape. The five-field
materialisation `A₅` (the existing refactor) is taken as a parameter.

```agda
module gate4-type-instance where
  module _ {o h} (C : category o h) where
    private module C = category C

    struct-of : hcategory-structure {o} {h} C.ob
    struct-of .hcategory-structure.hom = C.hom
    struct-of .hcategory-structure.idn x = C.idn
    struct-of .hcategory-structure.emb f γ =
      C.emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

    type-instance
      : (A₅ : hcategory-axioms struct-of)
        (open hcategory-structure struct-of)
        (open hcategory-axioms A₅)
        (coh-l : ∀ {y z} (g : hom y z) {v} (b : hom z v)
               → absorb-l (pre g b)
               ≡ interchange (idn y) g (idn y) b
               ∙ ap (λ a' → emb g ((y , a') , (v , b))) (post-eval (idn y)))
        (coh-r : ∀ {x y} (f : hom x y) {w} (a : hom w x)
               → absorb-r (post f a)
               ≡ sym (interchange f (idn y) a (idn y))
               ∙ ap (λ b' → emb f ((w , a) , (y , b'))) (post-eval (idn y)))
        (coh-θ : ∀ {x}
               → absorb-l (post (idn x) (idn x))
               ∙ sym (absorb-r (post (idn x) (idn x)))
               ≡ interchange (idn x) (idn x) (idn x) (idn x))
      → hcategory₈ o h
    type-instance A₅ coh-l coh-r coh-θ .hcategory₈.ob = C.ob
    type-instance A₅ coh-l coh-r coh-θ .hcategory₈.structure = struct-of
    type-instance A₅ coh-l coh-r coh-θ .hcategory₈.axioms =
      assemble₈ struct-of A₅ coh-l coh-r coh-θ
```
