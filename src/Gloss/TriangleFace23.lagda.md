Gloss: machine-checked evidence for T7 (history) in docs/gloss.md.
Self-contained modulo Core.*; Cat.* definitions frozen at 9133396.

UPDATE (2026-07-11): the "independent 2-cell" framing below was
REFUTED. `absorb-r (idn y) ≡ post-eval (idn y)` is DERIVABLE — it is
`gauge-r` in `Cat.Codep.Coherent` (homotopy-naturality of `absorb-r`
along `post-eval`, whiskered against the θ-core reconciliations). The
full `face₂₃` and Mac Lane triangle now live in
`Cat.Codep.Triangle.triangle-full-tower`. This file is kept as the
historical isolation of the bridge.

Wall witness: with the coherence overlay in scope, the full-triangle
face₂₃ (landing on the *library* `unitl g`) reduces exactly to the
2-cell `absorb-r (idn y) ≡ post-eval (idn y)` (once thought
independent; now derived as `gauge-r`).

The library `unitl g` (Cat.Codep.Base) bakes in `emb-idn-absorb g`,
whose pre-position reading is *definitionally* the `absorb-r` form
(`K-is-absorbr = refl` below). The overlay `absorb-lcoh` supplies
`absorb-l` in the `post-eval` form. Bridging the two — which face₂₃
must — is exactly `absorb-r (idn y) ≡ post-eval (idn y)`, which the
`Cat.Codep.Coherent` header and MEMORY declare independent of the five
base fields (S²/π₃ countermodel). Everything *except* that cell closes
by `refl`/`ap`, so `bridge-from-cell` is a total function of it.

Tracked Gloss evidence (T7 history).

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Gloss.TriangleFace23 where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (is-contr→is-prop; _∙_; module Path)
open import Core.Transport.J using (J; subst)
open import Core.Equiv.Base using (iso→equiv; _≃_; is-equiv)
open import Core.Function.Embedding
  using (equiv→lc; image-fibers-contr→is-embedding)
open import Core.Path.Base using (ap-comp)
```

## Frozen `Cat.Codep.Base` definitions

Verbatim copies of the `Cat.Codep.Base` records and coupling
provenance lemmas. This certificate is self-contained modulo `Core.*`;
the live `Cat.*` sources may change, and this evidence must not.

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

record hcategory (o h : Level) : Type ((o ⊔ h) ₊) where
  no-eta-equality
  field
    ob        : Type o
    structure : hcategory-structure {o} {h} ob
    axioms    : hcategory-axioms structure
  open hcategory-structure structure public
  open hcategory-axioms axioms public
```

## Frozen `Cat.Codep.Coherent` coherence cells

The three coherence cells of `hcategory-2-coherent`, frozen verbatim.
The derived `θ-core`/`gauge-*` members of the source record are omitted;
this certificate consumes only the `absorb-lcoh` cell.

```agda
-- Frozen from Cat.Codep.Coherent @ 9133396 (Gloss certificates inline
-- Cat.* definitions — the library may change; this evidence may not).
record hcategory-2-coherent {o h} (C : hcategory o h) : Type (o ⊔ h) where
  no-eta-equality
  open hcategory C

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
```

```agda
module _ {o h} (C : hcategory o h) (A2 : hcategory-2-coherent C) where
  open hcategory C
  open hcategory-2-coherent A2

  module probe {y z v : ob} (g : hom y z) (b : hom z v) where
    δ₀ : ctx y z
    δ₀ = ctr y , (v , b)

    c : hom y v
    c = pre g b

    -- the emb-idn-absorb reading (baked into the library unitl g)
    K-absorbr : pre (idn y) c ≡ c
    K-absorbr = happly (emb-idn-absorb g) δ₀

    -- machine-checked: it IS the absorb-r form, definitionally
    K-is-absorbr
      : K-absorbr
      ≡ interchange (idn y) g (idn y) b
        ∙ ap (λ a' → emb g ((y , a') , (v , b))) (absorb-r (idn y))
    K-is-absorbr = refl

    -- the overlay supplies absorb-l in POST-EVAL form
    absorb-l-posteval
      : absorb-l c
      ≡ interchange (idn y) g (idn y) b
        ∙ ap (λ a' → emb g ((y , a') , (v , b))) (post-eval (idn y))
    absorb-l-posteval = absorb-lcoh g b

    -- The face₂₃ bridge (K ≡ absorb-l c) is a TOTAL function of the
    -- one independent cell: everything else closes by refl/ap. No hole.
    bridge-from-cell
      : absorb-r (idn y) ≡ post-eval (idn y)
      → K-absorbr ≡ absorb-l c
    bridge-from-cell inner-cell =
      K-is-absorbr
      ∙ ap (interchange (idn y) g (idn y) b ∙_)
          (ap (ap (λ a' → emb g ((y , a') , (v , b)))) inner-cell)
      ∙ sym absorb-l-posteval
```
