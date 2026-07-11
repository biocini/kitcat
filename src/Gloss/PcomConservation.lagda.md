Gloss: machine-checked evidence for T20 in docs/gloss.md.
Self-contained modulo Core.*; Cat.* definitions frozen at 9133396.

Spike: reindex/whisker face bridges via native `pcom` operations.

Four staged variants of the `Cat.Codep` pentagon tower, testing whether
the reindex snd-bridges reduce to single `pcom.catr` applications and
whether the whisker faces incur a conservation-law `+1` step when the
`ptᵢ` endpoints are carried in native ternary `pcom` form.

- `baseline` — verbatim `collapse-B` (Move B only, unit-free). Oracle.
- `stage1`  — reindex faces routed through `pcom.catr`, pt-endpoints
              kept binary. (KILL-gate K1.)
- `stage2`  — pt-endpoints as native `pcom`; reindex via `catr`,
              whisker faces reconciled. (Conservation-law gate K2.)
- `stage3`  — scaffold helpers `reindex-face`/`whisker-face` on the
              K2 winner.

Tracked Gloss evidence (T20).

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Gloss.PcomConservation where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using
  ( is-contr→is-prop; is-contr→is-set; _∙_; contr-face; module Path
  ; pcom; module pcom; pcom→∙ )
open import Core.Transport.J using (J; subst)
open import Core.Transport.Properties using (prop-inhabited→is-contr)
open import Core.Path.Base using (ap-comp)
open import Core.Homotopy using (homotopy-natural)
open import Core.Coherence.Base using (coh-project)
open import Core.Equiv.Base using (iso→equiv; _≃_; is-equiv)
open import Core.Function.Embedding
  using (equiv→lc; image-fibers-contr→is-embedding)
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

## Stage 0 — baseline (verbatim collapse-B, Move B only, unit-free)

```agda
module baseline {o h} (C : hcategory o h) where
  open hcategory C

  E₃ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w) → composite x w
  E₃ f g h = emb f · g · h

  pt-l : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
       → fiber emb (E₃ f g h)
  pt-l f g h = (f ⨾ g) ⨾ h , emb-comp (f ⨾ g) h ∙ ap (_· h) (emb-comp f g)

  pt-r : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
       → fiber emb (E₃ f g h)
  pt-r f g h = f ⨾ (g ⨾ h) , emb-comp f (g ⨾ h) ∙ ·-comp (emb f) g h

  E₃-contr : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
           → is-contr (fiber emb (E₃ f g h))
  E₃-contr f g h .center = pt-l f g h
  E₃-contr f g h .paths =
    is-contr→is-prop
      (subst (λ T → is-contr (fiber emb T))
        (ap (_· h) (emb-comp f g))
        (compose-contr (f ⨾ g) h)) _

  assoc-σ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
          → pt-l f g h ≡ pt-r f g h
  assoc-σ f g h = is-contr→is-prop (E₃-contr f g h) (pt-l f g h) (pt-r f g h)

  assoc : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
        → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h = ap fst (assoc-σ f g h)

  module _ {x y z w v}
    (f : hom x y) (g : hom y z) (h : hom z w) (k : hom w v) where

    E₄ : composite x v
    E₄ = emb f · g · h · k

    E₄c : is-contr (fiber emb E₄)
    E₄c .center .fst = ((f ⨾ g) ⨾ h) ⨾ k
    E₄c .center .snd =
        emb-comp ((f ⨾ g) ⨾ h) k
      ∙ ap (_· k) (emb-comp (f ⨾ g) h)
      ∙ ap (_· k) (ap (_· h) (emb-comp f g))
    E₄c .paths =
      is-contr→is-prop
        (subst (λ T → is-contr (fiber emb T)) path₄
          (compose-contr ((f ⨾ g) ⨾ h) k)) _
      where
        path₄ : emb ((f ⨾ g) ⨾ h) · k ≡ E₄
        path₄ = ap (_· k) (emb-comp (f ⨾ g) h)
              ∙ ap (_· k) (ap (_· h) (emb-comp f g))

    pt₁ : fiber emb E₄
    pt₁ = ((f ⨾ g) ⨾ h) ⨾ k
        , emb-comp ((f ⨾ g) ⨾ h) k
        ∙ ap (_· k) (emb-comp (f ⨾ g) h)
        ∙ ap (_· k) (ap (_· h) (emb-comp f g))

    pt₂ : fiber emb E₄
    pt₂ = (f ⨾ (g ⨾ h)) ⨾ k
        , emb-comp (f ⨾ (g ⨾ h)) k
        ∙ ap (_· k) (emb-comp f (g ⨾ h))
        ∙ ap (_· k) (·-comp (emb f) g h)

    pt₃ : fiber emb E₄
    pt₃ = f ⨾ ((g ⨾ h) ⨾ k)
        , emb-comp f ((g ⨾ h) ⨾ k)
        ∙ ·-comp (emb f) (g ⨾ h) k
        ∙ ap (_· k) (·-comp (emb f) g h)

    pt₄ : fiber emb E₄
    pt₄ = (f ⨾ g) ⨾ (h ⨾ k)
        , emb-comp (f ⨾ g) (h ⨾ k)
        ∙ ap (_· (h ⨾ k)) (emb-comp f g)
        ∙ ·-comp (emb f · g) h k

    pt₅ : fiber emb E₄
    pt₅ = f ⨾ (g ⨾ (h ⨾ k))
        , emb-comp f (g ⨾ (h ⨾ k))
        ∙ ·-comp (emb f) g (h ⨾ k)
        ∙ ·-comp (emb f · g) h k

    σ₁₂ = is-contr→is-prop E₄c pt₁ pt₂
    σ₂₃ = is-contr→is-prop E₄c pt₂ pt₃
    σ₁₄ = is-contr→is-prop E₄c pt₁ pt₄
    σ₄₅ = is-contr→is-prop E₄c pt₄ pt₅
    σ₃₅ = is-contr→is-prop E₄c pt₃ pt₅

    α₁₂ = ap fst σ₁₂
    α₂₃ = ap fst σ₂₃
    α₁₄ = ap fst σ₁₄
    α₄₅ = ap fst σ₄₅
    α₃₅ = ap fst σ₃₅

    Λk : fiber emb (E₃ f g h) → fiber emb E₄
    Λk (m , p) = m ⨾ k , emb-comp m k ∙ ap (_· k) p

    Φ : composite y v → composite x v
    Φ L γ = emb f (γ .fst , (γ .snd .fst , L (ctr y , γ .snd)))

    Λf : fiber emb (E₃ g h k) → fiber emb E₄
    Λf (m , p) = f ⨾ m , emb-comp f m ∙ ap Φ p

    R₂₃ : fiber emb (E₃ f (g ⨾ h) k) → fiber emb E₄
    R₂₃ (m , p) = m , p ∙ ap (_· k) (·-comp (emb f) g h)

    R₄₅ : fiber emb (E₃ f g (h ⨾ k)) → fiber emb E₄
    R₄₅ (m , p) = m , p ∙ ·-comp (emb f · g) h k

    R₁₄ : fiber emb (E₃ (f ⨾ g) h k) → fiber emb E₄
    R₁₄ (m , p) = m , p ∙ ap (_· k) (ap (_· h) (emb-comp f g))

    face₁₂ : α₁₂ ≡ ap (_⨾ k) (assoc f g h)
    face₁₂ = contr-face E₄c σ₁₂ w₁₂ (λ i → Λk (assoc-σ f g h i)) v₁₂
      where
        w₁₂ : pt₁ .snd ≡ (Λk (pt-l f g h)) .snd
        w₁₂ = sym (ap (emb-comp ((f ⨾ g) ⨾ h) k ∙_)
          (ap-comp (_· k) (emb-comp (f ⨾ g) h) (ap (_· h) (emb-comp f g))))
        v₁₂ : (Λk (pt-r f g h)) .snd ≡ pt₂ .snd
        v₁₂ = ap (emb-comp (f ⨾ (g ⨾ h)) k ∙_)
          (ap-comp (_· k) (emb-comp f (g ⨾ h)) (·-comp (emb f) g h))

    face₃₅ : α₃₅ ≡ ap (f ⨾_) (assoc g h k)
    face₃₅ = contr-face E₄c σ₃₅ w₃₅ (λ i → Λf (assoc-σ g h k i)) v₃₅
      where
        w₃₅ : pt₃ .snd ≡ (Λf (pt-l g h k)) .snd
        w₃₅ = ap (emb-comp f ((g ⨾ h) ⨾ k) ∙_)
          (sym (ap-comp Φ (emb-comp (g ⨾ h) k) (ap (_· k) (emb-comp g h))))
        v₃₅ : (Λf (pt-r g h k)) .snd ≡ pt₅ .snd
        v₃₅ = ap (emb-comp f (g ⨾ (h ⨾ k)) ∙_)
          (ap-comp Φ (emb-comp g (h ⨾ k)) (·-comp (emb g) h k))

    face₂₃ : α₂₃ ≡ assoc f (g ⨾ h) k
    face₂₃ = contr-face E₄c σ₂₃ w₂₃ (λ i → R₂₃ (assoc-σ f (g ⨾ h) k i)) v₂₃
      where
        w₂₃ : pt₂ .snd ≡ (R₂₃ (pt-l f (g ⨾ h) k)) .snd
        w₂₃ = Path.assoc (emb-comp (f ⨾ (g ⨾ h)) k)
          (ap (_· k) (emb-comp f (g ⨾ h))) (ap (_· k) (·-comp (emb f) g h))
        v₂₃ : (R₂₃ (pt-r f (g ⨾ h) k)) .snd ≡ pt₃ .snd
        v₂₃ = sym (Path.assoc (emb-comp f ((g ⨾ h) ⨾ k))
          (·-comp (emb f) (g ⨾ h) k) (ap (_· k) (·-comp (emb f) g h)))

    face₄₅ : α₄₅ ≡ assoc f g (h ⨾ k)
    face₄₅ = contr-face E₄c σ₄₅ w₄₅ (λ i → R₄₅ (assoc-σ f g (h ⨾ k) i)) v₄₅
      where
        w₄₅ : pt₄ .snd ≡ (R₄₅ (pt-l f g (h ⨾ k))) .snd
        w₄₅ = Path.assoc (emb-comp (f ⨾ g) (h ⨾ k))
          (ap (_· (h ⨾ k)) (emb-comp f g)) (·-comp (emb f · g) h k)
        v₄₅ : (R₄₅ (pt-r f g (h ⨾ k))) .snd ≡ pt₅ .snd
        v₄₅ = sym (Path.assoc (emb-comp f (g ⨾ (h ⨾ k)))
          (·-comp (emb f) g (h ⨾ k)) (·-comp (emb f · g) h k))

    face₁₄ : α₁₄ ≡ assoc (f ⨾ g) h k
    face₁₄ = contr-face E₄c σ₁₄ w₁₄ (λ i → R₁₄ (assoc-σ (f ⨾ g) h k i)) v₁₄
      where
        w₁₄ : pt₁ .snd ≡ (R₁₄ (pt-l (f ⨾ g) h k)) .snd
        w₁₄ = Path.assoc (emb-comp ((f ⨾ g) ⨾ h) k)
          (ap (_· k) (emb-comp (f ⨾ g) h))
          (ap (_· k) (ap (_· h) (emb-comp f g)))
        v₁₄ : (R₁₄ (pt-r (f ⨾ g) h k)) .snd ≡ pt₄ .snd
        v₁₄ = sym (Path.assoc A₁₄ N₁₄ C₁₄) ∙ ap (A₁₄ ∙_) nat₁₄
          where
            A₁₄ = emb-comp (f ⨾ g) (h ⨾ k)
            N₁₄ = ·-comp (emb (f ⨾ g)) h k
            C₁₄ = ap (_· k) (ap (_· h) (emb-comp f g))
            nat₁₄ = sym (homotopy-natural (λ F → ·-comp F h k) (emb-comp f g))

    hom-identity : α₁₄ ∙ α₄₅ ≡ pcom (sym α₁₂) α₂₃ α₃₅
    hom-identity =
      coh-project E₄c fst (σ₁₄ ∙ σ₄₅) (pcom (sym σ₁₂) σ₂₃ σ₃₅)
        (ap-comp fst σ₁₄ σ₄₅)
        (pcom.ap (λ _ → fst) (sym σ₁₂) σ₂₃ σ₃₅)

    pentagon
      : assoc (f ⨾ g) h k ∙ assoc f g (h ⨾ k)
      ≡ ap (_⨾ k) (assoc f g h)
        ∙ assoc f (g ⨾ h) k
        ∙ ap (f ⨾_) (assoc g h k)
    pentagon =
      pcom (ap (_∙ α₄₅) face₁₄ ∙ ap (assoc (f ⨾ g) h k ∙_) face₄₅)
        hom-identity
        (λ i → pcom (sym (face₁₂ i)) (face₂₃ i) (face₃₅ i))
      ∙ pcom→∙
          (ap (_⨾ k) (assoc f g h))
          (assoc f (g ⨾ h) k)
          (ap (f ⨾_) (assoc g h k))
```

## Stage 1 — reindex faces via `pcom.catr`; binary pt-ends (K1)

**KILL K1 (confirmed).** With the four reindex snd-bridges rerouted to
`pcom.catr` but the `ptᵢ.snd` kept in binary 3-segment form, the very
first reindex bridge (`w₂₃`) fails to typecheck. `pcom.catr A B C` has
type `pcom (sym A) B C ≡ (A ∙ B) ∙ C`; its RHS `(A ∙ B) ∙ C` does match
`R₂₃ (pt-l …) .snd` definitionally, but its LHS `pcom (sym A) B C` does
NOT match the binary `pt₂ .snd = A ∙ (B ∙ C)`. The verbatim error was:

    error: [UnequalTerms]
    The terms
      compose-contr _ k .center .snd (~ i) γ
    and
      emb _ γ
    are not equal at type hom (γ .fst .fst) (γ .snd .fst)
    when checking that the expression
    pcom.catr (emb-comp (f ⨾ g ⨾ h₁) k)
      (ap (_· k) (emb-comp f (g ⨾ h₁)))
        (ap (_· k) (·-comp (emb f) g h₁))
    has type pt₂ .snd ≡ R₂₃ (pt-l f (g ⨾ h₁) k) .snd

Per K1, we do not patch with an extra `∙` — the fix is structural
(carry the endpoints in native `pcom` form), which is exactly Stage 2.
The module below is preserved verbatim in a non-checked fence for the
record; only the reindex snd-bridges differ from `baseline`.

```text
-- Stage 1 changed ONLY the reindex snd-bridges (Path.assoc → pcom.catr)
-- inside `baseline`; every other line is identical to `baseline`. The
-- four reindex bridges it substituted were:
--
--   w₂₃ = pcom.catr (emb-comp (f ⨾ (g ⨾ h)) k)
--           (ap (_· k) (emb-comp f (g ⨾ h)))
--           (ap (_· k) (·-comp (emb f) g h))
--   v₂₃ = sym (pcom.catr (emb-comp f ((g ⨾ h) ⨾ k))
--           (·-comp (emb f) (g ⨾ h) k) (ap (_· k) (·-comp (emb f) g h)))
--   w₄₅ = pcom.catr (emb-comp (f ⨾ g) (h ⨾ k))
--           (ap (_· (h ⨾ k)) (emb-comp f g)) (·-comp (emb f · g) h k)
--   v₄₅ = sym (pcom.catr (emb-comp f (g ⨾ (h ⨾ k)))
--           (·-comp (emb f) g (h ⨾ k)) (·-comp (emb f · g) h k))
--   w₁₄ = pcom.catr (emb-comp ((f ⨾ g) ⨾ h) k)
--           (ap (_· k) (emb-comp (f ⨾ g) h))
--           (ap (_· k) (ap (_· h) (emb-comp f g)))
--   v₁₄ = sym (pcom.catr A₁₄ N₁₄ C₁₄) ∙ ap (A₁₄ ∙_) nat₁₄
--
-- Typechecking halts at the FIRST reindex bridge (w₂₃) with the
-- [UnequalTerms] error quoted above: the binary pt₂.snd = A ∙ (B ∙ C)
-- does not match pcom.catr's LHS pcom (sym A) B C. KILL K1 — reindex
-- via catr is impossible while the pt-endpoints stay binary.
```

## Stage 2 — pt-endpoints native `pcom`; reindex via `catr` (K2 gate)

All five `ptᵢ.snd` carry the native ternary `pcom (sym s1) s2 s3` form.
Reindex faces now typecheck through `pcom.catr` (its LHS is the pt's
literal form). Whisker faces each pay a `+1` `pcom→∙` reconciliation
(prepended on `w`, appended on `v`) to bridge the pcom endpoint against
the `Λ`-lift's right-nested binary form — see the K2 analysis note.

```agda
module stage2 {o h} (C : hcategory o h) where
  open hcategory C

  E₃ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w) → composite x w
  E₃ f g h = emb f · g · h

  pt-l : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
       → fiber emb (E₃ f g h)
  pt-l f g h = (f ⨾ g) ⨾ h , emb-comp (f ⨾ g) h ∙ ap (_· h) (emb-comp f g)

  pt-r : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
       → fiber emb (E₃ f g h)
  pt-r f g h = f ⨾ (g ⨾ h) , emb-comp f (g ⨾ h) ∙ ·-comp (emb f) g h

  E₃-contr : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
           → is-contr (fiber emb (E₃ f g h))
  E₃-contr f g h .center = pt-l f g h
  E₃-contr f g h .paths =
    is-contr→is-prop
      (subst (λ T → is-contr (fiber emb T))
        (ap (_· h) (emb-comp f g))
        (compose-contr (f ⨾ g) h)) _

  assoc-σ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
          → pt-l f g h ≡ pt-r f g h
  assoc-σ f g h = is-contr→is-prop (E₃-contr f g h) (pt-l f g h) (pt-r f g h)

  assoc : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
        → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h = ap fst (assoc-σ f g h)

  module _ {x y z w v}
    (f : hom x y) (g : hom y z) (h : hom z w) (k : hom w v) where

    E₄ : composite x v
    E₄ = emb f · g · h · k

    E₄c : is-contr (fiber emb E₄)
    E₄c .center .fst = ((f ⨾ g) ⨾ h) ⨾ k
    E₄c .center .snd =
        emb-comp ((f ⨾ g) ⨾ h) k
      ∙ ap (_· k) (emb-comp (f ⨾ g) h)
      ∙ ap (_· k) (ap (_· h) (emb-comp f g))
    E₄c .paths =
      is-contr→is-prop
        (subst (λ T → is-contr (fiber emb T)) path₄
          (compose-contr ((f ⨾ g) ⨾ h) k)) _
      where
        path₄ : emb ((f ⨾ g) ⨾ h) · k ≡ E₄
        path₄ = ap (_· k) (emb-comp (f ⨾ g) h)
              ∙ ap (_· k) (ap (_· h) (emb-comp f g))

    -- Native ternary pt-endpoints: pcom (sym s1) s2 s3.
    pt₁ : fiber emb E₄
    pt₁ = ((f ⨾ g) ⨾ h) ⨾ k
        , pcom (sym (emb-comp ((f ⨾ g) ⨾ h) k))
            (ap (_· k) (emb-comp (f ⨾ g) h))
            (ap (_· k) (ap (_· h) (emb-comp f g)))

    pt₂ : fiber emb E₄
    pt₂ = (f ⨾ (g ⨾ h)) ⨾ k
        , pcom (sym (emb-comp (f ⨾ (g ⨾ h)) k))
            (ap (_· k) (emb-comp f (g ⨾ h)))
            (ap (_· k) (·-comp (emb f) g h))

    pt₃ : fiber emb E₄
    pt₃ = f ⨾ ((g ⨾ h) ⨾ k)
        , pcom (sym (emb-comp f ((g ⨾ h) ⨾ k)))
            (·-comp (emb f) (g ⨾ h) k)
            (ap (_· k) (·-comp (emb f) g h))

    pt₄ : fiber emb E₄
    pt₄ = (f ⨾ g) ⨾ (h ⨾ k)
        , pcom (sym (emb-comp (f ⨾ g) (h ⨾ k)))
            (ap (_· (h ⨾ k)) (emb-comp f g))
            (·-comp (emb f · g) h k)

    pt₅ : fiber emb E₄
    pt₅ = f ⨾ (g ⨾ (h ⨾ k))
        , pcom (sym (emb-comp f (g ⨾ (h ⨾ k))))
            (·-comp (emb f) g (h ⨾ k))
            (·-comp (emb f · g) h k)

    σ₁₂ = is-contr→is-prop E₄c pt₁ pt₂
    σ₂₃ = is-contr→is-prop E₄c pt₂ pt₃
    σ₁₄ = is-contr→is-prop E₄c pt₁ pt₄
    σ₄₅ = is-contr→is-prop E₄c pt₄ pt₅
    σ₃₅ = is-contr→is-prop E₄c pt₃ pt₅

    α₁₂ = ap fst σ₁₂
    α₂₃ = ap fst σ₂₃
    α₁₄ = ap fst σ₁₄
    α₄₅ = ap fst σ₄₅
    α₃₅ = ap fst σ₃₅

    Λk : fiber emb (E₃ f g h) → fiber emb E₄
    Λk (m , p) = m ⨾ k , emb-comp m k ∙ ap (_· k) p

    Φ : composite y v → composite x v
    Φ L γ = emb f (γ .fst , (γ .snd .fst , L (ctr y , γ .snd)))

    Λf : fiber emb (E₃ g h k) → fiber emb E₄
    Λf (m , p) = f ⨾ m , emb-comp f m ∙ ap Φ p

    R₂₃ : fiber emb (E₃ f (g ⨾ h) k) → fiber emb E₄
    R₂₃ (m , p) = m , p ∙ ap (_· k) (·-comp (emb f) g h)

    R₄₅ : fiber emb (E₃ f g (h ⨾ k)) → fiber emb E₄
    R₄₅ (m , p) = m , p ∙ ·-comp (emb f · g) h k

    R₁₄ : fiber emb (E₃ (f ⨾ g) h k) → fiber emb E₄
    R₁₄ (m , p) = m , p ∙ ap (_· k) (ap (_· h) (emb-comp f g))

    -- Whisker face: pcom endpoint → +1 pcom→∙ (prepend on w, append on v).
    face₁₂ : α₁₂ ≡ ap (_⨾ k) (assoc f g h)
    face₁₂ = contr-face E₄c σ₁₂ w₁₂ (λ i → Λk (assoc-σ f g h i)) v₁₂
      where
        w₁₂ : pt₁ .snd ≡ (Λk (pt-l f g h)) .snd
        w₁₂ = pcom→∙ (emb-comp ((f ⨾ g) ⨾ h) k)
                (ap (_· k) (emb-comp (f ⨾ g) h))
                (ap (_· k) (ap (_· h) (emb-comp f g)))
            ∙ sym (ap (emb-comp ((f ⨾ g) ⨾ h) k ∙_)
                (ap-comp (_· k) (emb-comp (f ⨾ g) h)
                  (ap (_· h) (emb-comp f g))))
        v₁₂ : (Λk (pt-r f g h)) .snd ≡ pt₂ .snd
        v₁₂ = ap (emb-comp (f ⨾ (g ⨾ h)) k ∙_)
                (ap-comp (_· k) (emb-comp f (g ⨾ h)) (·-comp (emb f) g h))
            ∙ sym (pcom→∙ (emb-comp (f ⨾ (g ⨾ h)) k)
                (ap (_· k) (emb-comp f (g ⨾ h)))
                (ap (_· k) (·-comp (emb f) g h)))

    face₃₅ : α₃₅ ≡ ap (f ⨾_) (assoc g h k)
    face₃₅ = contr-face E₄c σ₃₅ w₃₅ (λ i → Λf (assoc-σ g h k i)) v₃₅
      where
        w₃₅ : pt₃ .snd ≡ (Λf (pt-l g h k)) .snd
        w₃₅ = pcom→∙ (emb-comp f ((g ⨾ h) ⨾ k))
                (·-comp (emb f) (g ⨾ h) k)
                (ap (_· k) (·-comp (emb f) g h))
            ∙ ap (emb-comp f ((g ⨾ h) ⨾ k) ∙_)
                (sym (ap-comp Φ (emb-comp (g ⨾ h) k)
                  (ap (_· k) (emb-comp g h))))
        v₃₅ : (Λf (pt-r g h k)) .snd ≡ pt₅ .snd
        v₃₅ = ap (emb-comp f (g ⨾ (h ⨾ k)) ∙_)
                (ap-comp Φ (emb-comp g (h ⨾ k)) (·-comp (emb g) h k))
            ∙ sym (pcom→∙ (emb-comp f (g ⨾ (h ⨾ k)))
                (·-comp (emb f) g (h ⨾ k))
                (·-comp (emb f · g) h k))

    -- Reindex face: pcom endpoint matches catr's LHS literally (1 atom).
    face₂₃ : α₂₃ ≡ assoc f (g ⨾ h) k
    face₂₃ = contr-face E₄c σ₂₃ w₂₃ (λ i → R₂₃ (assoc-σ f (g ⨾ h) k i)) v₂₃
      where
        w₂₃ : pt₂ .snd ≡ (R₂₃ (pt-l f (g ⨾ h) k)) .snd
        w₂₃ = pcom.catr (emb-comp (f ⨾ (g ⨾ h)) k)
          (ap (_· k) (emb-comp f (g ⨾ h))) (ap (_· k) (·-comp (emb f) g h))
        v₂₃ : (R₂₃ (pt-r f (g ⨾ h) k)) .snd ≡ pt₃ .snd
        v₂₃ = sym (pcom.catr (emb-comp f ((g ⨾ h) ⨾ k))
          (·-comp (emb f) (g ⨾ h) k) (ap (_· k) (·-comp (emb f) g h)))

    face₄₅ : α₄₅ ≡ assoc f g (h ⨾ k)
    face₄₅ = contr-face E₄c σ₄₅ w₄₅ (λ i → R₄₅ (assoc-σ f g (h ⨾ k) i)) v₄₅
      where
        w₄₅ : pt₄ .snd ≡ (R₄₅ (pt-l f g (h ⨾ k))) .snd
        w₄₅ = pcom.catr (emb-comp (f ⨾ g) (h ⨾ k))
          (ap (_· (h ⨾ k)) (emb-comp f g)) (·-comp (emb f · g) h k)
        v₄₅ : (R₄₅ (pt-r f g (h ⨾ k))) .snd ≡ pt₅ .snd
        v₄₅ = sym (pcom.catr (emb-comp f (g ⨾ (h ⨾ k)))
          (·-comp (emb f) g (h ⨾ k)) (·-comp (emb f · g) h k))

    face₁₄ : α₁₄ ≡ assoc (f ⨾ g) h k
    face₁₄ = contr-face E₄c σ₁₄ w₁₄ (λ i → R₁₄ (assoc-σ (f ⨾ g) h k i)) v₁₄
      where
        w₁₄ : pt₁ .snd ≡ (R₁₄ (pt-l (f ⨾ g) h k)) .snd
        w₁₄ = pcom.catr (emb-comp ((f ⨾ g) ⨾ h) k)
          (ap (_· k) (emb-comp (f ⨾ g) h))
          (ap (_· k) (ap (_· h) (emb-comp f g)))
        -- face₁₄'s nat tail resists `catr`: the tail needs the binary
        -- intermediate A₁₄ ∙ (N₁₄ ∙ C₁₄) — that is `Path.assoc`'s LHS,
        -- NOT `catr`'s pcom LHS. So the reassociation stays `Path.assoc`
        -- and the native pcom endpoint is reached by a trailing pcom→∙.
        v₁₄ : (R₁₄ (pt-r (f ⨾ g) h k)) .snd ≡ pt₄ .snd
        v₁₄ = sym (Path.assoc A₁₄ N₁₄ C₁₄) ∙ ap (A₁₄ ∙_) nat₁₄
            ∙ sym (pcom→∙ A₁₄ B₄ D₄)
          where
            A₁₄ = emb-comp (f ⨾ g) (h ⨾ k)
            N₁₄ = ·-comp (emb (f ⨾ g)) h k
            C₁₄ = ap (_· k) (ap (_· h) (emb-comp f g))
            B₄ = ap (_· (h ⨾ k)) (emb-comp f g)
            D₄ = ·-comp (emb f · g) h k
            nat₁₄ = sym (homotopy-natural (λ F → ·-comp F h k) (emb-comp f g))

    hom-identity : α₁₄ ∙ α₄₅ ≡ pcom (sym α₁₂) α₂₃ α₃₅
    hom-identity =
      coh-project E₄c fst (σ₁₄ ∙ σ₄₅) (pcom (sym σ₁₂) σ₂₃ σ₃₅)
        (ap-comp fst σ₁₄ σ₄₅)
        (pcom.ap (λ _ → fst) (sym σ₁₂) σ₂₃ σ₃₅)

    pentagon
      : assoc (f ⨾ g) h k ∙ assoc f g (h ⨾ k)
      ≡ ap (_⨾ k) (assoc f g h)
        ∙ assoc f (g ⨾ h) k
        ∙ ap (f ⨾_) (assoc g h k)
    pentagon =
      pcom (ap (_∙ α₄₅) face₁₄ ∙ ap (assoc (f ⨾ g) h k ∙_) face₄₅)
        hom-identity
        (λ i → pcom (sym (face₁₂ i)) (face₂₃ i) (face₃₅ i))
      ∙ pcom→∙
          (ap (_⨾ k) (assoc f g h))
          (assoc f (g ⨾ h) k)
          (ap (f ⨾_) (assoc g h k))
```

## Stage 3 — scaffold helpers on the K2 survivor (stage2)

Two local helpers factor the face boilerplate. `reindex-face` cleanly
handles face₂₃/face₄₅ (pure `catr` on both bridges). `whisker-face`
factors the `contr-face` + `Λ`-core skeleton for face₁₂/face₃₅ (the
`+1` `pcom→∙` bridges stay caller-side — their `s1 s2 s3` segment types
depend on the face and resist being hidden without fragile inference).
face₁₄ stays bespoke: its naturality tail forbids the uniform `catr`
(K3, expected).

```agda
module stage3 {o h} (C : hcategory o h) where
  open hcategory C

  E₃ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w) → composite x w
  E₃ f g h = emb f · g · h

  pt-l : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
       → fiber emb (E₃ f g h)
  pt-l f g h = (f ⨾ g) ⨾ h , emb-comp (f ⨾ g) h ∙ ap (_· h) (emb-comp f g)

  pt-r : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
       → fiber emb (E₃ f g h)
  pt-r f g h = f ⨾ (g ⨾ h) , emb-comp f (g ⨾ h) ∙ ·-comp (emb f) g h

  E₃-contr : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
           → is-contr (fiber emb (E₃ f g h))
  E₃-contr f g h .center = pt-l f g h
  E₃-contr f g h .paths =
    is-contr→is-prop
      (subst (λ T → is-contr (fiber emb T))
        (ap (_· h) (emb-comp f g))
        (compose-contr (f ⨾ g) h)) _

  assoc-σ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
          → pt-l f g h ≡ pt-r f g h
  assoc-σ f g h = is-contr→is-prop (E₃-contr f g h) (pt-l f g h) (pt-r f g h)

  assoc : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
        → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
  assoc f g h = ap fst (assoc-σ f g h)

  module _ {x y z w v}
    (f : hom x y) (g : hom y z) (h : hom z w) (k : hom w v) where

    E₄ : composite x v
    E₄ = emb f · g · h · k

    E₄c : is-contr (fiber emb E₄)
    E₄c .center .fst = ((f ⨾ g) ⨾ h) ⨾ k
    E₄c .center .snd =
        emb-comp ((f ⨾ g) ⨾ h) k
      ∙ ap (_· k) (emb-comp (f ⨾ g) h)
      ∙ ap (_· k) (ap (_· h) (emb-comp f g))
    E₄c .paths =
      is-contr→is-prop
        (subst (λ T → is-contr (fiber emb T)) path₄
          (compose-contr ((f ⨾ g) ⨾ h) k)) _
      where
        path₄ : emb ((f ⨾ g) ⨾ h) · k ≡ E₄
        path₄ = ap (_· k) (emb-comp (f ⨾ g) h)
              ∙ ap (_· k) (ap (_· h) (emb-comp f g))

    pt₁ : fiber emb E₄
    pt₁ = ((f ⨾ g) ⨾ h) ⨾ k
        , pcom (sym (emb-comp ((f ⨾ g) ⨾ h) k))
            (ap (_· k) (emb-comp (f ⨾ g) h))
            (ap (_· k) (ap (_· h) (emb-comp f g)))

    pt₂ : fiber emb E₄
    pt₂ = (f ⨾ (g ⨾ h)) ⨾ k
        , pcom (sym (emb-comp (f ⨾ (g ⨾ h)) k))
            (ap (_· k) (emb-comp f (g ⨾ h)))
            (ap (_· k) (·-comp (emb f) g h))

    pt₃ : fiber emb E₄
    pt₃ = f ⨾ ((g ⨾ h) ⨾ k)
        , pcom (sym (emb-comp f ((g ⨾ h) ⨾ k)))
            (·-comp (emb f) (g ⨾ h) k)
            (ap (_· k) (·-comp (emb f) g h))

    pt₄ : fiber emb E₄
    pt₄ = (f ⨾ g) ⨾ (h ⨾ k)
        , pcom (sym (emb-comp (f ⨾ g) (h ⨾ k)))
            (ap (_· (h ⨾ k)) (emb-comp f g))
            (·-comp (emb f · g) h k)

    pt₅ : fiber emb E₄
    pt₅ = f ⨾ (g ⨾ (h ⨾ k))
        , pcom (sym (emb-comp f (g ⨾ (h ⨾ k))))
            (·-comp (emb f) g (h ⨾ k))
            (·-comp (emb f · g) h k)

    σ₁₂ = is-contr→is-prop E₄c pt₁ pt₂
    σ₂₃ = is-contr→is-prop E₄c pt₂ pt₃
    σ₁₄ = is-contr→is-prop E₄c pt₁ pt₄
    σ₄₅ = is-contr→is-prop E₄c pt₄ pt₅
    σ₃₅ = is-contr→is-prop E₄c pt₃ pt₅

    α₁₂ = ap fst σ₁₂
    α₂₃ = ap fst σ₂₃
    α₁₄ = ap fst σ₁₄
    α₄₅ = ap fst σ₄₅
    α₃₅ = ap fst σ₃₅

    Λk : fiber emb (E₃ f g h) → fiber emb E₄
    Λk (m , p) = m ⨾ k , emb-comp m k ∙ ap (_· k) p

    Φ : composite y v → composite x v
    Φ L γ = emb f (γ .fst , (γ .snd .fst , L (ctr y , γ .snd)))

    Λf : fiber emb (E₃ g h k) → fiber emb E₄
    Λf (m , p) = f ⨾ m , emb-comp f m ∙ ap Φ p

    -- reindex-face: pure-reindex faces (both bridges are catr). Given the
    -- sub-triple f' g' h' and the tail C : E₃ f' g' h' ≡ E₄, the whole
    -- face is one application; the reindex lift R (m , p) = (m , p ∙ C)
    -- is built internally.
    reindex-face
      : ∀ {y' z'} (f' : hom x y') (g' : hom y' z') (h' : hom z' v)
        (C : E₃ f' g' h' ≡ E₄)
        (σ : (((f' ⨾ g') ⨾ h')
                 , pcom (sym (emb-comp (f' ⨾ g') h'))
                     (ap (_· h') (emb-comp f' g')) C)
           ≡ ((f' ⨾ (g' ⨾ h'))
                 , pcom (sym (emb-comp f' (g' ⨾ h')))
                     (·-comp (emb f') g' h') C))
      → ap fst σ ≡ assoc f' g' h'
    reindex-face f' g' h' C σ =
      contr-face E₄c σ
        (pcom.catr (emb-comp (f' ⨾ g') h') (ap (_· h') (emb-comp f' g')) C)
        (λ i → R (assoc-σ f' g' h' i))
        (sym (pcom.catr (emb-comp f' (g' ⨾ h')) (·-comp (emb f') g' h') C))
      where
        R : fiber emb (E₃ f' g' h') → fiber emb E₄
        R (m , p) = m , p ∙ C

    -- whisker-face: factors the contr-face + Λ-core skeleton for a
    -- single-whisker face. The caller supplies the two bridges w and v
    -- (each carrying its own +1 pcom→∙ reconciliation — those cannot be
    -- hidden here without face-specific segment plumbing).
    whisker-face
      : ∀ {x₀ y₀ z₀ w₀}
        (p : hom x₀ y₀) (q : hom y₀ z₀) (r : hom z₀ w₀)
        (Λ : fiber emb (E₃ p q r) → fiber emb E₄)
        {α : emb (Λ (pt-l p q r) .fst) ≡ E₄}
        {β : emb (Λ (pt-r p q r) .fst) ≡ E₄}
        (σ : (Λ (pt-l p q r) .fst , α) ≡ (Λ (pt-r p q r) .fst , β))
        (w : α ≡ Λ (pt-l p q r) .snd)
        (v : Λ (pt-r p q r) .snd ≡ β)
      → ap fst σ ≡ ap fst (λ i → Λ (assoc-σ p q r i))
    whisker-face p q r Λ σ w v =
      contr-face E₄c σ w (λ i → Λ (assoc-σ p q r i)) v

    -- face₁₂/face₃₅: whisker faces through whisker-face.
    face₁₂ : α₁₂ ≡ ap (_⨾ k) (assoc f g h)
    face₁₂ = whisker-face f g h Λk σ₁₂ w₁₂ v₁₂
      where
        w₁₂ : pt₁ .snd ≡ (Λk (pt-l f g h)) .snd
        w₁₂ = pcom→∙ (emb-comp ((f ⨾ g) ⨾ h) k)
                (ap (_· k) (emb-comp (f ⨾ g) h))
                (ap (_· k) (ap (_· h) (emb-comp f g)))
            ∙ sym (ap (emb-comp ((f ⨾ g) ⨾ h) k ∙_)
                (ap-comp (_· k) (emb-comp (f ⨾ g) h)
                  (ap (_· h) (emb-comp f g))))
        v₁₂ : (Λk (pt-r f g h)) .snd ≡ pt₂ .snd
        v₁₂ = ap (emb-comp (f ⨾ (g ⨾ h)) k ∙_)
                (ap-comp (_· k) (emb-comp f (g ⨾ h)) (·-comp (emb f) g h))
            ∙ sym (pcom→∙ (emb-comp (f ⨾ (g ⨾ h)) k)
                (ap (_· k) (emb-comp f (g ⨾ h)))
                (ap (_· k) (·-comp (emb f) g h)))

    face₃₅ : α₃₅ ≡ ap (f ⨾_) (assoc g h k)
    face₃₅ = whisker-face g h k Λf σ₃₅ w₃₅ v₃₅
      where
        w₃₅ : pt₃ .snd ≡ (Λf (pt-l g h k)) .snd
        w₃₅ = pcom→∙ (emb-comp f ((g ⨾ h) ⨾ k))
                (·-comp (emb f) (g ⨾ h) k)
                (ap (_· k) (·-comp (emb f) g h))
            ∙ ap (emb-comp f ((g ⨾ h) ⨾ k) ∙_)
                (sym (ap-comp Φ (emb-comp (g ⨾ h) k)
                  (ap (_· k) (emb-comp g h))))
        v₃₅ : (Λf (pt-r g h k)) .snd ≡ pt₅ .snd
        v₃₅ = ap (emb-comp f (g ⨾ (h ⨾ k)) ∙_)
                (ap-comp Φ (emb-comp g (h ⨾ k)) (·-comp (emb g) h k))
            ∙ sym (pcom→∙ (emb-comp f (g ⨾ (h ⨾ k)))
                (·-comp (emb f) g (h ⨾ k))
                (·-comp (emb f · g) h k))

    -- face₂₃/face₄₅: pure reindex through reindex-face — one-liners.
    face₂₃ : α₂₃ ≡ assoc f (g ⨾ h) k
    face₂₃ = reindex-face f (g ⨾ h) k (ap (_· k) (·-comp (emb f) g h)) σ₂₃

    face₄₅ : α₄₅ ≡ assoc f g (h ⨾ k)
    face₄₅ = reindex-face f g (h ⨾ k) (·-comp (emb f · g) h k) σ₄₅

    -- face₁₄: bespoke (K3). The naturality tail needs the binary
    -- intermediate, so the reassociation stays Path.assoc and the native
    -- pcom endpoint is reached by a trailing pcom→∙.
    R₁₄ : fiber emb (E₃ (f ⨾ g) h k) → fiber emb E₄
    R₁₄ (m , p) = m , p ∙ ap (_· k) (ap (_· h) (emb-comp f g))

    face₁₄ : α₁₄ ≡ assoc (f ⨾ g) h k
    face₁₄ = contr-face E₄c σ₁₄ w₁₄ (λ i → R₁₄ (assoc-σ (f ⨾ g) h k i)) v₁₄
      where
        w₁₄ : pt₁ .snd ≡ (R₁₄ (pt-l (f ⨾ g) h k)) .snd
        w₁₄ = pcom.catr (emb-comp ((f ⨾ g) ⨾ h) k)
          (ap (_· k) (emb-comp (f ⨾ g) h))
          (ap (_· k) (ap (_· h) (emb-comp f g)))
        v₁₄ : (R₁₄ (pt-r (f ⨾ g) h k)) .snd ≡ pt₄ .snd
        v₁₄ = sym (Path.assoc A₁₄ N₁₄ C₁₄) ∙ ap (A₁₄ ∙_) nat₁₄
            ∙ sym (pcom→∙ A₁₄ B₄ D₄)
          where
            A₁₄ = emb-comp (f ⨾ g) (h ⨾ k)
            N₁₄ = ·-comp (emb (f ⨾ g)) h k
            C₁₄ = ap (_· k) (ap (_· h) (emb-comp f g))
            B₄ = ap (_· (h ⨾ k)) (emb-comp f g)
            D₄ = ·-comp (emb f · g) h k
            nat₁₄ = sym (homotopy-natural (λ F → ·-comp F h k) (emb-comp f g))

    hom-identity : α₁₄ ∙ α₄₅ ≡ pcom (sym α₁₂) α₂₃ α₃₅
    hom-identity =
      coh-project E₄c fst (σ₁₄ ∙ σ₄₅) (pcom (sym σ₁₂) σ₂₃ σ₃₅)
        (ap-comp fst σ₁₄ σ₄₅)
        (pcom.ap (λ _ → fst) (sym σ₁₂) σ₂₃ σ₃₅)

    pentagon
      : assoc (f ⨾ g) h k ∙ assoc f g (h ⨾ k)
      ≡ ap (_⨾ k) (assoc f g h)
        ∙ assoc f (g ⨾ h) k
        ∙ ap (f ⨾_) (assoc g h k)
    pentagon =
      pcom (ap (_∙ α₄₅) face₁₄ ∙ ap (assoc (f ⨾ g) h k ∙_) face₄₅)
        hom-identity
        (λ i → pcom (sym (face₁₂ i)) (face₂₃ i) (face₃₅ i))
      ∙ pcom→∙
          (ap (_⨾ k) (assoc f g h))
          (assoc f (g ⨾ h) k)
          (ap (f ⨾_) (assoc g h k))
```
