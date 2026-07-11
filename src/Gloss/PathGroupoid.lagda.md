Gloss: machine-checked evidence for T18, T13(i) in docs/theorems.md.
Self-contained modulo Core.*; Cat.* definitions frozen at 9133396.

Bounded SPIKE — path-groupoid instance of `hcategory` over an
abstract type, plus the level-2 coherence rungs and membership
diagnosis, checked by concrete path algebra.

The carrier: `ob := A`, `hom x y := x ≡ y`, `idn := refl`, and the
two-sided embedding `emb f ((w , a) , (v , b)) := pcom (sym a) f b`
— the born-ternary composite `a ⁻¹-side · f · b`. `emb` is an
equivalence (its context `ctx x y` is a product of contractible
singletons), so `compose-contr` is `eqv-fibers`; the other four
axioms are pcom path algebra. This reuses the `Cat.Type` path
groupoid design (`Cat.Groupoid`, `Core.Groupoid.Virtual.repr`) but
targets the uncurried `hcategory` record of `Cat.Codep.Base`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Gloss.PathGroupoid where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Equiv.Base using (is-equiv; eqv-fibers; iso→equiv; _≃_)
open import Core.Equiv.Properties using (comp-equiv)
open import Core.Transport.J using (J; subst)
open import Core.Function.Embedding
  using ( equiv→lc; equiv→lc-section
        ; is-embedding→ap-equiv; is-equiv→is-embedding
        ; image-fibers-contr→is-embedding )
open import Core.Groupoid.Virtual using (module repr)
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

## The instance

```agda
module _ {u} (A : Type u) where

  path-structure : hcategory-structure {u} {u} A
  path-structure .hcategory-structure.hom x y = x ≡ y
  path-structure .hcategory-structure.idn x = refl
  path-structure .hcategory-structure.emb f ((w , a) , (v , b)) =
    pcom (sym a) f b

  open hcategory-structure path-structure
```

`emb` factors as `uncurryF ∘ repr.emb`, both equivalences, so `emb`
is an equivalence. `repr.emb {A = λ _ → A}` is the curried
`q ↦ λ w a v b → pcom (sym a) q b`; `uncurryF` re-associates the
context into the Σ-pair shape `emb` uses. They agree definitionally.

```agda
  emb-is-equiv : ∀ {x y} → is-equiv (emb {x} {y})
  emb-is-equiv {x} {y} =
    comp-equiv (repr.emb-equiv {A = λ _ → A} {x} {y}) uncurryF-is-equiv
    where
      Curried : Type u
      Curried = ∀ w → w ≡ x → ∀ v → y ≡ v → w ≡ v

      uncurryF : Curried → composite x y
      uncurryF g ((w , a) , (v , b)) = g w a v b

      curryF : composite x y → Curried
      curryF F w a v b = F ((w , a) , (v , b))

      uncurryF-is-equiv : is-equiv uncurryF
      uncurryF-is-equiv =
        iso→equiv uncurryF curryF (λ _ → refl) (λ _ → refl) .snd
```

The five axioms.

  * `compose-contr` — fiber of an equivalence is contractible.
  * `interchange` — `pcom.lsplit ∙ pcom.lr ∙ sym pcom.rsplit`, the
    born-ternary reassociation (routed through `pcom→∙` so the chain
    stays ternary per the house rule).
  * `post-eval` — `pcom.unit`: `pcom refl f refl ≡ f`.
  * `unit-eqvl` — `pre (idn x) b = pcom refl refl b = refl ∙ b`, so
    `Path.unitl` is the (co)homotopy.
  * `unit-eqvr` — `post (idn x) a = pcom (sym a) refl refl`, so
    `pcom.idemr` is the (co)homotopy.

```agda
  path-axioms : hcategory-axioms path-structure
  path-axioms .hcategory-axioms.compose-contr f g =
    emb-is-equiv .eqv-fibers (emb f · g)
  path-axioms .hcategory-axioms.interchange f g {w} a {v} b =
    pcom (sym (pcom.lsplit a f (pcom refl g b)))
         (pcom.lr (pcom (sym a) f refl) (pcom refl g b))
         (sym (pcom.rsplit (pcom (sym a) f refl) g b))
  path-axioms .hcategory-axioms.post-eval f = pcom.unit f
  path-axioms .hcategory-axioms.unit-eqvl {x} {v} =
    iso→equiv (pre (idn x) {v}) id Path.unitl Path.unitl .snd
  path-axioms .hcategory-axioms.unit-eqvr {x} {w} =
    iso→equiv (post (idn x) {w}) id pcom.idemr pcom.idemr .snd

  path-cat : hcategory u u
  path-cat .hcategory.ob = A
  path-cat .hcategory.structure = path-structure
  path-cat .hcategory.axioms = path-axioms
```

## Deliverable (3): membership machinery — generic over any hcategory

`kill-1` — because `pre (idn x)` is an equivalence (`unit-eqvl`),
`ap (pre (idn x))` is an equivalence, so all its fibers are
contractible. Free from `unit-eqvl`; the composite
`is-embedding→ap-equiv ∘ is-equiv→is-embedding : is-equiv f →
is-equiv (ap f)` already lives in `Core.Function.Embedding`, so no
Core gap here.

```agda
module membership {o h} (C : hcategory o h) where
  open hcategory C

  kill-1 : ∀ {x v} (w : hom x v)
           (ε : pre (idn x) (pre (idn x) w) ≡ pre (idn x) w)
         → is-contr (fiber (ap (pre (idn x))) ε)
  kill-1 {x} w ε =
    is-embedding→ap-equiv (is-equiv→is-embedding unit-eqvl) .eqv-fibers ε
```

`kill-3` — membership + `kill-1` ⇒ rung-l. Given the membership
witness `M` (that the interchange-route's image under
`ap (pre (idn y))` is the idempotency square `Qc`), the crux closes
by the `equiv→lc-section` uniqueness argument: `ap (pre (idn y))` is
injective, `ap (pre (idn y)) (absorb-l c) = Qc` by
`equiv→lc-section`, and `M` matches it against the route. This is
`CodepTriangleCrux.crux'` with its stuck residue `R-core` supplied
as the hypothesis. Fully generic.

```agda
  module _ {y z v} (g : hom y z) (b : hom z v) where
    private
      c : hom y v
      c = pre g b

      RHSl : pre (idn y) c ≡ c
      RHSl = interchange (idn y) g (idn y) b
           ∙ ap (λ a' → emb g ((y , a') , (v , b))) (post-eval (idn y))

      Qc : pre (idn y) (pre (idn y) c) ≡ pre (idn y) c
      Qc = sym (subst (λ t → pre t c ≡ pre (idn y) (pre (idn y) c))
                 idem (pre-comp (idn y) (idn y) c))

    kill-3 : ap (pre (idn y)) RHSl ≡ Qc
           → absorb-l c ≡ RHSl
    kill-3 M =
      equiv→lc (is-embedding→ap-equiv (is-equiv→is-embedding unit-eqvl))
        (equiv→lc-section unit-eqvl Qc ∙ sym M)
```

## Deliverable (4, STRETCH): inertness of `ap emb`

Since `emb` is an equivalence in the instance, `ap emb` is an
equivalence, so `fiber (ap emb) Θ` is contractible for any
`Θ : emb f ≡ emb f'`. The trap is real: paths between `emb`-images
carry no extra data.

```agda
module inert {u} {A : Type u} where
  open hcategory (path-cat A)

  ap-emb-inert
    : ∀ {x y} {f f' : hom x y} (Θ : emb f ≡ emb f')
    → is-contr (fiber (ap emb {x = f} {y = f'}) Θ)
  ap-emb-inert {x} {y} Θ =
    is-embedding→ap-equiv
      (is-equiv→is-embedding (emb-is-equiv A {x} {y})) .eqv-fibers Θ
```

## Deliverable (2): the three rungs — not closed (2-cell residues)

The three rung statements are stated below in a non-checked block.
Each is a coherence *between two paths* with coinciding endpoints; in
the path-groupoid carrier every ingredient (`interchange`,
`post-eval`, `pre`/`post`, and — via the concrete `iso→equiv`
inverses — `⨾`/`idem`/`absorb-l`/`pre-comp`) reduces to concrete
pcom/hcom terms. But none of the three closes by `refl`: each is a
genuine 2-cell reconciling an *interchange* hcom-filler against the
unit contractions.

Empirical residues (both probed with `refl`, both rejected):

  * **rung-θ** goal
    `ap (pre e) (post-eval e)
       ≡ interchange e e e e ∙ ap (post e) (post-eval e)`  (e = idn x).
    Underlying mismatch: `primHComp {φ = ~i∨i}` (LHS, one hcom)
    vs `primHComp {φ = (~i₁∨i₁)∨~i∨i}` (RHS, interchange layer added).

  * **rung-l residue** (rung-l `= kill-3 g b M`, so the content is `M`):
    `ap (pre (idn y)) RHSl ≡ Qc`, i.e.
    `primHComp {~i∨i}` vs `primHComp {(i₁∨~i₁)∨~i∨i}`. This is exactly
    the `R-core` residue `CodepTriangleCrux` found stuck *generically*
    — here fully concrete, but still a non-refl pcom 2-cell.

Analytic decomposition of **rung-θ** (the calibration data asked for).
Write `η = pcom.ideml` (`pre e ∼ id`), `ζ = pcom.idemr`
(`post e ∼ id`), `R = pcom refl refl refl`, and
`u = post-eval e : R ≡ refl`.
Two `homotopy-natural` applications give
`ap (pre e) u  = η R ∙ u ∙ sym (η refl)` and
`ap (post e) u = ζ R ∙ u ∙ sym (ζ refl)`, reducing rung-θ to the
conjunction

  (A) `interchange e e e e ≡ η R ∙ sym (ζ R)`  — the interchange
      hcom-filler equals the difference of the two unit contractions;
  (B) `pcom.ideml refl ≡ pcom.idemr refl`      — the two canonical
      contractions of `R` to `refl` agree.

(A) is the crux: it re-relates the `lsplit ∙ lr ∙ rsplit` interchange
filler to `ideml`/`idemr` and is *not* itself refl. This is the
groupoid-law bill the rung consumes: `homotopy-natural` ×2,
`Path.assoc`/`invl`/`unitr`, plus (A)+(B). The finding: even in the
maximally coherent carrier the rung is a real 2-cell — its content is
carrier-independent (matches the abstract `R-core`), confirming the
obstruction is about the *structure* (the level-2 axiom must supply
this 2-cell), not about exotic carriers.

```text
-- NON-CHECKED (documented goals; each is a non-refl 2-cell):
module rungs {u} {A : Type u} where
  open hcategory (path-cat A)
  open membership (path-cat A)

  rung-θ : ∀ {x} → let e = idn x in
      ap (pre e) (post-eval e)
    ≡ interchange e e e e ∙ ap (post e) (post-eval e)

  rung-l : ∀ {y z v} (g : hom y z) (b : hom z v)
    → absorb-l (pre g b)
    ≡ interchange (idn y) g (idn y) b
      ∙ ap (λ a' → emb g ((y , a') , (v , b))) (post-eval (idn y))
  -- rung-l g b = kill-3 g b M   with   M : ap (pre (idn y)) RHSl ≡ Qc

  rung-r : ∀ {w x y} (f : hom x y) (a : hom w x)
    → absorb-r (post f a)
    ≡ sym (interchange f (idn y) a (idn y))
      ∙ ap (λ b' → emb f ((w , a) , (y , b'))) (post-eval (idn y))
```
