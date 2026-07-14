Lane Biocini
July 2026

Gloss: machine-checked evidence for T22 in docs/gloss.md.
Self-contained modulo Core.* — no Cat.* import. The frozen blocks
carry two provenances, each named at its marker: the
representable-category core from `Cat.Codep.Base`, and the
three-layer structure with its filling from its tracked source
file, both at commit dde1f57.

## Synopsis

This certificate houses an axiomatization and a theorem about its
canonical model.

The axiomatization is a three-layer structure for "category with
families and cofamilies acting on dependent composites", stated at
full generality. `fam-structure` gives objects,
morphisms with identities and a base composition, and two abstract
carriers — a family assigned to each object, acted on
contravariantly by morphisms (`_◃_`), and a cofamily acted on
covariantly (`_▹_`) — with unit and functoriality laws for both
actions; it abstracts the dependent- and codependent-arrow
substrate of Petrakis's categories with dependent arrows.
`codep-structure` adds a result type over every context
(a pair of one cofamily element and one family element) and takes
a composite from `x` to `y` to be a dependent function assigning a
result to every context over `(x , y)`; the two morphism actions
on composites are then defined by reindexing the context, and the
layer's fields assert that the result type is invariant under each
action — stated function-valued, as maps between result types
rather than as paths of types — together with four laws making the
invariance maps unital and functorial over the family laws'
tracks. `codep-representable` adds an embedding `emb` of
morphisms into composites, contractible composition fibers
(`compose-contr`) whose centers extract a composite morphism
`_⨾_`, and an agreement axiom (`extract-agree`) identifying that
extraction with the base composition.

The theorem (`module taut`) is that every category presented by a
representable embedding — the `hcategory` record, frozen here from
`Cat.Codep.Base` — fills all three layers tautologically, with
every operation recovered definitionally: the two invariance
fields are accepted as the identity function `λ s → s`, and the
four invariance laws and the agreement axiom are accepted as
`refl`. Definitional acceptance is itself the mathematical
content: a field filled by `λ s → s` or `refl` typechecks exactly
when the two sides of the field's equation are definitionally
convertible, so the green typecheck is a conversion proof, not
merely an inhabitation proof.

Four named pins convert the recovery into standing regression
checks — `killcheck-res-inv-r` and `killcheck-res-inv-l` (the
result type literally collapses under each action),
`killcheck-dot` (the abstract fixed-endpoint action computes to
the base category's action `_·_`), and `killcheck-itc1` (the
one-composite interchange law is definitional at the filling).
This module is imported by the whole-library typecheck, so a
foundation change that stops any of these reductions from firing
fails the next full build. One scope note for honesty:
`killcheck-dot` pins the recovery against the frozen copy of the
base category housed in this file, not against the live library
module — by design, a certificate witnesses its claim at the
pinned commit, so drift in the stable `Core.*` foundation will
trip the pin while drift in the volatile `Cat.*` namespace will
not.

Finally, `itc2-taut` records that at this filling the general
theory's two-composite interchange statement is term-for-term the
base category's `interchange` axiom. The companion certificate
`Gloss.InterchangeCircularity` consumes this fact.

Why it matters: the passage from one category to the layered
structure is free — specializing back to the concrete category
costs no transport, no coercion, nothing propositional. In
particular the composite-as-dependent-product carrier (a composite
from `x` to `y` is a function assigning, to every context of
incoming and outgoing arrows, a result arrow) is vindicated as the
right generality: the fixed-endpoint action defined through the
abstract invariance operator literally computes to the concrete
category's action.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Gloss.TautologicalFilling where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (is-contr→is-prop; _∙_)
open import Core.Transport.J using (J; subst)
open import Core.Equiv.Base using (iso→equiv; _≃_; is-equiv)
open import Core.Function.Embedding
  using (equiv→lc; image-fibers-contr→is-embedding)
```

## The representable-category core, frozen

An `hcategory` is a wild category — morphism types never truncated
to sets — presented by a representable embedding: morphisms `hom`
with identities `idn`, an embedding `emb` of morphisms into
two-sided composite operators, and five axioms (contractible
composition fibers, the coupling laws `interchange` and
`post-eval`, and two unit equivalences) from which every unit and
associativity law is derived. The blocks are frozen because the
`Cat.*` namespace is under active development: a certificate pins
the exact structure it certifies at a named commit, while the
stable `Core.*` API is imported, never frozen. The copies are
verbatim: the structure record, then the three
hypothesis-explicit coupling lemmas, the axioms record, and the
bundle.

```agda
-- Frozen from Cat.Codep.Base @ dde1f57 (Gloss certificates inline
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
```

The three standalone lemmas record that composition extraction and
idempotency derive from the coupling fields alone; their explicit
hypothesis lists are the minimality statements.

```agda
-- Frozen from Cat.Codep.Base @ dde1f57 (Gloss certificates inline
-- Cat.* definitions — the library may change; this evidence may not).
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
```

The axioms record gates every derived law on the five fields.

```agda
-- Frozen from Cat.Codep.Base @ dde1f57 (Gloss certificates inline
-- Cat.* definitions — the library may change; this evidence may not).
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

The bundle packages objects, structure, and axioms, re-exporting
the latter two so a single `open` recovers the whole interface.

```agda
-- Frozen from Cat.Codep.Base @ dde1f57 (Gloss certificates inline
-- Cat.* definitions — the library may change; this evidence may not).
record hcategory (o h : Level) : Type ((o ⊔ h) ₊) where
  no-eta-equality
  field
    ob        : Type o
    structure : hcategory-structure {o} {h} ob
    axioms    : hcategory-axioms structure
  open hcategory-structure structure public
  open hcategory-axioms axioms public
```

## The three-layer structure, frozen from the source experiment

The three records were born in the tracked experiment file
`Test.CodepFaithful-20260713-140913` and are frozen from it at the
same commit. `fam-structure` follows Petrakis's categories with
dependent arrows: `fam` is the abstract family carrier (the
concrete model
below instantiates it as the coslice — the arrows out of an
object) and `cofam` the cofamily carrier (the slice — the arrows
into an object), each with its morphism action and the action's
unit and functoriality laws. One notational remark: `fam₂` states
functoriality in this library's diagrammatic composition order
(`g ⨾ᵇ h` reads "g, then h"), so the law transposes the
applicative order of the source — the content is Petrakis's, the
orientation is kitcat's.

```agda
-- Frozen from Test.CodepFaithful-20260713-140913 @ dde1f57
-- (tracked-Test provenance; the source may drift — this may not);
-- comments revised at freeze.
-- Following Petrakis (arXiv:2303.14754), Def 2.1 (families:
-- ◃, 𝔣₁/𝔣₂) and §6 (cofamily-arrows: ▹, cf₁/cf₂);
-- entry resources/petrakis-dep-arrows/.
record fam-structure {o h fℓ} (ob : Type o)
  : Type (o ⊔ h ₊ ⊔ fℓ ₊) where
  no-eta-equality
  field
    hom  : ob → ob → Type h
    idn  : (x : ob) → hom x x
    _⨾ᵇ_ : ∀ {x y z} → hom x y → hom y z → hom x z
    fam   : ob → Type fℓ
    cofam : ob → Type fℓ
    _◃_ : ∀ {y z} → hom y z → fam z → fam y
    _▹_ : ∀ {x y} → cofam x → hom x y → cofam y
    fam₁   : ∀ {y} (φ : fam y) → idn y ◃ φ ≡ φ
    fam₂   : ∀ {x y z} (g : hom x y) (h : hom y z) (φ : fam z)
           → (g ⨾ᵇ h) ◃ φ ≡ g ◃ (h ◃ φ)
    cofam₁ : ∀ {x} (c : cofam x) → c ▹ idn x ≡ c
    cofam₂ : ∀ {x y z} (c : cofam x) (f : hom x y) (g : hom y z)
           → c ▹ (f ⨾ᵇ g) ≡ (c ▹ f) ▹ g

  ctx : ob → ob → Type fℓ
  ctx x y = cofam x × fam y

  sub : ∀ {x y z} → hom y z → ctx x z → ctx x y
  sub g (c , φ) = c , g ◃ φ

  subl : ∀ {x y v} → hom x y → ctx x v → ctx y v
  subl f (c , φ) = c ▹ f , φ
```

`codep-structure`'s composites are dependent products over
contexts: a
composite is a function, and applying it to a context is the only
eliminator. The invariance fields `res-inv-r`/`res-inv-l` are
functions between result types, not paths of types, and that
choice is load-bearing: in cubical type theory `transport refl` is
not definitionally the identity function, so a path-valued
invariance could recover a concrete action only up to a
propositional equality — the definitional recovery this
certificate pins would not even be statable. The right action
follows Petrakis's dependent application read at this
dependent-product carrier; the codependent duals follow his 2025
lecture slides.

```agda
-- Frozen from Test.CodepFaithful-20260713-140913 @ dde1f57
-- (tracked-Test provenance; the source may drift — this may not);
-- comments revised at freeze.
-- Following Petrakis (arXiv:2303.14754), Def 4.1 (dependent
-- application at the Π-integral: ·, 𝔡𝔦₁/𝔡𝔦₂); the codependent
-- duals (⟩, codep-l laws) follow Petrakis's WG6 2025 slides
-- (codHom, slide 41); entries resources/petrakis-dep-arrows/,
-- resources/petrakis-codep-slides/.
record codep-structure {o h fℓ rℓ} {ob : Type o}
  (FS : fam-structure {o} {h} {fℓ} ob)
  : Type (o ⊔ h ⊔ fℓ ⊔ rℓ ₊) where
  no-eta-equality
  open fam-structure FS
  field
    res : ∀ {x y} → ctx x y → Type rℓ

  composite : ob → ob → Type (fℓ ⊔ rℓ)
  composite x y = (γ : ctx x y) → res γ

  _·ʰ_ : ∀ {x y z} → composite x y → (g : hom y z)
       → ((γ : ctx x z) → res (sub g γ))
  (F ·ʰ g) γ = F (sub g γ)

  _⟩ʰ_ : ∀ {x y v} (f : hom x y) → composite y v
       → ((γ : ctx x v) → res (subl f γ))
  (f ⟩ʰ F) γ = F (subl f γ)

  field
    res-inv-r : ∀ {x y z} (g : hom y z) (c : cofam x) (φ : fam z)
              → res (c , g ◃ φ) → res (c , φ)
    res-inv-l : ∀ {x y v} (f : hom x y) (c : cofam x) (φ : fam v)
              → res (c ▹ f , φ) → res (c , φ)
    codep₁-r : ∀ {x y} (c : cofam x) (φ : fam y)
             → PathP (λ i → res (c , fam₁ φ i) → res (c , φ))
                 (res-inv-r (idn y) c φ) (λ s → s)
    codep₂-r : ∀ {x y z w} (g : hom y z) (h : hom z w)
                 (c : cofam x) (φ : fam w)
             → PathP (λ i → res (c , fam₂ g h φ i) → res (c , φ))
                 (res-inv-r (g ⨾ᵇ h) c φ)
                 (λ s → res-inv-r h c φ (res-inv-r g c (h ◃ φ) s))
    codep₁-l : ∀ {x v} (c : cofam x) (φ : fam v)
             → PathP (λ i → res (cofam₁ c i , φ) → res (c , φ))
                 (res-inv-l (idn x) c φ) (λ s → s)
    codep₂-l : ∀ {x y z v} (f : hom x y) (g : hom y z)
                 (c : cofam x) (φ : fam v)
             → PathP (λ i → res (cofam₂ c f g i , φ) → res (c , φ))
                 (res-inv-l (f ⨾ᵇ g) c φ)
                 (λ s → res-inv-l f c φ (res-inv-l g (c ▹ f) φ s))

  _·_ : ∀ {x y z} → composite x y → hom y z → composite x z
  (F · g) (c , φ) = res-inv-r g c φ (F (c , g ◃ φ))
  infixl 30 _·_

  _⟩_ : ∀ {x y v} → hom x y → composite y v → composite x v
  (f ⟩ F) (c , φ) = res-inv-l f c φ (F (c ▹ f , φ))
```

`codep-representable` carries no external credit: the
representability overlay —
composition obtained as the center of a contractible fiber rather
than posited as primitive data — is native to kitcat. In
Petrakis's setting composition is primitive, so the agreement
question that the `extract-agree` field answers cannot arise in
the source.

```agda
-- Frozen from Test.CodepFaithful-20260713-140913 @ dde1f57
-- (tracked-Test provenance; the source may drift — this may not);
-- comments revised at freeze.
record codep-representable {o h fℓ rℓ} {ob : Type o}
  {FS : fam-structure {o} {h} {fℓ} ob}
  (CS : codep-structure {o} {h} {fℓ} {rℓ} FS)
  : Type (o ⊔ h ⊔ fℓ ⊔ rℓ) where
  no-eta-equality
  open fam-structure FS
  open codep-structure CS
  field
    emb : ∀ {x y} → hom x y → composite x y
    compose-contr
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (fiber emb (emb f · g))
    extract-agree
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → compose-contr f g .center .fst ≡ f ⨾ᵇ g

  _⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾ g = compose-contr f g .center .fst
  infixr 40 _⨾_

  emb-comp : ∀ {x y z} (f : hom x y) (g : hom y z)
           → emb (f ⨾ g) ≡ emb f · g
  emb-comp f g = compose-contr f g .center .snd
```

## The tautological filling

The filling assigns, over a category `C`: `fam y = Σ v , hom y v`
and `cofam x = Σ w , hom w x` (coslice and slice), the family and
cofamily actions by the category's own representable actions `pre`
and `post`, the base composition by the extracted center `_⨾_` —
no raw composition data survives at the instance — and the result
type `res γ = hom (γ .fst .fst) (γ .snd .fst)`, the morphisms from
the cofamily element's source to the family element's target. The
lines marked ★ are the theorem: each is a field of the general
structure filled by the identity function or by `refl`, and a
field so filled typechecks exactly when the field's two sides are
definitionally convertible — the conversion checker is the judge.
The record values are given by copatterns so that projections
compute.

```agda
-- Frozen from Test.CodepFaithful-20260713-140913 @ dde1f57
-- (tracked-Test provenance; the source may drift — this may not);
-- comments revised at freeze.
module taut {o h} (C : hcategory o h) where
  open hcategory C

  FS : fam-structure {o} {h} {o ⊔ h} ob
  FS .fam-structure.hom  = hom
  FS .fam-structure.idn  = idn
  FS .fam-structure._⨾ᵇ_ = _⨾_
  FS .fam-structure.fam y   = Σ v ∶ ob , hom y v
  FS .fam-structure.cofam x = Σ w ∶ ob , hom w x
  FS .fam-structure._◃_ g φ = φ .fst , pre g (φ .snd)
  FS .fam-structure._▹_ c f = c .fst , post f (c .snd)
  FS .fam-structure.fam₁ φ     = ap (φ .fst ,_) (absorb-l (φ .snd))
  FS .fam-structure.fam₂ g h φ =
    ap (φ .fst ,_) (pre-comp g h (φ .snd))
  FS .fam-structure.cofam₁ c     = ap (c .fst ,_) (absorb-r (c .snd))
  FS .fam-structure.cofam₂ c f g =
    ap (c .fst ,_) (post-comp f g (c .snd))

  CS : codep-structure {o} {h} {o ⊔ h} {h} FS
  CS .codep-structure.res γ = hom (γ .fst .fst) (γ .snd .fst)
  CS .codep-structure.res-inv-r g c φ = λ s → s   -- ★
  CS .codep-structure.res-inv-l f c φ = λ s → s   -- ★
  CS .codep-structure.codep₁-r c φ     = refl     -- ★
  CS .codep-structure.codep₂-r g h c φ = refl     -- ★
  CS .codep-structure.codep₁-l c φ     = refl     -- ★
  CS .codep-structure.codep₂-l f g c φ = refl     -- ★

  RS : codep-representable CS
  RS .codep-representable.emb           = emb     -- the category's own
  RS .codep-representable.compose-contr = compose-contr
  RS .codep-representable.extract-agree f g = refl -- ★

  module FS = fam-structure FS
  module CS = codep-structure CS
  module RS = codep-representable RS
```

## The definitional pins

The four named pins restate the recovery as standing regression
checks. The path-valued pair records that the result type
literally collapses under each action (the type-level form of the
`λ s → s` fields above); `killcheck-dot` states that the abstract
fixed-endpoint action computes to the base category's `_·_` —
against the frozen copy above, per the synopsis note; and
`killcheck-itc1` pins the one-composite interchange law, which is
definitional at the filling because the two actions touch disjoint
slots of the context. Each pin is a reduction later development
leans on; a foundation change that silences one fails the
whole-library check that imports this file.

```agda
  -- Frozen from Test.CodepFaithful-20260713-140913 @ dde1f57
  -- (tracked-Test provenance; the source may drift — this may not);
  -- comments revised at freeze.
  killcheck-res-inv-r
    : ∀ {x y z} (g : hom y z) (c : FS.cofam x) (φ : FS.fam z)
    → CS.res (c , g FS.◃ φ) ≡ CS.res (c , φ)
  killcheck-res-inv-r g c φ = refl

  killcheck-res-inv-l
    : ∀ {x y v} (f : hom x y) (c : FS.cofam x) (φ : FS.fam v)
    → CS.res (c FS.▹ f , φ) ≡ CS.res (c , φ)
  killcheck-res-inv-l f c φ = refl

  killcheck-dot
    : ∀ {x y z} (F : CS.composite x y) (g : hom y z)
    → CS._·_ F g ≡ F · g
  killcheck-dot F g = refl

  killcheck-itc1
    : ∀ {x y z v} (f : hom x y) (F : CS.composite y z) (g : hom z v)
    → CS._·_ (CS._⟩_ f F) g ≡ CS._⟩_ f (CS._·_ F g)
  killcheck-itc1 f F g = refl
```

## The interchange statement at the filling

The general theory's two-composite interchange statement — the
subject of the companion certificate
`Gloss.InterchangeCircularity` — specializes at this filling to
the base category's `interchange` axiom, term for term: the proof
below is that axiom applied at the context's components, under
`funext`.

```agda
  -- Frozen from Test.CodepFaithful-20260713-140913 @ dde1f57
  -- (tracked-Test provenance; the source may drift — this may not);
  -- comments revised at freeze.
  itc2-taut
    : ∀ {x y z} (f : hom x y) (g : hom y z)
    → CS._·_ (emb f) g ≡ CS._⟩_ f (emb g)
  itc2-taut f g = funext λ γ →
    interchange f g (γ .fst .snd) (γ .snd .snd)
```
