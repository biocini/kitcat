Lane Biocini
July 2026

A formulation of category — in the mould of `Cat.Type` — presented
through a representable embedding `emb` into two-sided *composite*
operators. A category is `hom` + identities `idn` + `emb`, together
with five axioms; every unit and associativity law is derived. This
is one presentation of a category among several, not "the codependent
theory": codependence names the *shape* of the carrier the embedding
lands in, not a different notion of category.

The records take the name `hcategory` — they are what they present:
wild (homotopy) categories, homs never truncated to a set. They are
one *instance* of the (co)dependent theory, not that theory itself,
which is a planned separate stratum. The `Cat.Codep` module namespace
is retained for now, so the file paths and imports are unchanged.

The presentation is a trilayer. The operations — `hom`, `idn`, the
embedding `emb`, and the two representable actions `pre`/`post` —
together with every axiom-free derived notion live in
`hcategory-structure`. The five axioms (contractible composition fibers,
the coupling `interchange`/`post-eval`, and the two unit
equivalences), the extraction `_⨾_`, and *all* derived laws live in
`hcategory-axioms`, stated over a `hcategory-structure` value. The
universe-ranging `hcategory` bundles `ob`, `structure`, `axioms`
and re-exports the other two — so the bundle IS the category, and the
refactor equation is literal: `Cat.Type.category ≅ hcategory`.

Splitting the axioms off from the operations is what makes naive
multi-object instances termination-safe: `hcategory-axioms` states its
axioms over an *external* `hcategory-structure` value, so a direct
instance's proof only projects that closed value — a `hom`/`idn` that
cases on the object no longer leaves a stuck `idn y` self-call.

`hcategory-axioms` is now the single gate for every derived law. The
former `Cat.Codep.Coupling` and `Cat.Codep.Unit` modules — the
coupling idempotency block and the whole unit fragment — are absorbed
here: with the axioms record complete, there is nothing left to gate
downstream. What stays standalone are the three provenance lemmas
`post-comp-from-coupling`/`comp-eq-from-coupling`/`idem-from-coupling`
above the record: their explicit hypothesis lists are machine-checked
minimality theorems (idempotency never touches the unit axioms), so
they must be stated where those hypotheses can be listed one by one,
not as record members with the whole field-set in scope.

## Carrier vocabulary

The carrier is canonical, built from `hom` + `idn`, and its names
carry the Petrakis paper-trail — "Categories with dependent arrows"
(arXiv:2303.14754) for the family/dependent side; the codependent
side follows Petrakis's WG6 2025 talk ("Categories with dependent
and codependent arrows"), which builds on Y. Ehrhardt's 2024 LMU
thesis. `cofam x = Σ w , hom w x` is a
*cofamily-arrow* into `x` (Petrakis: cofHom; an object of the slice
over `x`). `fam y = Σ v , hom y v` is a *family-arrow* out of `y`
(Petrakis: fHom; an object of the coslice under `y`). A context
`ctx x y = cofam x × fam y` pairs the two; `res γ` is the *result
family* over a context — the hom from the cofamily's source to the
family's target — the slot that a future general fam-parametric
stratum abstracts as a field.

`ctr y = (y , idn y)` is the identity cofamily-arrow — the *center*:
in the path instance `cofam x` is the singleton `Σ w , w ≡ x` and
`ctr` is its center of contraction; wild categories posit the center
without the contractibility. It is the universal element the
representable actions read at.

This record *inlines* Petrakis's (co)dependent substrate at
its tautological instance: fHom is the literal coslice, cofHom the
literal slice, and the (co)dependent arrows are the plain two-sided
`composite`. The general theory over *abstract* families is a
separate, planned stratum; here everything is pinned to the concrete
hom carrier.

`pre g` is the family-arrow action (contravariant, Petrakis (fam):
λ ↦ λ∘g); `post f` is the cofamily-arrow action (covariant, (cofam):
ρ ↦ f∘ρ). These are the real names of `Cat.Type`'s yon/noy
placeholders. `composite x y` is the Π-model of the two-sided
codependent arrows; `emb` is the two-sided Yoneda/CPS embedding
f ↦ λ(a,b). b∘f∘a.

The six-law dictionary, in Petrakis numbering:

| Petrakis | Kitcat                  |
|----------|-------------------------|
| (fam₁)   | `unit-eqvl` / `absorb-l` |
| (fam₂)   | `pre-comp`               |
| (cofam₁) | `unit-eqvr` / `absorb-r` |
| (cofam₂) | `post-comp`              |
| (codep₁) | `·-idn`                  |
| (codep₂) | `·-comp`                 |

The polarity is asymmetric: `pre-comp` is free (a `happly` of
`emb-comp`), while `post-comp` costs `interchange`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (is-contr→is-prop; _∙_)
open import Core.Transport.J using (J; subst)
open import Core.Equiv.Base using (iso→equiv; _≃_; is-equiv)
open import Core.Function.Embedding
  using (equiv→lc; image-fibers-contr→is-embedding)
```

## The structure record

`hcategory-structure` holds the operations `hom`/`idn`/`emb`, the
canonical carrier (`cofam`/`fam`/`ctr`/`ctx`/`res`), the two
representable actions `pre`/`post` (the axiom field types
`interchange`/`post-eval`/the unit equivalences reference them, so
they live here), the lax substitution `sub` and application `_·_`, and
the unconditional total-space equivalence `hom≃representable`.

```agda
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

  composite-ext : ∀ {x y} {F G : composite x y} → (∀ γ → F γ ≡ G γ) → F ≡ G
  composite-ext h = funext h

  field
    emb : ∀ {x y} → hom x y → composite x y

  -- The tightness predicate: a composite is representable when an
  -- `emb`-image.
  is-representable : ∀ {x y} → composite x y → Type (o ⊔ h)
  is-representable F = fiber emb F

  -- `pre g` acts on the family slot, `post f` on the cofamily; both
  -- are `emb` read at the center.
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

## Coupling provenance lemmas (hypothesis-explicit)

Each of these stays standalone: its explicit hypothesis list IS the
minimality theorem. `idem-from-coupling`'s signature machine-checks
that idempotency is derivable from `compose-contr`/`interchange`/
`post-eval` alone — never touching `unit-eqvl`/`unit-eqvr` or
`absorb`. The `hcategory-axioms` record below instantiates each at
its own fields. The `⨾` in the statements is the extraction
`cc f g .center .fst`.

```agda
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

## The axioms record

`hcategory-axioms` gates every derived law on the five fields —
`compose-contr`, the coupling `interchange`/`post-eval`, and the two
unit equivalences — over a `hcategory-structure` value. The structure
parameter is annotated `{o} {h}` so the level is fixed by the value.

The internal order matters: the extraction `_⨾_`, `emb-comp`,
`pre-comp` (the old `act-comp`, now read at the center), `sub-comp`,
`·-comp` come first; then the coupling derivations (`post-comp`,
`comp-eq`, `idem`, instantiating the provenance lemmas); then the unit
fragment — `absorb-l` (consuming `idem`/`pre-comp`) and `absorb-r`
(consuming `idem`/`post-comp`),
`·-idn`, `emb-idn-absorb`, `emb-image-contr`, `unitl`/`unitr`, and
finally `emb-post` before `unit-is-prop` and `is-representable-prop`.

```agda
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
  ·-idn F = composite-ext λ γ →
    ap (λ β → F (γ .fst , β)) (ap (γ .snd .fst ,_) (absorb-l (γ .snd .snd)))

  emb-idn-absorb : ∀ {x y} (f : hom x y) → emb (idn x) · f ≡ emb f
  emb-idn-absorb f = composite-ext λ γ →
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

## The bundle

`hcategory` bundles `ob`, `structure`, `axioms` and re-exports
the latter two, so a single `open hcategory C` recovers the
entire API. The axioms record is complete, so the bundle IS the
category.

```agda
record hcategory (o h : Level) : Type ((o ⊔ h) ₊) where
  no-eta-equality
  field
    ob        : Type o
    structure : hcategory-structure {o} {h} ob
    axioms    : hcategory-axioms structure
  open hcategory-structure structure public
  open hcategory-axioms axioms public
```

## Definitional regression witnesses

`composite` is a genuine Π (application computes — the funext-merge
substrate), and `pre-comp` is definitionally `happly` of `emb-comp`
read at the center. The bundle re-export recovers both structure-level
and axioms-level names from one `open`.

```agda
module _ {o h} {ob : Type o} (S : hcategory-structure {o} {h} ob) where
  open hcategory-structure S

  composite-is-Π : ∀ {x y} (F : composite x y) (γ : ctx x y) → res γ
  composite-is-Π F γ = F γ

  pre-eval-is-post-eval
    : ∀ {x y} (f : hom x y) → pre f (idn y) ≡ post f (idn x)
  pre-eval-is-post-eval f = refl

module _ {o h} {ob : Type o} {S : hcategory-structure {o} {h} ob}
  (A : hcategory-axioms S) where
  open hcategory-structure S
  open hcategory-axioms A

  pre-comp-is-happly
    : ∀ {y z w} (g : hom y z) (hh : hom z w) {v} (b : hom w v)
    → pre-comp g hh b ≡ happly (emb-comp g hh) (ctr y , (v , b))
  pre-comp-is-happly g hh b = refl

module _ {o h} (C : hcategory o h) where
  open hcategory C

  -- structure-level and axioms-level names, from a single open.
  _ : ∀ {x y} → hom x y → composite x y
  _ = emb

  _ : ∀ {x y z} → hom x y → hom y z → hom x z
  _ = _⨾_
```
