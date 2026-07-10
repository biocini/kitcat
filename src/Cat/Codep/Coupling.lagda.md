Lane Biocini
July 2026

The coupling-derived laws. The coupling axioms themselves —
`interchange` and `post-eval` — now live in `codep-axioms`
(`Cat.Codep.Base`), alongside the two representable actions
`pre`/`post` in `codep-structure`. `coupling-laws` gates on the bundle
`(C : codep-category o h)` (one object, one gate) and derives the
identity idempotency block from them.

The provenance of `idem` — that idempotency is derivable from the
*coupling* sub-theory alone, never touching `unit-eqvl`/`unit-eqvr` or
`absorb` — is stated as a standalone theorem, the lemma
`idem-from-coupling`. Its hypotheses are exactly `compose-contr`,
`interchange`, `post-eval` (passed explicitly, and nothing else), so
its typechecked signature IS the minimality/absorption-freeness fact
(machine-checked non-usage of the unit axioms). `coupling-laws`
instantiates it and its siblings `post-comp`/`comp-eq` at the bundle's
fields. The interchange-independence research item references this
lemma directly.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep.Coupling where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_)

open import Cat.Codep.Base
```

## The coupling sub-theory, hypothesis-explicit

Each of `post-comp`/`comp-eq`/`idem` is a standalone lemma whose
hypotheses (`cc`, `ic`, and for the latter two `pe`) are listed in its
own signature — nothing else is in scope. `idem-from-coupling` is the
provenance theorem: its signature's hypothesis list machine-checks that
idempotency never touches `unit-eqvl`/`unit-eqvr` or `absorb`. The `⨾`
in the statements is the extraction `cc f g .center .fst`.

```agda
post-comp-from-coupling
  : ∀ {o h} {ob : Type o} (S : codep-structure {o} {h} ob)
    (open codep-structure S)
    (cc : ∀ {x y z} (f : hom x y) (g : hom y z)
        → is-contr (is-representable (emb f · g)))
    (ic : ∀ {x y z} (f : hom x y) (g : hom y z)
          {w} (a : hom w x) {v} (b : hom z v)
        → emb f ((v , (w , a)) , pre g b) ≡ emb g ((v , (w , post f a)) , b))
  → ∀ {x y z} (f : hom x y) (g : hom y z) {w} (a : hom w x)
  → post (cc f g .center .fst) a ≡ post g (post f a)
post-comp-from-coupling S cc ic f g {w} a =
  happly (cc f g .center .snd) ((_ , (w , a)) , idn _)
  ∙ ic f g a (idn _)
  where open codep-structure S

comp-eq-from-coupling
  : ∀ {o h} {ob : Type o} (S : codep-structure {o} {h} ob)
    (open codep-structure S)
    (cc : ∀ {x y z} (f : hom x y) (g : hom y z)
        → is-contr (is-representable (emb f · g)))
    (ic : ∀ {x y z} (f : hom x y) (g : hom y z)
          {w} (a : hom w x) {v} (b : hom z v)
        → emb f ((v , (w , a)) , pre g b) ≡ emb g ((v , (w , post f a)) , b))
    (pe : ∀ {x y} (f : hom x y) → post f (idn x) ≡ f)
  → ∀ {x y z} (f : hom x y) (g : hom y z)
  → cc f g .center .fst ≡ post g f
comp-eq-from-coupling S cc ic pe f g =
  sym (pe (cc f g .center .fst))
  ∙ post-comp-from-coupling S cc ic f g (idn _)
  ∙ ap (λ t → post g t) (pe f)
  where open codep-structure S

idem-from-coupling
  : ∀ {o h} {ob : Type o} (S : codep-structure {o} {h} ob)
    (open codep-structure S)
    (cc : ∀ {x y z} (f : hom x y) (g : hom y z)
        → is-contr (is-representable (emb f · g)))
    (ic : ∀ {x y z} (f : hom x y) (g : hom y z)
          {w} (a : hom w x) {v} (b : hom z v)
        → emb f ((v , (w , a)) , pre g b) ≡ emb g ((v , (w , post f a)) , b))
    (pe : ∀ {x y} (f : hom x y) → post f (idn x) ≡ f)
  → ∀ {x} → cc (idn x) (idn x) .center .fst ≡ idn x
idem-from-coupling S cc ic pe {x} =
  comp-eq-from-coupling S cc ic pe (idn x) (idn x) ∙ pe (idn x)
  where open codep-structure S
```

## The bundle-gated coupling-laws

`post-comp`, `comp-eq`, `idem` instantiate the from-coupling lemmas at
`C`'s fields; `pre-comp` is `act-comp` at the identity binder.

```agda
module coupling-laws {o h} (C : codep-category o h) where
  open codep-category C

  post-comp
    : ∀ {x y z} (f : hom x y) (g : hom y z) {w} (a : hom w x)
    → post (f ⨾ g) a ≡ post g (post f a)
  post-comp f g =
    post-comp-from-coupling structure compose-contr interchange f g

  comp-eq : ∀ {x y z} (f : hom x y) (g : hom y z) → f ⨾ g ≡ post g f
  comp-eq f g =
    comp-eq-from-coupling structure compose-contr interchange post-eval f g

  idem : ∀ {x} → idn x ⨾ idn x ≡ idn x
  idem = idem-from-coupling structure compose-contr interchange post-eval

  -- pre-comp is act-comp at the identity binder.
  pre-comp
    : ∀ {y z w} (g : hom y z) (h : hom z w) {v} (b : hom w v)
    → pre (g ⨾ h) b ≡ pre g (pre h b)
  pre-comp {y} g h b = act-comp (_ , unit y) g h b
```
