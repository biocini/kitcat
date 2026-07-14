Spike: `Cat.Virtual` (classifier-gated / partial-representability) rebuilt
on the flat `Cat.Codep` pattern. Tests the trilayer's designed payoff:
whether the classified variant is A DIFFERENT AXIOM RECORD OVER THE SAME
`codep-structure`, sharing the whole derived/coherence layer.

The claim under test: `classified-axioms` is defined over an UNCHANGED
`codep-structure S`. It translates `Cat.Virtual`'s axiom set to the flat
vocabulary (noy ↦ pre, yon ↦ post, context tuples ↦ `((w,a),(v,b))`),
gating `compose`/`interchange` on a prop-classifier while keeping the unit
axioms ungated.

Scratch only. Not in All.lagda.md.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.CodepClassified-20260710-171145 where

open import Core.Type using (Type; Level; _₊; _⊔_; 0ℓ; ⊤; tt; _∘_)
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using
  ( is-contr→is-prop; _∙_; contr-face; module Path; pcom; module pcom; pcom→∙ )
open import Core.Transport.J using (subst)
open import Core.Transport.Base using (is-prop→PathP)
open import Core.Path.Base using (ap-comp)
open import Core.Equiv.Base using (is-equiv)
open import Core.Function.Embedding using (equiv→lc)
open import Core.HLevel.Base using (⊤-is-prop)

open import Cat.Type
```

## Step 1 — the classified axiom record

`classified-axioms` lives over an UNCHANGED `codep-structure S`. The five
`Cat.Virtual` axiom groups translate mechanically:

  * `classifier` / `classifier-prop` — prop-valued classifier on pairs.
  * `compose-classified` — gated `compose-contr`. Target is the flat
    `is-representable (emb f · g) = fiber emb (emb f · g)`; `emb f · g`
    is exactly `Cat.Virtual`'s `λ w a v b → emb f w a v (noy g v b)`.
  * `interchange-classified` — gated `interchange`, same binder pattern as
    the flat unconditional `interchange`.
  * `post-eval` (= `yon-eval`), `unit-eqvl`, `unit-eqvr` — UNGATED, exactly
    the flat `codep-axioms` unit axioms.
  * `classifier-idn-l/r`, `classifier-assoc` — the extra classifier
    identity/associativity laws with no flat counterpart (the classifier's
    own algebra).

```agda
record classified-axioms {o h p} {ob : Type o}
  (S : codep-structure {o} {h} ob) : Type (o ⊔ h ⊔ p ₊) where
  no-eta-equality
  open codep-structure S

  field
    classifier
      : ∀ {x y z} → hom x y → hom y z → Type p
    classifier-prop
      : ∀ {x y z} {f : hom x y} {g : hom y z} → is-prop (classifier f g)
    compose-classified
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → classifier f g
      → is-contr (is-representable (emb f · g))
    interchange-classified
      : ∀ {x y z} (f : hom x y) (g : hom y z)
      → classifier f g
      → ∀ {w} (a : hom w x) {v} (b : hom z v)
      → emb f ((w , a) , (v , pre g b))
      ≡ emb g ((w , post f a) , (v , b))
    post-eval
      : ∀ {x y} (f : hom x y) → post f (idn x) ≡ f
    unit-eqvl : ∀ {x} {v} → is-equiv (pre (idn x) {v})
    unit-eqvr : ∀ {x} {w} → is-equiv (post (idn x) {w})
    classifier-idn-l : ∀ {x y} (f : hom x y) → classifier (idn x) f
    classifier-idn-r : ∀ {x y} (f : hom x y) → classifier f (idn y)

  -- Gated extraction and its gated `emb-comp`.
  comp : ∀ {x y z} (f : hom x y) (g : hom y z) → classifier f g → hom x z
  comp f g c = compose-classified f g c .center .fst

  emb-comp : ∀ {x y z} (f : hom x y) (g : hom y z) (c : classifier f g)
           → emb (comp f g c) ≡ emb f · g
  emb-comp f g c = compose-classified f g c .center .snd

  field
    classifier-assoc
      : ∀ {x y z w} {f : hom x y} {g : hom y z} {h : hom z w}
      → (cfg : classifier f g) → (cgh : classifier g h)
      → classifier (comp f g cfg) h × classifier f (comp g h cgh)
```

### Which derived members survive with classifier hypotheses

The composition-side derivations (`pre-comp`, `sub-comp`, `·-comp`,
`post-comp`, `comp-eq`) survive in gated form. The provenance lemmas
`post-comp-from-coupling` etc. CANNOT be reused: they quantify ungated
`cc`/`ic` over all pairs, whereas here we only have classified ones. So
`post-comp`/`comp-eq`/`idem` are re-derived by hand (as `Cat.Virtual`
does), reading the coupling only at the pairs we can classify.

```agda
  -- pre-comp: free happly of emb-comp read at the center (fam₂), gated.
  pre-comp : ∀ {y z w} (g : hom y z) (h : hom z w) (c : classifier g h)
             {v} (b : hom w v)
           → pre (comp g h c) b ≡ pre g (pre h b)
  pre-comp {y} g h c {v} b = happly (emb-comp g h c) (ctr y , (v , b))

  sub-comp : ∀ {x y z w} (g : hom y z) (h : hom z w) (c : classifier g h)
           → sub {x} (comp g h c) ≡ sub g ∘ sub h
  sub-comp g h c = funext λ γ →
    ap (γ .fst ,_) (ap (γ .snd .fst ,_) (pre-comp g h c (γ .snd .snd)))

  ·-comp : ∀ {x y z w} (F : composite x y) (g : hom y z) (h : hom z w)
           (c : classifier g h)
         → F · (comp g h c) ≡ F · g · h
  ·-comp F g h c = funext λ γ → ap F (happly (sub-comp g h c) γ)

  -- post-comp: costs interchange (cofam₂). Hand-derived at classified pairs.
  post-comp
    : ∀ {x y z} (f : hom x y) (g : hom y z) (c : classifier f g)
      {w} (a : hom w x)
    → post (comp f g c) a ≡ post g (post f a)
  post-comp {x} {y} {z} f g c {w} a =
    happly (emb-comp f g c) ((w , a) , (z , idn z))
    ∙ interchange-classified f g c a (idn z)

  comp-eq : ∀ {x y z} (f : hom x y) (g : hom y z) (c : classifier f g)
          → comp f g c ≡ post g f
  comp-eq f g c =
    sym (post-eval (comp f g c))
    ∙ post-comp f g c (idn _)
    ∙ ap (λ t → post g t) (post-eval f)

  -- Identity classifier witness (classifier-idn-l at the identity).
  idn-class : ∀ {x} → classifier (idn x) (idn x)
  idn-class {x} = classifier-idn-l (idn x)

  idem : ∀ {x} → comp (idn x) (idn x) idn-class ≡ idn x
  idem {x} = comp-eq (idn x) (idn x) idn-class ∙ post-eval (idn x)
```

### Unit fragment — survives UNGATED

Every unit derivation needs only the identity classifier (always available
via `classifier-idn-l/r`), so the RESULTS are ungated, exactly as in the
flat `codep-axioms` and in `Cat.Virtual`.

```agda
  absorb-l : ∀ {x v} (b : hom x v) → pre (idn x) b ≡ b
  absorb-l {x} b = equiv→lc unit-eqvl pre-idn-idpt
    where
      pre-idn-idpt : pre (idn x) (pre (idn x) b) ≡ pre (idn x) b
      pre-idn-idpt =
        sym (subst (λ t → pre t b ≡ pre (idn x) (pre (idn x) b))
          idem (pre-comp (idn x) (idn x) idn-class b))

  absorb-r : ∀ {w x} (a : hom w x) → post (idn x) a ≡ a
  absorb-r {w} {x} a = equiv→lc unit-eqvr post-idn-idpt
    where
      post-idn-idpt : post (idn x) (post (idn x) a) ≡ post (idn x) a
      post-idn-idpt =
        sym (subst (λ t → post t a ≡ post (idn x) (post (idn x) a))
          idem (post-comp (idn x) (idn x) idn-class a))

  ·-idn : ∀ {x y} (F : composite x y) → F · idn y ≡ F
  ·-idn F = composite-ext λ γ →
    ap (λ β → F (γ .fst , β))
      (ap (γ .snd .fst ,_) (absorb-l (γ .snd .snd)))

  emb-idn-absorb : ∀ {x y} (f : hom x y) → emb (idn x) · f ≡ emb f
  emb-idn-absorb {x} f = composite-ext λ γ →
    interchange-classified (idn x) f (classifier-idn-l f)
      (γ .fst .snd) (γ .snd .snd)
    ∙ ap (λ a' → emb f ((γ .fst .fst , a') , γ .snd))
        (absorb-r (γ .fst .snd))

  emb-image-contr : ∀ {x y} (f : hom x y) → is-contr (fiber emb (emb f))
  emb-image-contr {x} f =
    subst (λ T → is-contr (fiber emb T))
      (emb-idn-absorb f) (compose-classified (idn x) f (classifier-idn-l f))

  unitr : ∀ {x y} (f : hom x y) → comp f (idn y) (classifier-idn-r f) ≡ f
  unitr {x} {y} f = ap fst (is-contr→is-prop (emb-image-contr f) lhs rhs)
    where
      lhs : fiber emb (emb f)
      lhs = comp f (idn y) (classifier-idn-r f)
          , (emb-comp f (idn y) (classifier-idn-r f) ∙ ·-idn (emb f))
      rhs : fiber emb (emb f)
      rhs = f , refl

  unitl : ∀ {x y} (f : hom x y) → comp (idn x) f (classifier-idn-l f) ≡ f
  unitl {x} {y} f = ap fst (is-contr→is-prop (emb-image-contr f) lhs rhs)
    where
      lhs : fiber emb (emb f)
      lhs = comp (idn x) f (classifier-idn-l f)
          , (emb-comp (idn x) f (classifier-idn-l f) ∙ emb-idn-absorb f)
      rhs : fiber emb (emb f)
      rhs = f , refl
```

## Step 2 — gated collapse-B coherence

Ported under gating: `E₃-contr`, `assoc`, and `face₁₂`. The gated `E₃`
tower is a mechanical decoration of collapse-B's `subst`-manufactured
contractibility with classifier arguments. `assoc` uses
`classifier-assoc cfg cgh` for the two intermediate composites, exactly
mirroring `Cat.Virtual.assoc`.

```agda
module Coherence {o h p} {ob : Type o}
  {S : codep-structure {o} {h} ob} (A : classified-axioms {o} {h} {p} S) where
  open codep-structure S
  open classified-axioms A

  E₃ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w) → composite x w
  E₃ f g h = emb f · g · h

  pt-l : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
       → (cfg : classifier f g) (c-l : classifier (comp f g cfg) h)
       → fiber emb (E₃ f g h)
  pt-l f g h cfg c-l =
    comp (comp f g cfg) h c-l
    , (emb-comp (comp f g cfg) h c-l ∙ ap (_· h) (emb-comp f g cfg))

  pt-r : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
       → (cgh : classifier g h) (c-r : classifier f (comp g h cgh))
       → fiber emb (E₃ f g h)
  pt-r f g h cgh c-r =
    comp f (comp g h cgh) c-r
    , (emb-comp f (comp g h cgh) c-r ∙ ·-comp (emb f) g h cgh)

  E₃-contr : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
           → (cfg : classifier f g) (c-l : classifier (comp f g cfg) h)
           → is-contr (fiber emb (E₃ f g h))
  E₃-contr f g h cfg c-l .center = pt-l f g h cfg c-l
  E₃-contr f g h cfg c-l .paths =
    is-contr→is-prop
      (subst (λ T → is-contr (fiber emb T))
        (ap (_· h) (emb-comp f g cfg))
        (compose-classified (comp f g cfg) h c-l)) _

  assoc-σ : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
          → (cfg : classifier f g) (cgh : classifier g h)
          → pt-l f g h cfg (classifier-assoc cfg cgh .fst)
          ≡ pt-r f g h cgh (classifier-assoc cfg cgh .snd)
  assoc-σ f g h cfg cgh =
    is-contr→is-prop
      (E₃-contr f g h cfg (classifier-assoc cfg cgh .fst))
      (pt-l f g h cfg (classifier-assoc cfg cgh .fst))
      (pt-r f g h cgh (classifier-assoc cfg cgh .snd))

  assoc : ∀ {x y z w} (f : hom x y) (g : hom y z) (h : hom z w)
        → (cfg : classifier f g) (cgh : classifier g h)
        → comp (comp f g cfg) h (classifier-assoc cfg cgh .fst)
        ≡ comp f (comp g h cgh) (classifier-assoc cfg cgh .snd)
  assoc f g h cfg cgh = ap fst (assoc-σ f g h cfg cgh)
```

### face₁₂ under gating

The right-whisker face. This is where the classifier bookkeeping surfaces:
whiskering the associator by `k` needs `classifier m k` for `m` ranging
along the associator path `assoc-σ f g h`. Since the classifier is a prop,
this is a `classifier`-PathP `cpath` (new machinery: `is-prop→PathP`). The
face's RHS is consequently no longer `ap (_⨾ k) (assoc f g h)` — that
whisker function does not exist in the gated world — but the
classifier-transported whisker `ap fst core₁₂`.

```agda
  module _ {x y z w v}
    (f : hom x y) (g : hom y z) (h : hom z w) (k : hom w v)
    (cfg : classifier f g) (cgh : classifier g h) (chk : classifier h k)
    where

    -- Intermediate composites and their classifiers.
    c-fgh-l = classifier-assoc cfg cgh .fst      -- classifier (fg) h
    c-fgh-r = classifier-assoc cfg cgh .snd      -- classifier f (gh)
    c-ghk-l = classifier-assoc cgh chk .fst      -- classifier (gh) k
    fgh-l = comp (comp f g cfg) h c-fgh-l        -- (fg)h
    fgh-r = comp f (comp g h cgh) c-fgh-r        -- f(gh)
    c-top1 = classifier-assoc c-fgh-l chk .fst   -- classifier ((fg)h) k
    c-top2 = classifier-assoc c-fgh-r c-ghk-l .fst  -- classifier (f(gh)) k

    E₄ : composite x v
    E₄ = emb f · g · h · k

    E₄c : is-contr (fiber emb E₄)
    E₄c .center .fst = comp fgh-l k c-top1
    E₄c .center .snd =
        emb-comp fgh-l k c-top1
      ∙ ap (_· k) (emb-comp (comp f g cfg) h c-fgh-l)
      ∙ ap (_· k) (ap (_· h) (emb-comp f g cfg))
    E₄c .paths =
      is-contr→is-prop
        (subst (λ T → is-contr (fiber emb T)) path₄
          (compose-classified fgh-l k c-top1)) _
      where
        path₄ : emb fgh-l · k ≡ E₄
        path₄ = ap (_· k) (emb-comp (comp f g cfg) h c-fgh-l)
              ∙ ap (_· k) (ap (_· h) (emb-comp f g cfg))

    pt₁ : fiber emb E₄
    pt₁ = comp fgh-l k c-top1
        , (emb-comp fgh-l k c-top1
          ∙ ap (_· k) (emb-comp (comp f g cfg) h c-fgh-l)
          ∙ ap (_· k) (ap (_· h) (emb-comp f g cfg)))

    pt₂ : fiber emb E₄
    pt₂ = comp fgh-r k c-top2
        , (emb-comp fgh-r k c-top2
          ∙ ap (_· k) (emb-comp f (comp g h cgh) c-fgh-r)
          ∙ ap (_· k) (·-comp (emb f) g h cgh))

    -- Right-whisker lift, now carrying its own classifier for `m ⨾ k`.
    Λk : (m : hom x w) (cmk : classifier m k) → emb m ≡ E₃ f g h
       → fiber emb E₄
    Λk m cmk q = comp m k cmk , (emb-comp m k cmk ∙ ap (_· k) q)

    -- The classifier transported along the associator path (new machinery).
    cpath : PathP (λ i → classifier (assoc-σ f g h cfg cgh i .fst) k)
              c-top1 c-top2
    cpath = is-prop→PathP (λ i → classifier-prop) c-top1 c-top2

    core₁₂ : Λk fgh-l c-top1 (pt-l f g h cfg c-fgh-l .snd)
           ≡ Λk fgh-r c-top2 (pt-r f g h cgh c-fgh-r .snd)
    core₁₂ i =
      Λk (assoc-σ f g h cfg cgh i .fst) (cpath i)
         (assoc-σ f g h cfg cgh i .snd)

    σ₁₂ : pt₁ ≡ pt₂
    σ₁₂ = is-contr→is-prop E₄c pt₁ pt₂

    α₁₂ : comp fgh-l k c-top1 ≡ comp fgh-r k c-top2
    α₁₂ = ap fst σ₁₂

    -- The gated face. RHS is the classifier-transported whisker,
    -- NOT ap (_⨾ k) (assoc f g h): the whisker-by-k function does not
    -- exist gated.
    face₁₂ : α₁₂ ≡ ap fst core₁₂
    face₁₂ = contr-face E₄c σ₁₂ w₁₂ core₁₂ v₁₂
      where
        w₁₂ : pt₁ .snd
            ≡ Λk fgh-l c-top1 (pt-l f g h cfg c-fgh-l .snd) .snd
        w₁₂ = sym (ap (emb-comp fgh-l k c-top1 ∙_)
          (ap-comp (_· k) (emb-comp (comp f g cfg) h c-fgh-l)
            (ap (_· h) (emb-comp f g cfg))))
        v₁₂ : Λk fgh-r c-top2 (pt-r f g h cgh c-fgh-r .snd) .snd
            ≡ pt₂ .snd
        v₁₂ = ap (emb-comp fgh-r k c-top2 ∙_)
          (ap-comp (_· k) (emb-comp f (comp g h cgh) c-fgh-r)
            (·-comp (emb f) g h cgh))
```

## Step 3 — degeneration smoke test

A plain `codep-category` yields a `classified-axioms` instance with the
total/trivial classifier (`⊤`): every field is the plain record's field
with the classifier argument discarded. This is the "Cat.Virtual =
contractible classifier" claim.

```agda
module _ {o h} (C : codep-category o h) where
  open codep-category C

  trivial-classified : classified-axioms {p = 0ℓ} structure
  trivial-classified .classified-axioms.classifier _ _ = ⊤
  trivial-classified .classified-axioms.classifier-prop = ⊤-is-prop
  trivial-classified .classified-axioms.compose-classified f g _ =
    compose-contr f g
  trivial-classified .classified-axioms.interchange-classified f g _ =
    interchange f g
  trivial-classified .classified-axioms.post-eval = post-eval
  trivial-classified .classified-axioms.unit-eqvl = unit-eqvl
  trivial-classified .classified-axioms.unit-eqvr = unit-eqvr
  trivial-classified .classified-axioms.classifier-idn-l _ = tt
  trivial-classified .classified-axioms.classifier-idn-r _ = tt
  trivial-classified .classified-axioms.classifier-assoc _ _ = tt , tt
```
