Lane Biocini
July 2026

Extract-agree bridge spike (arms 1-3): is Layer C's
`extract-agree` derivable from weaker structure, or irreducible at
Petrakis generality? Run ledger:
`notes/plans/2026-07-13-extract-agree-bridge.md`; spec: the
analyzer memo
`notes/research/2026-07-13-extract-agree-bridge-design.md`
(§-references are to it). The three stratum records are restated
verbatim from the green stratum spike
`src/Test/CodepFaithful-20260713-140913.lagda.md` :71-194 (as of
the 2026-07-13 credit-prose edits; line anchors into that spike
drift with its prose — the load-bearing fact is block identity,
re-verified by the mechanical gate's diff, not the line numbers).
No import of that spike and no import of Bb.CatsWithExplicitInterchange.Type:
self-contained modulo Core, for the later Gloss freeze.

Kill criteria (pre-registered, memo §3/§4/§5-C3):

- Arm 1 (C4, bridge-forms): {EA, EH, EE} inter-derivable over the
  compose-contr hypothesis. Expected DERIVED; consequence: one
  countermodel refutes the whole class.
- Arm 2 (C0, collapsed): the countermodel typechecks including the
  ★ killcheck-center and no-extract-agree ⇒ irreducibility PINNED
  (kills C1, C2(i), pointed-fam). A Layer A/B refl rejected ⇒
  transcribe both normal forms, FULL STOP (design revelation). ★
  rejected alone ⇒ hand-built is-contr fallback (memo §3), record
  the attempt; the refutation needs only `center .fst ≐ f`.
- Arm 3 (C3, honest): routes (a)/(b) forced-refl probes over
  {FS, CS, emb, cc} alone; expected STUCK ×2, residues
  transcribed. ⊥-detector, pre-registered: if either route closes
  while arm 2 is green, instantiate the derivation in the
  collapsed model against no-extract-agree, derive ⊥, and
  ESCALATE — a stratum-record discrepancy, not mathematics.

Verdict summary (this run, 2026-07-13; per-arm detail at each
`-- VERDICT` block below; the typecheck is the pin — the file is
green at zero warnings):

- Arm 1 DERIVED — EA ⟺ EH ⟺ EE over compose-contr, all four
  maps first-try; ·-comp-base pins the one-link corollary (the
  ⨾ᵇ-level composition law is extract-agree-free).
- Arm 2 DERIVED — the collapsed countermodel typechecks whole,
  both memo hinges held (emb₀-equiv's refl legs; the ★ center
  reduction), and extract-agree is REFUTED at (false, true): the
  field is independent of the remaining stratum fields and of
  every representability/orbit/pointed strengthening the model
  satisfies.
- Arm 3 STUCK ×2 — both pre-registered routes wall at the bridge
  (route a: EH's normal-form gap; route b: the naked
  center-vs-⨾ᵇ residue); walls transcribed verbatim (fenced).
  The pre-registered ⊥-detector did not fire.

Enshrined 2026-07-13: this result is T21 in docs/gloss.md, frozen
as `Gloss.ExtractAgreeIndependence` @ dde1f57.

Scratch file — not in All.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.CatsWithExplicitInterchange.Gist.CodepExtractAgree where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (is-contr→is-prop; _∙_)
open import Core.Data.Empty using (⊥; ¬_)
open import Core.Data.Bool.Type
open import Core.Data.Bool.Base using (xor)
open import Core.Equiv.Base using (iso→equiv; _≃_; eqv-fibers)
open import Core.Transport.J using (subst)
```

## The stratum records (restated)

Verbatim from the green spike :69-190 (self-containment for the
freeze; Test never imports Test), with the green spike's level
binders `fℓ rℓ`. Layer A is the Petrakis substrate; Layer B the
Π-integral composite with function-valued res-invariance; Layer C
the representability overlay whose `extract-agree` field is this
spike's subject.

```agda
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

```agda
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

Layer C carries no external credit: the representability overlay is
native to kitcat (memo §5-C5 — Petrakis's composition is primitive,
so the agreement question cannot arise in the source).

```agda
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

## Arm 1 — the equivalence class (C4, memo §4)

Over the abstract stratum with hypothesis-explicit {emb, cc} (the
`*-from-coupling` pattern), the three bridge formulations sit in
one contractible fiber, so agreement among them is free (the
T4-side of the free/paid boundary): EA (the current field form),
EH (emb-hom), EE (agreement under emb) are inter-derivable.
Consequence: one countermodel refutes the whole class.

```agda
module bridge-forms {o h fℓ rℓ} {ob : Type o}
  {FS : fam-structure {o} {h} {fℓ} ob}
  {CS : codep-structure {o} {h} {fℓ} {rℓ} FS}
  (open fam-structure FS)
  (open codep-structure CS)
  (emb : ∀ {x y} → hom x y → composite x y)
  (cc : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (fiber emb (emb f · g)))
  where

  -- the extraction over the hypothesis (not a wrapper: cc is a
  -- module parameter).
  _⨾R_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾R g = cc f g .center .fst

  EA-stmt : Type (o ⊔ h)
  EA-stmt = ∀ {x y z} (f : hom x y) (g : hom y z)
          → f ⨾R g ≡ f ⨾ᵇ g

  EH-stmt : Type (o ⊔ h ⊔ fℓ ⊔ rℓ)
  EH-stmt = ∀ {x y z} (f : hom x y) (g : hom y z)
          → emb (f ⨾ᵇ g) ≡ emb f · g

  EE-stmt : Type (o ⊔ h ⊔ fℓ ⊔ rℓ)
  EE-stmt = ∀ {x y z} (f : hom x y) (g : hom y z)
          → emb (f ⨾R g) ≡ emb (f ⨾ᵇ g)

  -- links: emb (f ⨾ᵇ g) ≡ emb (f ⨾R g)  [sym (ap emb (ea f g))]
  --        emb (f ⨾R g) ≡ emb f · g     [cc f g .center .snd]
  ea→hom : EA-stmt → EH-stmt
  ea→hom ea f g = sym (ap emb (ea f g)) ∙ cc f g .center .snd

  -- the injected fiber point (f ⨾ᵇ g , eh f g) lands in
  -- fiber emb (emb f · g); contractibility identifies it with the
  -- center; ap fst projects.
  hom→ea : EH-stmt → EA-stmt
  hom→ea eh f g =
    ap fst (is-contr→is-prop (cc f g)
      (cc f g .center) (f ⨾ᵇ g , eh f g))

  ea→ee : EA-stmt → EE-stmt
  ea→ee ea f g = ap emb (ea f g)

  -- sym (ee f g) ∙ cc f g .center .snd : emb (f ⨾ᵇ g) ≡ emb f · g
  -- is EH's body; hom→ea closes.
  ee→ea : EE-stmt → EA-stmt
  ee→ea ee = hom→ea (λ f g → sym (ee f g) ∙ cc f g .center .snd)
```

The §2 corollary: the bridge is exactly one link wide — the
⨾ᵇ-level composition law is extract-agree-free (the green spike's
`·-comp` link₂ alone, emb never mentioned); only ⨾-functoriality
costs the bridge.

```agda
module one-link {o h fℓ rℓ} {ob : Type o}
  {FS : fam-structure {o} {h} {fℓ} ob}
  {CS : codep-structure {o} {h} {fℓ} {rℓ} FS}
  (open fam-structure FS)
  (open codep-structure CS)
  where

  ·-comp-base
    : ∀ {x y z w} (F : composite x y) (g : hom y z) (h : hom z w)
    → F · (g ⨾ᵇ h) ≡ (F · g) · h
  ·-comp-base F g h = funext λ γ i →
    codep₂-r g h (γ .fst) (γ .snd) i
      (ap F (λ j → γ .fst , fam₂ g h (γ .snd) j) i)
```

-- VERDICT ARM 1: DERIVED. {EA, EH, EE} inter-derivable over the
-- stratum + cc (ea→hom / hom→ea / ea→ee / ee→ea, all first-try:
-- one contractible fiber, elementary fiber algebra). The one-link
-- corollary ·-comp-base also DERIVED: the ⨾ᵇ-level composition
-- law costs no extract-agree.

## Arm 2 — the collapsed-context countermodel (C0, memo §3)

The decisive arm. Over `ob = ⊤`, `hom = Bool`, `⨾ᵇ = xor`,
`fam = cofam = ⊤`, `res = Bool`, `emb₀ = const`: every stratum
field minus extract-agree holds — the four ⨾ᵇ-mentioning laws are
paths in ⊤-derived types (refl by ⊤-eta), the codep laws are paths
between identity functions over a constant `res` — and `emb₀` is an
equivalence, so every representability-shaped strengthening holds
too; the fam side is even pointed. The extraction is definitionally
the left argument, so extract-agree at (false, true) asserts
`false ≡ true`. `xor` over right-projection deliberately:
(Bool, xor, false) is a group, so the refutation survives any
future base unit/assoc laws for ⨾ᵇ. Everything at 0ℓ: a
level-polymorphic derivation would specialize here, so the
refutation kills derivations at all levels.

```agda
module collapsed where

  FS : fam-structure {0ℓ} {0ℓ} {0ℓ} ⊤
  FS .fam-structure.hom _ _  = Bool
  FS .fam-structure.idn _    = false
  FS .fam-structure._⨾ᵇ_     = xor
  FS .fam-structure.fam _    = ⊤
  FS .fam-structure.cofam _  = ⊤
  FS .fam-structure._◃_ _ _  = tt
  FS .fam-structure._▹_ _ _  = tt
  FS .fam-structure.fam₁ _       = refl
  FS .fam-structure.fam₂ _ _ _   = refl
  FS .fam-structure.cofam₁ _     = refl
  FS .fam-structure.cofam₂ _ _ _ = refl

  CS : codep-structure {0ℓ} {0ℓ} {0ℓ} {0ℓ} FS
  CS .codep-structure.res _ = Bool
  CS .codep-structure.res-inv-r _ _ _ = λ s → s
  CS .codep-structure.res-inv-l _ _ _ = λ s → s
  CS .codep-structure.codep₁-r _ _     = refl
  CS .codep-structure.codep₂-r _ _ _ _ = refl
  CS .codep-structure.codep₁-l _ _     = refl
  CS .codep-structure.codep₂-l _ _ _ _ = refl

  open fam-structure FS
  module CS = codep-structure CS

  emb₀ : ∀ {x y} → hom x y → CS.composite x y
  emb₀ f = λ _ → f

  eval₀ : ∀ {x y} → CS.composite x y → hom x y
  eval₀ F = F (tt , tt)

  -- retr goal emb₀ (F (tt , tt)) ≡ F: γ ≐ (tt , tt) by Σ-eta +
  -- ⊤-eta, so both sides are λ γ → F (tt , tt) (memo §3 hinge 1;
  -- fallback funext λ γ → refl).
  emb₀-equiv : ∀ {x y} → hom x y ≃ CS.composite x y
  emb₀-equiv = iso→equiv emb₀ eval₀ (λ _ → refl) (λ _ → refl)

  cc₀ : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (fiber emb₀ (CS._·_ (emb₀ f) g))
  cc₀ f g = emb₀-equiv .snd .eqv-fibers (CS._·_ (emb₀ f) g)
```

The definitional trace the refutation leans on (memo §3 hinge 2):
the qinv-derived center is `(eval₀ T , ε T)` — its fst is the
inverse's value, `Core.Equiv.Base:150-152` — and
`eval₀ (CS._·_ (emb₀ f) g)` unfolds to
`res-inv-r g tt tt (emb₀ f (tt , g ◃ tt)) = (λ s → s) f = f`.

```agda
  -- ★ the pin (fallback if rejected: hand-built is-contr with
  -- center (f , refl); the refutation needs only center .fst ≐ f).
  killcheck-center : (f g : Bool) → cc₀ f g .center .fst ≡ f
  killcheck-center f g = refl

  -- extract-agree refuted at (false, true): LHS ≐ false (the ★
  -- reduction), RHS ≐ xor false true ≐ true. Pattern-lambda
  -- precedent: Core.Data.Bool.Properties:26-27.
  no-extract-agree
    : ¬ ((f g : Bool) → cc₀ f g .center .fst ≡ xor f g)
  no-extract-agree ea = subst P (ea false true) tt
    where P = λ { false → ⊤ ; true → ⊥ }

  -- the same refutation at the exact field shape of
  -- codep-representable.extract-agree, with compose-contr := cc₀
  -- (hom x z ≐ Bool and f ⨾ᵇ g ≐ xor f g at this filling).
  no-extract-agree-field
    : ¬ (∀ {x y z} (f : hom x y) (g : hom y z)
         → cc₀ f g .center .fst ≡ (f ⨾ᵇ g))
  no-extract-agree-field ea = no-extract-agree (λ f g → ea f g)
```

The kill instances (memo §3/§5): every representability-flavored
strengthening in the candidate space holds in this model while
extract-agree fails, so none can entail it.

```agda
  -- C1 killer: EVERY emb₀-fiber is contractible, so any
  -- representability-shaped axiom (idn-repr included, at any
  -- target in the §2 inventory) holds here.
  all-repr : ∀ {x y} (T : CS.composite x y)
           → is-contr (fiber emb₀ T)
  all-repr = emb₀-equiv .snd .eqv-fibers

  idn-repr-holds : ∀ {x} → is-contr (fiber emb₀ (emb₀ (idn x)))
  idn-repr-holds = all-repr _

  -- pointed-fam killer: the rejected design (b) HOLDS here — the
  -- missing ingredient is Base's decoding at the point, not the
  -- point itself.
  fam-pt : ∀ {y} → fam y
  fam-pt = tt

  -- C2(i) killer: Σ-form orbit surjectivity (the prop-truncated
  -- form is a fortiori inhabited).
  orbit-surj : ∀ {y z} (φ : fam z) (ψ : fam y)
             → Σ g ∶ hom y z , (g ◃ φ) ≡ ψ
  orbit-surj φ ψ = false , refl
```

-- VERDICT ARM 2: DERIVED — irreducibility PINNED. The full
-- stratum-minus-extract-agree is inhabited over trivial families
-- (every Layer A/B refl accepted first-try), emb₀ is an
-- equivalence (both iso→equiv legs closed by refl — memo hinge 1
-- held, no funext fallback), the ★ killcheck-center reduction
-- fired (memo hinge 2 held, no hand-built fallback), and
-- no-extract-agree / no-extract-agree-field refute the field at
-- (false, true). Candidates C1 (all-repr, idn-repr-holds), C2(i)
-- (orbit-surj), and pointed-fam (fam-pt) all HOLD in the model,
-- so none entails extract-agree.

## Arm 3 — the honest derivation arm (C3, memo §5)

Pure derivability of EA over the abstract stratum hypotheses
{FS, CS, emb, cc} alone — the two pre-registered routes, forced at
the annotated goal types from memo §5-C3 and run to their walls
inside the bridge-forms telescope. Both probes were run live in
this file (2026-07-13, this run) and reverted per the failure
protocol; each fenced block below is the raw typechecker error
verbatim from `The terms` onward — the leading file:position line
is omitted, since it names the transient probe site.

-- STUCK (route a — the fiber route): inject (f ⨾ᵇ g , ?) into
-- cc f g's contractible fiber and project with ap fst.
--   attempted term (inside bridge-forms):
--     agree-attempt-a : EA-stmt
--     agree-attempt-a f g =
--       ap fst (is-contr→is-prop (cc f g)
--         (cc f g .center) (f ⨾ᵇ g , forced))
--       where
--         forced : emb (f ⨾ᵇ g) ≡ emb f · g
--         forced = refl
--   `forced` demands EH itself; forcing it with refl, the checker
--   rejects (exit 42):

```text
The terms
  emb (f ⨾ᵇ g) γ
and
  res-inv-r g (γ .fst) (γ .snd) (emb f (γ .fst , (g ◃ γ .snd)))
are not equal at type res γ
when checking that the expression refl has type
emb (f ⨾ᵇ g) ≡ emb f · g
```

-- STUCK (route b — the action route): reach fam₂-at-the-
-- extraction via ap (_◃ φ) on the agreement, which is the goal
-- itself.
--   attempted term (inside bridge-forms):
--     fam2-ext
--       : ∀ {x y z} (f : hom x y) (g : hom y z) (φ : fam z)
--       → ((f ⨾R g) ◃ φ) ≡ (f ◃ (g ◃ φ))
--     fam2-ext f g φ = ap (_◃ φ) forced ∙ fam₂ f g φ
--       where
--         forced : f ⨾R g ≡ f ⨾ᵇ g
--         forced = refl
--   forcing it with refl, the checker rejects (exit 42):

```text
The terms
  cc f g .center .fst
and
  f ⨾ᵇ g
are not equal at type hom x z
when checking that the expression refl has type (f ⨾R g) ≡ (f ⨾ᵇ g)
```

-- Route (b)'s residue is the naked bridge — the machine-checked
-- record that rejected option (a) of the prep memo's note 7 (fam₂
-- stated at the extraction) is the same missing content, reached
-- from the other end.
--
-- ⊥-detector (pre-registered, memo §5-C3): DID NOT FIRE — neither
-- route closed. Had either closed while arm 2 stayed green, the
-- closure instantiated at collapsed (FS, CS, emb₀, cc₀) and fed
-- to no-extract-agree would have derived ⊥ — full stop, escalate.
--
-- VERDICT ARM 3: STUCK ×2 — the expected, healthy outcome; the
-- residues are the calibration record (arm 2 carries the pin).
-- Both walls are the A2 wall's ⨾ᵇ-shaped twin, consistent with
-- the §2 empty-interface inventory: no stratum field converts
-- emb-level paths into fam-level paths or vice versa.
