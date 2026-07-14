Lane Biocini
July 2026

Gloss: machine-checked evidence for T21 in docs/gloss.md.
Self-contained modulo Core.*, with no Cat.* import: every code
block is a frozen copy of its tracked source at the marked commit,
apart from one block of additions marked as such below.

Over a three-layer structure — a substrate of families and
cofamilies with actions (`fam-structure`, following Petrakis), a
layer of dependent composites with result-invariance
(`codep-structure`), and a representability overlay
(`codep-representable`) — the field `extract-agree` asserts that
the composition extracted from the contractible representability
fiber agrees with the substrate's primitive composition `⨾ᵇ`.
This certificate proves that `extract-agree` is independent: not
derivable from the other fields of the three records, nor from
any representability, orbit-surjectivity, or pointedness
strengthening in the class examined below. The argument has three
parts.

First (`bridge-forms`): the three natural formulations of the
agreement — at the extraction (`EA-stmt`), under the embedding
(`EH-stmt`), and between embeddings (`EE-stmt`) — are
inter-derivable over the contractibility hypothesis, since all
three inhabit one contractible fiber; hence a single countermodel
refutes the entire class.

Second (`collapsed`): the countermodel — one object, Boolean homs
with `⨾ᵇ = xor`, trivial families, constant embedding — satisfies
every remaining field, and moreover every representability-shaped
strengthening (`all-repr`), pointedness of the families
(`fam-pt`), and orbit surjectivity on both sides (`orbit-surj`,
`orbit-surj-cofam`); yet the extracted composite is definitionally
the left argument (`killcheck-center`, a pinned reduction), so
`extract-agree` fails at `(false , true)` (`no-extract-agree`,
with `no-EH` and `no-EE` closing the class).

Third (the section ending the file): the two honest derivation
routes over the abstract hypotheses are each pushed to the point
where it demands exactly the missing content, and the
typechecker's rejections are preserved verbatim — both exhibit
the same gap, a conversion between embedding-level and
substrate-level equalities that no field supplies.

Consequence: the composition law at the substrate level
(`·-comp-base`) is free — it never mentions the embedding — and
only the functoriality of the extracted composition costs the
bridge; the independence settles that the agreement is a genuine
axiom of the overlay, not a redundancy.

The refutation's honest boundary. Decoding structures in the
style of a chosen centre with evaluation equations are outside
the refuted class by design: such structure derives the agreement
because it is the agreement in a different wrapper. And one
candidate class — action-faithfulness, or two-sided
representability — fails in the model but is excluded only by
argument together with the two preserved walls; its dedicated
countermodel is designed but not built here.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Gloss.ExtractAgreeIndependence where

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

## The three records

`fam-structure` is the substrate, following Petrakis: a graph
with identities and a primitive composition `⨾ᵇ`, together with
families and cofamilies acted on from the two sides (`◃`, `▹`),
each action functorial over `⨾ᵇ`. `codep-structure` adds a result
type over each context, dependent composites as sections of it,
and function-valued result-invariance: fields converting a result
over an acted-on context back to the plain context, with laws
(`codep₁-r` through `codep₂-l`) tying the conversions to the
substrate's action laws. `codep-representable` is the
representability overlay: an embedding of morphisms into
composites, contractibility of the embedding's fiber over an
acted image (`compose-contr`), and the field under study —
`extract-agree`, asserting that the extracted centre agrees with
`⨾ᵇ`.

```agda
-- Frozen from Test.CodepExtractAgree-20260713-171000 @ dde1f57
-- (tracked-Test provenance; the source may drift — this may not);
-- comments revised to the presentation standard 2026-07-13.
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
-- Frozen from Test.CodepExtractAgree-20260713-171000 @ dde1f57
-- (tracked-Test provenance; the source may drift — this may not);
-- comments revised to the presentation standard 2026-07-13.
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

The overlay carries no source credit: in Petrakis's development
composition is primitive, so the agreement question cannot arise
there; the representability presentation is this library's own.

```agda
-- Frozen from Test.CodepExtractAgree-20260713-171000 @ dde1f57
-- (tracked-Test provenance; the source may drift — this may not);
-- comments revised to the presentation standard 2026-07-13.
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

## The three formulations are equivalent

Over the abstract records, with the embedding and its
contractibility taken as explicit hypotheses (`bridge-forms`
binds `emb` and `cc` as module parameters), the three
formulations of the agreement all describe points of one
contractible fiber, and points of a single contractible fiber
are identified for free. `EA-stmt` is the field form, at the
extraction; `EH-stmt` states the agreement under the embedding;
`EE-stmt` states it between embeddings. Each derives the others,
so one countermodel refutes all three (realized as terms at
`no-EH`/`no-EE` below).

```agda
-- Frozen from Test.CodepExtractAgree-20260713-171000 @ dde1f57
-- (tracked-Test provenance; the source may drift — this may not);
-- comments revised to the presentation standard 2026-07-13.
module bridge-forms {o h fℓ rℓ} {ob : Type o}
  {FS : fam-structure {o} {h} {fℓ} ob}
  {CS : codep-structure {o} {h} {fℓ} {rℓ} FS}
  (open fam-structure FS)
  (open codep-structure CS)
  (emb : ∀ {x y} → hom x y → composite x y)
  (cc : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (fiber emb (emb f · g)))
  where

  -- the extraction over the hypothesis: cc is a module parameter,
  -- so ⨾R is relative to it, not a renaming of the record's ⨾.
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

A corollary locating the cost precisely: the composition law at
the substrate level, `F · (g ⨾ᵇ h) ≡ (F · g) · h`, is derivable
with no appeal to `extract-agree` — indeed with no mention of the
embedding at all. Only the functoriality of the extracted
composition `⨾` costs the bridge.

```agda
-- Frozen from Test.CodepExtractAgree-20260713-171000 @ dde1f57
-- (tracked-Test provenance; the source may drift — this may not);
-- comments revised to the presentation standard 2026-07-13.
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

The equivalence is complete: `ea→hom`, `hom→ea`, `ea→ee`, and
`ee→ea` close by elementary fiber algebra in one contractible
fiber, and `·-comp-base` closes beside them — the substrate-level
composition law needs no agreement axiom.

## The collapsed-context countermodel

The decisive construction. Over `ob = ⊤`, `hom = Bool`,
`⨾ᵇ = xor`, `fam = cofam = ⊤`, `res = Bool`, and the constant
embedding `emb₀`, every field of the three records except
`extract-agree` holds: the four laws mentioning `⨾ᵇ` are paths in
`⊤`-derived types (`refl` by `⊤`-eta), the result-invariance laws
are paths between identity functions over a constant `res`, and
`emb₀` is an equivalence, so every representability-shaped
strengthening holds as well; the family side is even pointed. The
extracted composite is definitionally the left argument, so
`extract-agree` at `(false , true)` asserts `false ≡ true`. The
composition is `xor` rather than a projection deliberately:
`(Bool, xor, false)` is a group, so the refutation survives any
future unit or associativity laws for `⨾ᵇ`. And everything lives
at the lowest universe level, so a level-polymorphic derivation
would specialize here: the refutation kills derivations at every
level.

```agda
-- Frozen from Test.CodepExtractAgree-20260713-171000 @ dde1f57
-- (tracked-Test provenance; the source may drift — this may not);
-- comments revised to the presentation standard 2026-07-13.
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
  -- ⊤-eta, so both sides are λ γ → F (tt , tt) and refl suffices.
  emb₀-equiv : ∀ {x y} → hom x y ≃ CS.composite x y
  emb₀-equiv = iso→equiv emb₀ eval₀ (λ _ → refl) (λ _ → refl)

  cc₀ : ∀ {x y z} (f : hom x y) (g : hom y z)
      → is-contr (fiber emb₀ (CS._·_ (emb₀ f) g))
  cc₀ f g = emb₀-equiv .snd .eqv-fibers (CS._·_ (emb₀ f) g)
```

The definitional trace the refutation leans on: the center that
`iso→equiv` produces is `(eval₀ T , ε T)` — its first component
is the inverse's value (`Core.Equiv.Base`) — and
`eval₀ (CS._·_ (emb₀ f) g)` unfolds to
`res-inv-r g tt tt (emb₀ f (tt , g ◃ tt)) = (λ s → s) f = f`.
`killcheck-center` pins this reduction: were a change to the
equivalence machinery to stop it firing, this certificate would
fail to typecheck.

```agda
  -- Frozen from Test.CodepExtractAgree-20260713-171000 @ dde1f57
  -- (tracked-Test provenance; the source may drift — this may
  -- not); comments revised to the presentation standard 2026-07-13.
  -- The load-bearing reduction, pinned: the refutation needs only
  -- that the center's first component is definitionally f.
  killcheck-center : (f g : Bool) → cc₀ f g .center .fst ≡ f
  killcheck-center f g = refl

  -- extract-agree refuted at (false, true): the left side is
  -- definitionally false (the killcheck-center reduction), the
  -- right side is xor false true ≐ true.
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

The strengthenings, refuted wholesale: every representability-
flavored strengthening in the examined class holds in this model
while `extract-agree` fails, so none can entail it.

```agda
  -- Frozen from Test.CodepExtractAgree-20260713-171000 @ dde1f57
  -- (tracked-Test provenance; the source may drift — this may
  -- not); comments revised to the presentation standard 2026-07-13.
  -- Every emb₀-fiber is contractible, so any representability-
  -- shaped axiom — idn-repr included, at any target composite —
  -- holds here.
  all-repr : ∀ {x y} (T : CS.composite x y)
           → is-contr (fiber emb₀ T)
  all-repr = emb₀-equiv .snd .eqv-fibers

  idn-repr-holds : ∀ {x} → is-contr (fiber emb₀ (emb₀ (idn x)))
  idn-repr-holds = all-repr _

  -- Pointedness of the families also holds here, so a pointed-
  -- family strengthening cannot entail the agreement: the missing
  -- ingredient is a decoding at the point, not the point itself.
  fam-pt : ∀ {y} → fam y
  fam-pt = tt

  -- Orbit surjectivity on the family side, in Σ-form (the
  -- prop-truncated form is a fortiori inhabited).
  orbit-surj : ∀ {y z} (φ : fam z) (ψ : fam y)
             → Σ g ∶ hom y z , (g ◃ φ) ≡ ψ
  orbit-surj φ ψ = false , refl
```

The two definitions below are additions made at the freeze
(2026-07-13), not present in the frozen source: the cofamily-side
orbit twin, mirroring `orbit-surj`, and the class refutation as
terms — `bridge-forms` instantiated at the collapsed model, so
that one countermodel refuting the entire class is itself
machine-checked (`no-EH`, `no-EE`).

```agda
  orbit-surj-cofam : ∀ {x y} (c : cofam x) (c' : cofam y)
                   → Σ g ∶ hom x y , (c ▹ g) ≡ c'
  orbit-surj-cofam c c' = false , refl

  module BF = bridge-forms {FS = FS} {CS = CS} emb₀ cc₀

  no-EH : ¬ BF.EH-stmt
  no-EH eh = no-extract-agree-field (BF.hom→ea eh)

  no-EE : ¬ BF.EE-stmt
  no-EE ee = no-extract-agree-field (BF.ee→ea ee)
```

What the countermodel establishes, in sum: every field of the
substrate and composite layers is inhabited over the trivial
families, `emb₀` is an equivalence with both `iso→equiv` legs
closing by `refl`, the extraction's reduction is pinned
(`killcheck-center`), and `no-extract-agree` /
`no-extract-agree-field` refute the agreement at `(false , true)`.
Every strengthening in the examined class holds in the model —
full representability (`all-repr`, `idn-repr-holds`), orbit
surjectivity on both sides (`orbit-surj`, `orbit-surj-cofam`),
pointed families (`fam-pt`) — so none of them entails
`extract-agree`.

## The two derivation routes and their obstructions

Could the agreement be derived outright — from the two record
layers, the embedding, and the contractibility hypothesis alone?
The two natural routes were fixed before the attempt, so the
obstruction below is not an artifact of proof search. Each route
is pushed, inside `bridge-forms`, to the point where it demands
exactly the missing content; the missing equation is then forced
with `refl` and the typechecker's rejection recorded. Both
attempts were made in the tracked source at the pinned commit and
reverted there; each fenced block below is the raw typechecker
error, verbatim from `The terms` onward — the leading
location/error-tag line (`<file>:<pos>: error: [UnequalTerms]`)
is omitted, since it names the transient probe site.

Route (a), the fiber route: inject `(f ⨾ᵇ g , ?)` into the
contractible fiber of `cc f g` and project with `ap fst`. The
attempted term, inside `bridge-forms`:

```text
agree-attempt-a : EA-stmt
agree-attempt-a f g =
  ap fst (is-contr→is-prop (cc f g)
    (cc f g .center) (f ⨾ᵇ g , forced))
  where
    forced : emb (f ⨾ᵇ g) ≡ emb f · g
    forced = refl
```

The hole `forced` demands `EH-stmt` itself — the route begs its
own question. Forcing it with `refl`, the checker rejects
(exit 42):

```text
The terms
  emb (f ⨾ᵇ g) γ
and
  res-inv-r g (γ .fst) (γ .snd) (emb f (γ .fst , (g ◃ γ .snd)))
are not equal at type res γ
when checking that the expression refl has type
emb (f ⨾ᵇ g) ≡ emb f · g
```

Route (b), the action route: derive the substrate action law at
the extraction, `((f ⨾R g) ◃ φ) ≡ (f ◃ (g ◃ φ))`, by transporting
`fam₂` along the agreement — which is the goal itself. The
attempted term, inside `bridge-forms`:

```text
fam2-ext
  : ∀ {x y z} (f : hom x y) (g : hom y z) (φ : fam z)
  → ((f ⨾R g) ◃ φ) ≡ (f ◃ (g ◃ φ))
fam2-ext f g φ = ap (_◃ φ) forced ∙ fam₂ f g φ
  where
    forced : f ⨾R g ≡ f ⨾ᵇ g
    forced = refl
```

Forcing the agreement with `refl`, the checker rejects (exit 42):

```text
The terms
  cc f g .center .fst
and
  f ⨾ᵇ g
are not equal at type hom x z
when checking that the expression refl has type (f ⨾R g) ≡ (f ⨾ᵇ g)
```

Route (b)'s residue is the bridge equation itself, bare — the
same missing content as route (a), reached from the other end: a
substrate action law stated at the extraction would demand
precisely this equality, and no field supplies it.

A consistency check binds the two halves of the certificate: had
either route closed, instantiating the closure at the collapsed
model and feeding it to `no-extract-agree` would have derived
`⊥`. Neither closed, as the countermodel requires.

Both rejections exhibit the same missing conversion — between
equalities at the embedding level and equalities at the substrate
level — and the records' field inventory offers nothing of that
type. The walls recorded in `Gloss.InterchangeCircularity` meet
the same missing conversion in another shape, on the two-sided
interchange routes.
