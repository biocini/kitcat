Gloss: machine-checked evidence for T13(ii)/(iii) in docs/gloss.md.
Self-contained modulo Core.* and Gloss.PathGroupoid (whose frozen
`hcategory` this builds on); no Cat.* import.

Exploratory SPIKE — the level-2 representability axiom ("couple²").
GO/NO-GO for whether one prop-valued overlay `level-2-representable`
discharges the two stuck coherences `R-core` (CodepTriangleCrux) and
`θ-core` (CodepOpTheta), and whether the path-groupoid model inhabits
it. Tracked Gloss evidence (T13).

The unifying discovery behind this file (recorded up front so the code
below can be read against it):

BOTH `θ-core` and `R-core` are instances of ONE statement — the
natural slot-swap homotopy between the *pre-action* and the
*post-action* of an identity agrees with `interchange` at the
doubly-centered point and with `refl` at the identity. Writing
`Ψ a b := emb e ((x,a),(x,b))` for `e = idn x` and `D₀ := Ψ e e`:

  * `θ-core` (from CodepOpTheta) is
      `ap (pre e) pe ≡ interchange e e e e ∙ ap (post e) pe`
    with `pe = post-eval e : D₀ ≡ e`. This is exactly
    `homotopy-natural η pe` for a homotopy `η : pre e ⟹ post e` with
    `η D₀ = interchange e e e e` and `η e = refl`.

  * `R-core` (from CodepTriangleCrux) is `crux` lifted through the
    equivalence `ap (pre (idn y))`. `crux : absorb-l c ≡ IC ∙ AR`
    (c = pre g b) says the unit-route proof of `pre (idn y) c ≡ c`
    agrees with the interchange-route proof. Same slot-swap coherence,
    smeared over the context `c`.

Both are genuinely non-`refl` 2-cells; both are `true` in the path
groupoid (concrete `pcom` algebra) but NOT derivable from the five
`hcategory` axioms. The overlay posits them, uniformly.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Gloss.PropPinning where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
  using ( is-contr→is-prop; is-contr→is-set; total-contr-unique
        ; _∙_; module Path; pcom; pfil; module pcom; pcom→∙ )
open import Core.Transport.J using (subst; J)
open import Core.Transport.Base using (transport-refl)
open import Core.Homotopy using (homotopy-natural)
open import Core.Equiv.Base using (is-equiv; iso→equiv; eqv-fibers)
open import Core.Function.Embedding
  using ( equiv→lc; equiv→lc-section
        ; is-embedding→ap-equiv; is-equiv→is-embedding )
open import Core.Path.Base using (ap-comp)

open import Gloss.PathGroupoid using (hcategory; path-cat)
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

subst-path-l
  : ∀ {u w} {A : Type u} {B : Type w} (Q : A → B)
    {a a' : A} {D : B} (e : a ≡ a') (P : Q a ≡ D)
  → subst (λ t → Q t ≡ D) e P ≡ sym (ap Q e) ∙ P
subst-path-l Q {D = D} e P =
  J (λ a'' e' → subst (λ t → Q t ≡ D) e' P ≡ sym (ap Q e') ∙ P)
    (transport-refl P ∙ sym (Path.unitl P)) e
```

## (1) The encoding — slot-swap homotopy at an identity endo

`swap-lift e` (for an endo `e : hom x x`) is the space of homotopies
`η` between the pre-action `pre e` and the post-action `post e`, both
read as endofunctions of `hom x x` (`pre e t = emb e ((x,idn),(x,t))`
puts `t` in the fam slot; `post e t = emb e ((x,t),(x,idn))` puts it
in the cofam slot). The two boundary clauses pin `η` at the identity
(`refl`) and at the doubly-centered point `D₀ = post e (idn x)`
(the `interchange` cell). At `e = idn x` the boundary types line up
definitionally: `interchange e e e e : pre e D₀ ≡ post e D₀`.

Design note. `η` ranges over ALL of `hom x x`, and the two boundary
values sit at two distinct points; this is why the space is not
inert (KILL-A). The pointwise `interchange` supplies the value at
`D₀`, and the unit structure supplies `refl` at `e`, but no total
homotopy carrying BOTH prescribed values is constructible from the
five axioms.

Rejected encodings (one line each):
  * `fiber emb T` / `fiber (ap emb) Θ` — INERT: `emb` is an embedding
    (`emb-image-contr`), so `ap emb` is an equivalence and every such
    fiber is already contractible from the five axioms.
  * `Σ p ∶ (pre(idn) c ≡ c) , ap (pre idn) p ≡ Qc`
    = `fiber (ap (pre idn)) Qc`
    — INERT for the same reason (`unit-eqvl` makes `ap (pre idn)` an
    equivalence; this is `kill-1`).
  * `Σ η , (η ≡ interchange)` — INERT: a singleton around `interchange`.
  * plain `pre(idn) c ≡ c` (no cut) — the opposite failure: a wild
    (untruncated) path space, NOT contractible; the axiom would be
    false, killing the model (KILL-B).
The surviving encoding threads between "free fiber" and "wild path
space" by pinning a total homotopy at two points.

```agda
module encoding {o h} (C : hcategory o h) where
  open hcategory C

  swap-lift : (x : ob) → Type h
  swap-lift x =
    Σ η ∶ ((t : hom x x) → pre (idn x) t ≡ post (idn x) t)
        , ( (η (post (idn x) (idn x))
              ≡ interchange (idn x) (idn x) (idn x) (idn x))
          × (η (idn x) ≡ refl) )
```

## The overlay record

```agda
record level-2-representable {o h} (C : hcategory o h) : Type (o ⊔ h) where
  no-eta-equality
  open hcategory C
  open encoding C
  field
    couple² : (x : ob) → is-contr (swap-lift x)
```

## (4) θ-core from couple²

`θ-core` (verbatim from CodepOpTheta) is the naturality square of the
slot-swap homotopy along `post-eval e`, collapsed by the two boundary
clauses. It is `homotopy-natural η (post-eval e)` with `η e = refl`
and `η D₀ = interchange e e e e`.

```agda
module theta {o h} {C : hcategory o h} (L2 : level-2-representable C) where
  open hcategory C
  open encoding C
  open level-2-representable L2

  module _ {x : ob} where
    private
      e : hom x x
      e = idn x

      D₀ : hom x x
      D₀ = post e (idn x)

      IC : pre e D₀ ≡ post e D₀
      IC = interchange e e e e

      apPre : pre e D₀ ≡ pre e e
      apPre = ap (pre e) (post-eval e)

      apPost : post e D₀ ≡ post e e
      apPost = ap (post e) (post-eval e)

      lift : swap-lift x
      lift = couple² x .center

      η : (t : hom x x) → pre e t ≡ post e t
      η = lift .fst

      ηD₀ : η D₀ ≡ IC
      ηD₀ = lift .snd .fst

      ηe : η e ≡ refl
      ηe = lift .snd .snd

    θ-core : apPre ≡ IC ∙ apPost
    θ-core =
        sym (Path.unitr apPre)
      ∙ ap (apPre ∙_) (sym ηe)
      ∙ homotopy-natural η (post-eval e)
      ∙ ap (_∙ apPost) ηD₀
```

θ-core has the exact type CodepOpTheta's stuck `θ-core` hole demands
(`ap (pre e) (post-eval e) ≡ interchange e e e e ∙ ap (post e)
(post-eval e)`, `e = idn x`). Plugging this into that file's hole
closes its κ / M-B≡M-A / ξ / θ chain verbatim — those four
definitions consume only `θ-core` of this type, so no edits there.

## (2) KILL-A — swap-lift is NOT inhabitable from the five axioms

The honest inhabitant attempt. The only total homotopy
`pre (idn x) ⟹ post (idn x)` the five axioms furnish is the absorb
route `η-abs t = absorb-l t ∙ sym (absorb-r t)` (both actions cancel
the identity, so the composite crosses through `t`). This typechecks.

```agda
module killA {o h} (C : hcategory o h) where
  open hcategory C

  module _ {x : ob} where
    η-abs : (t : hom x x) → pre (idn x) t ≡ post (idn x) t
    η-abs t = absorb-l t ∙ sym (absorb-r t)
```

But neither boundary clause closes. The two obligations are, verbatim,
the two stuck cores of this whole program:

```text
-- NON-CHECKED — the two boundary obligations for (η-abs , _ , _):

  clause-D₀ : η-abs (post (idn x) (idn x))
            ≡ interchange (idn x) (idn x) (idn x) (idn x)
  -- i.e.  absorb-l D₀ ∙ sym (absorb-r D₀) ≡ interchange e e e e.
  -- This IS the model identity (A) of Gloss.PathGroupoid
  -- (`interchange e e e e ≡ pcom.ideml R ∙ sym (pcom.idemr R)`),
  -- read abstractly: the absorb homotopy at D₀ equals interchange.
  -- Not derivable — it is θ-core's ηD₀ obligation. Pointwise
  -- interchange supplies interchange e e e e as ONE value; it does
  -- NOT tell us the total absorb homotopy passes through it.

  clause-e  : η-abs (idn x) ≡ refl
  -- i.e.  absorb-l (idn x) ∙ sym (absorb-r (idn x)) ≡ refl.
  -- The two unit derivations (unit-eqvl vs unit-eqvr) agree at the
  -- identity. This is (B) of Gloss.PathGroupoid
  -- (`pcom.ideml refl ≡ pcom.idemr refl`), read abstractly. Not
  -- derivable: `absorb-l`/`absorb-r` are independent `equiv→lc`
  -- discharges, unequal on the nose.
```

VERDICT (KILL-A): `swap-lift x` is NOT inhabitable from the five
axioms. `η-abs` gives the carrier; both boundary clauses wall at the
naturality that pointwise `interchange` (one value at one point) cannot
supply. The encoding is non-inert.

## (3) GO/NO-GO — R-core from couple²

Two independent facts settle this.

FACT 1 (scope gap). The identity `swap-lift x` above discharges
`θ-core` because `θ-core`'s only interchange input is the identity
self-cell `interchange (idn x) (idn x) (idn x) (idn x)`. But `R-core`'s
interchange input is the MIXED cell `interchange (idn y) g (idn y) b`,
carrying a general `g`. No free structure bridges the mixed cell to the
identity self-cell (`g` does not factor out of `emb g`), so `R-core` is
not a projection of `couple² y`. A `g`-carrying `swap-lift` is required.

FACT 2 (the two-points method is obstructed for ANY `g`-carrying lift
space). We reconstruct `R-core`'s context and probe the memo's stated
route (two points `L = absorb`, `R = interchange`, `is-contr→is-prop`,
project). The natural lift-fiber is `fiber (ap E) Qc` with
`E = pre (idn y)`.

```agda
module Rcore-attempt {o h} (C : hcategory o h) where
  open hcategory C

  module _ {y z v : ob} (g : hom y z) (b : hom z v) where
    private
      E : hom y v → hom y v
      E = pre (idn y)

      c : hom y v
      c = pre g b

      IC : pre (idn y) c ≡ emb g ((y , post (idn y) (idn y)) , (v , b))
      IC = interchange (idn y) g (idn y) b

      AR : emb g ((y , post (idn y) (idn y)) , (v , b)) ≡ c
      AR = ap (λ a' → emb g ((y , a') , (v , b))) (absorb-r (idn y))

      -- Qc is the fiber target: the ap-image of the absorb route.
      Qc : E (E c) ≡ E c
      Qc = ap E (absorb-l c)
```

The absorb route `L` is a free point of `fiber (ap E) Qc`, and that
fiber is contractible from `unit-eqvl` alone (`kill-1`: `E` is an
equivalence, so `ap E` is, so its fibers are contractible). So the
contractibility of THIS space is inert — it cannot be the axiom.

```agda
    L : fiber (ap E) Qc
    L = absorb-l c , refl

    fiber-is-free : is-contr (fiber (ap E) Qc)
    fiber-is-free =
      is-embedding→ap-equiv (is-equiv→is-embedding unit-eqvl)
        .eqv-fibers Qc
```

The interchange route `R = IC ∙ AR` would be the second point — but
its membership obligation is `R-core` itself:

```text
-- NON-CHECKED — the interchange route's fiber-membership obligation:

  R : fiber (ap E) Qc
  R = (IC ∙ AR) , R-core-obligation
      where
        R-core-obligation : ap E (IC ∙ AR) ≡ Qc
        -- = ap-comp E IC AR ∙ (ap E IC ∙ ap E AR ≡ ap E (absorb-l c))
        -- The bracketed part, after equiv→lc-section unfolds Qc, is
        -- exactly CodepTriangleCrux.R-core. So R is a point of the
        -- fiber IFF R-core already holds. Circular.
```

The dichotomy: to make the interchange route a FREE point, the lift
space must not cut down the wild path type `pre (idn y) c ≡ c` (else
membership needs `R-core`); but the uncut wild path type is not
contractible, so `couple²` would be false there (KILL-B). Any cut
tight enough for contractibility is a fiber of an equivalence
(`emb`, `ap emb`, or `ap E`) — inert — and re-imposes `R-core` on the
interchange route. There is no middle encoding for which BOTH routes
are free points of a contractible non-inert space.

VERDICT (3, GO/NO-GO): the memo's "two free points + is-contr→is-prop"
derivation of `R-core` is a **NO-GO** — the interchange-route point is
never constructible without `R-core` itself. `couple²` can still
discharge `R-core` only by DIRECTLY positing the coherence (θ-style, a
total homotopy pinned at two values), which requires a `g`-carrying
overlay strictly larger than the identity `swap-lift` and whose second
pin-point I could not exhibit within budget (see report). So: **GO for
θ-core, NO-GO for R-core by the stated method; R-core is discharged
only by a baked g-carrying coherence, whose construction is open.**

## (5) KILL-B — the path-groupoid model

Inhabiting `swap-lift x` in `path-cat A` reduces EXACTLY to the two
identities (A), (B) of Gloss.PathGroupoid. In the model
`pre (idn x) t = pcom refl refl t` and `post (idn x) t = pcom (sym t)
refl refl` (definitionally), so the model-native slot-swap homotopy is
`η t = pcom.ideml t ∙ sym (pcom.idemr t)`, and:

  * `η (idn x) = pcom.ideml refl ∙ sym (pcom.idemr refl)` — clause-e is
    (B): the two contractions of `R` to `refl` agree.
  * `η (post (idn x)(idn x)) = pcom.ideml R ∙ sym (pcom.idemr R)`,
    `R = pcom refl refl refl` — clause-D₀ is (A): this equals
    `interchange (idn x)^4`.

```agda
module killB {u} (A : Type u) where
  open hcategory (path-cat A)
  open encoding (path-cat A)

  module _ {x : A} where
    R : hom x x
    R = pcom refl refl refl

    η : (t : hom x x) → pre (idn x) t ≡ post (idn x) t
    η t = pcom.ideml t ∙ sym (pcom.idemr t)
```

(B) is clause-e. `pcom.ideml refl` and `pcom.idemr refl` are the same
`HComposite.unique` term (their fillers `λ i j → q (i ∧ j)` and
`λ i j → q (i ∨ ~ j)` both collapse to the constant square at
`q = refl`), so `η refl = p ∙ sym p` and `Path.invr` closes it.

```agda
    clause-e : η (idn x) ≡ refl
    clause-e = Path.invr (pcom.ideml refl)
```

(A) is clause-D₀ — the MUST-PROVE. It is `refl`-REJECTED (verified:
LHS `x`, RHS an `hfil` term — a genuine non-`refl` 2-cell). Concrete
partial progress: the model `interchange (idn x)⁴` is definitionally
the ternary `pcom (sym (lsplit refl refl R)) (lr R R) (sym (rsplit R
refl refl))`, so `pcom→∙` rewrites it to a binary chain. This
typechecks and reduces (A) to a pure `pcom`-filler identity.

```agda
    interchange-binary
      : interchange (idn x) (idn x) (idn x) (idn x)
      ≡ pcom.lsplit refl refl R
        ∙ pcom.lr R R
        ∙ sym (pcom.rsplit R refl refl)
    interchange-binary =
      pcom→∙ (pcom.lsplit refl refl R) (pcom.lr R R)
             (sym (pcom.rsplit R refl refl))
```

So (A) reduces to the checkable-but-unclosed
`pcom.ideml R ∙ sym (pcom.idemr R)
   ≡ pcom.lsplit refl refl R ∙ pcom.lr R R
     ∙ sym (pcom.rsplit R refl refl)`
— relating the `ideml`/`idemr` unit contractions to the
`lsplit`/`lr`/`rsplit` interchange fillers. Genuine multi-`hcom`
algebra; NOT found false (the endpoints match and both are canonical
fillers in the free ∞-groupoid). Full exhibition deferred — this is
the residual model-verification item.

```text
-- NON-CHECKED — (A) residual, and the model swap-lift inhabitant:
  clause-D₀ : η (post (idn x) (idn x))
            ≡ interchange (idn x) (idn x) (idn x) (idn x)
  -- = sym interchange-binary composed with the ideml/idemr↔lsplit/lr/rsplit
  --   identity above.

  model-center : swap-lift (path-cat A) x   -- inhabits the CENTER only
  model-center = η , (clause-D₀ , clause-e)
  -- NB: this is an INHABITANT, not a proof of is-contr. See the
  -- critical finding below: is-contr (swap-lift x) is MODEL-FALSE.
```

## (6) CRITICAL FINDING — the `is-contr` wrapper is MODEL-FALSE

The decisive obstruction, and a correction to BOTH this encoding and
the memo's schematic. `swap-lift x` has the shape

    Σ (η : (t : hom x x) → P t) , (η D₀ ≡ IC) × (η idn ≡ refl)

with `P t = pre (idn x) t ≡ post (idn x) t`. The first component is a
Π over `hom x x`, and the boundary pins `η` at only TWO points. Its
homotopy fiber under the two-point evaluation
`(ev_D₀ , ev_idn) : (Π t , P t) → P D₀ × P idn` is contractible IFF
`P t` is contractible for every `t` off `{D₀, idn}`.

But `P t` is a path space inside `hom x x = x ≡ x`; it is a proposition
only when `x ≡ x` is a set, i.e. only when `A` is a groupoid. For a
path-groupoid over a higher type (`A = S²`, `x ≡ x = Ω S²` is not a
set), `P t` is not a proposition, so `swap-lift x` is NOT a proposition
and `is-contr (swap-lift x)` is FALSE.

So `couple²` as `is-contr (swap-lift x)` is NOT satisfiable by all
path-groupoid models — KILL-B fails at the level of the CONTRACTIBILITY
WRAPPER, not the coherence content. Crucially, this is inherent to
"`is-contr` of a Π-family pinned at finitely many points": the memo's
`Σ η ∶ (∀ {w} (a) → PathP …) , <normalization at a = idn>` has the SAME
Π-over-`a` freedom cut at one point, so it is model-false the same way.

What IS model-true:
  * the COHERENCE CONTENT — (A), (B), θ-core, R-core — holds in every
    path groupoid (they are true 2-cells, the residual (A) included);
  * hence the CENTER exists (model-inhabited via `η` above);
  * but UNIQUENESS (is-contr) does not, because Π-families are wild.

## Corrected axiom shape (identified, not constructed)

The prop-valued overlay must wrap a FIBER that is genuinely a
proposition, not a Π-family. The right shape is representability:

    couple² : … → is-contr (fiber emb T)

for a swap-derived composite `T`. `is-contr (fiber emb T)` is
prop-valued unconditionally (`emb` is an embedding), model-true (`emb`
is an EQUIVALENCE in path groupoids, so surjective — every `T` is hit,
"contract through eqv-fibers" as the memo anticipated), and non-inert
when `T` is not an `emb`-image abstractly (`emb` is NOT surjective from
the five axioms — that is precisely a NEW representability demand,
sibling to `compose-contr`). The open constructive gap: exhibit the `T`
whose representability PROJECTS (via `is-contr→is-set` + `ap fst`, the
`unitl`/`unitr` pattern one rung up) to θ-core and R-core. This spike
did not close that projection.
