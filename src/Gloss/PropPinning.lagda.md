Lane Biocini
July 2026

Gloss: machine-checked evidence for T13(ii)/(iii) in docs/gloss.md.
Self-contained modulo Core.* and Gloss.PathGroupoid (whose frozen
`hcategory` this builds on); no Cat.* import.

Can a proposition-valued predicate on the five hcategory axioms
pin the coherence cells? This certificate examines the natural
candidate — a contractibility axiom `couple²` over a space of
pinned homotopies — and establishes three findings, which
together supply the machine-checked part of two clauses of a
trichotomy: every prop-valued candidate is blind to the twist
(that clause rests on `Gloss.PathGroupoid`), obstructed in what
it can discharge, or false in the intended models.

First, the encoding is not inert: the space `swap-lift` is not
inhabitable from the five axioms — the only available total
homotopy is the absorption route, and its two boundary
obligations are exactly the two stuck coherences (module
`absorb-route`); by contrast, `θ-core` does follow from `couple²`
(module `theta`), by one naturality square collapsed at the two
pins.

Second, the same method cannot reach `R-core`: any lift space
tight enough to be contractible is a fiber of an equivalence —
hence inert, already contractible from the axioms — and
re-imposes `R-core` as the membership obligation of the
interchange route (module `Rcore-attempt`; the dichotomy is
stated in full below).

Third, the decisive correction: the `is-contr` wrapper over a
Π-family pinned at finitely many points is FALSE in
path-groupoid models over higher types — off the pinned points
the family's values range over wild path spaces — so this entire
encoding class is model-false, even though its coherence CONTENT
holds in every path groupoid (module `path-model` inhabits the
center).

The corrected axiom shape — representability,
`is-contr (fiber emb T)`, of a swap-derived composite, which is
prop-valued unconditionally and model-true — is identified in the
final section; exhibiting the composite `T` whose
representability projects to the two coherences remains open. One
boundary the reader should carry: that these clauses exhaust the
candidate space is argued, not machine-checked.

The unifying discovery behind this file (recorded up front so the
code below can be read against it):

BOTH `θ-core` and `R-core` are instances of ONE statement — the
natural slot-swap homotopy between the *pre-action* and the
*post-action* of an identity agrees with `interchange` at the
doubly-centered point and with `refl` at the identity. Writing
`Ψ a b := emb e ((x,a),(x,b))` for `e = idn x` and `D₀ := Ψ e e`:

  * `θ-core` is
      `ap (pre e) pe ≡ interchange e e e e ∙ ap (post e) pe`
    with `pe = post-eval e : D₀ ≡ e` — the reconciliation, at the
    identity, of the two transports of the evaluation law. This is
    exactly `homotopy-natural η pe` for a homotopy
    `η : pre e ⟹ post e` with `η D₀ = interchange e e e e` and
    `η e = refl`.

  * `R-core` is the mixed-argument sibling, lifted through the
    equivalence `ap (pre (idn y))`: at a general point
    `c = pre g b`, it says the unit-route proof of
    `pre (idn y) c ≡ c` (the absorption path) agrees with the
    interchange-route proof (`IC ∙ AR` in the notation of module
    `Rcore-attempt` below). Same slot-swap coherence, smeared
    over the context `c`.

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
open import Core.Homotopy using (homotopy-natural)
open import Core.Equiv.Base using (is-equiv; iso→equiv; eqv-fibers)
open import Core.Function.Embedding
  using ( equiv→lc; equiv→lc-section
        ; is-embedding→ap-equiv; is-equiv→is-embedding )

open import Gloss.PathGroupoid using (hcategory; path-cat)
```

## The encoding: the slot-swap homotopy at an identity endo

`swap-lift e` (for an endo `e : hom x x`) is the space of homotopies
`η` between the pre-action `pre e` and the post-action `post e`, both
read as endofunctions of `hom x x` (`pre e t = emb e ((x,idn),(x,t))`
puts `t` in the fam slot; `post e t = emb e ((x,t),(x,idn))` puts it
in the cofam slot). The two boundary clauses pin `η` at the identity
(`refl`) and at the doubly-centered point `D₀ = post e (idn x)`
(the `interchange` cell). At `e = idn x` the boundary types line up
definitionally: `interchange e e e e : pre e D₀ ≡ post e D₀`.

Design note. `η` ranges over ALL of `hom x x`, and the two
boundary values sit at two distinct points; this is why the space
is not inert — and inertness disqualifies a candidate, since an
axiom whose content is already derivable pins nothing. The
pointwise `interchange` supplies the value at `D₀`, and the unit
structure supplies `refl` at `e`, but no total homotopy carrying
BOTH prescribed values is constructible from the five axioms.

Rejected encodings (one line each):
  * `fiber emb T` / `fiber (ap emb) Θ` — INERT: `emb` is an embedding
    (`emb-image-contr`), so `ap emb` is an equivalence and every such
    fiber is already contractible from the five axioms.
  * `Σ p ∶ (pre(idn) c ≡ c) , ap (pre idn) p ≡ Qc`
    = `fiber (ap (pre idn)) Qc`
    — INERT for the same reason (`unit-eqvl` makes `ap (pre idn)` an
    equivalence; this is `ap-pre-inert` of `Gloss.PathGroupoid`).
  * `Σ η , (η ≡ interchange)` — INERT: a singleton around `interchange`.
  * plain `pre(idn) c ≡ c` (no cut) — the opposite failure: a wild
    (untruncated) path space, NOT contractible; the axiom would be
    false in the intended models.
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

The candidate axiom, packaged: `couple²` asserts that the space
of pinned slot-swap homotopies is contractible at every object.

```agda
record level-2-representable {o h} (C : hcategory o h) : Type (o ⊔ h) where
  no-eta-equality
  open hcategory C
  open encoding C
  field
    couple² : (x : ob) → is-contr (swap-lift x)
```

## θ-core follows from couple²

`θ-core` is the naturality square of the slot-swap homotopy along
`post-eval e`, collapsed by the two boundary clauses. It is
`homotopy-natural η (post-eval e)` with `η e = refl` and
`η D₀ = interchange e e e e`.

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

This θ-core has exactly the type consumed downstream
(`ap (pre e) (post-eval e) ≡ interchange e e e e ∙ ap (post e)
(post-eval e)`, `e = idn x`): the derivation reconciling the
opposite idempotent with the base one — the `θ-derivation` chain
in `Gloss.EightFieldWall`, whose κ / M-B≡M-A / ξ / θ definitions
consume only a θ-core of this type — could take `couple²` as its
source without further change.

## Non-inertness: swap-lift is not inhabitable from the five axioms

The honest inhabitant attempt. The only total homotopy
`pre (idn x) ⟹ post (idn x)` the five axioms furnish is the absorb
route `η-abs t = absorb-l t ∙ sym (absorb-r t)` (both actions cancel
the identity, so the composite crosses through `t`). This typechecks.

```agda
module absorb-route {o h} (C : hcategory o h) where
  open hcategory C

  module _ {x : ob} where
    η-abs : (t : hom x x) → pre (idn x) t ≡ post (idn x) t
    η-abs t = absorb-l t ∙ sym (absorb-r t)
```

But neither boundary clause closes. The two obligations are,
verbatim, the two stuck coherences themselves:

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

So `swap-lift x` is not inhabitable from the five axioms: `η-abs`
gives the carrier, and both boundary clauses demand a naturality
that pointwise `interchange` — one value at one point — cannot
supply. The encoding is therefore not inert: an axiom asserting
its contractibility says something the five axioms do not already
say.

## R-core: the same method is obstructed

Two independent facts settle this.

FACT 1 (scope gap). The identity `swap-lift x` above discharges
`θ-core` because `θ-core`'s only interchange input is the identity
self-cell `interchange (idn x) (idn x) (idn x) (idn x)`. But `R-core`'s
interchange input is the MIXED cell `interchange (idn y) g (idn y) b`,
carrying a general `g`. No free structure bridges the mixed cell to the
identity self-cell (`g` does not factor out of `emb g`), so `R-core` is
not a projection of `couple² y`. A `g`-carrying `swap-lift` is required.

FACT 2 (the two-points method is obstructed for ANY `g`-carrying
lift space). We reconstruct `R-core`'s context and probe the
natural route: exhibit two points of one contractible space — the
absorption route `L` and the interchange route `R` — identify
them by `is-contr→is-prop`, and project. The natural lift-fiber
is `fiber (ap E) Qc` with `E = pre (idn y)`.

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
fiber is contractible from `unit-eqvl` alone (`ap-pre-inert`: `E`
is an equivalence, so `ap E` is, so its fibers are contractible).
So the contractibility of THIS space is inert — it cannot be the
axiom.

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
        -- exactly R-core. So R is a point of the fiber IFF R-core
        -- already holds. Circular.
```

The dichotomy: to make the interchange route a FREE point, the
lift space must not cut down the wild path type
`pre (idn y) c ≡ c` (else membership needs `R-core`); but the
uncut wild path type is not contractible, so `couple²` would be
false there. Any cut tight enough for contractibility is a fiber
of an equivalence (`emb`, `ap emb`, or `ap E`) — inert — and
re-imposes `R-core` on the interchange route. There is no middle
encoding for which BOTH routes are free points of a contractible
non-inert space.

The conclusion: a two-free-points derivation of `R-core` is
impossible — the interchange-route point is never constructible
without `R-core` itself. `couple²` can still discharge `R-core`
only by DIRECTLY positing the coherence (as with θ: a total
homotopy pinned at two prescribed values), which requires a
`g`-carrying overlay strictly larger than the identity
`swap-lift`; this certificate does not exhibit its second
pin-point, and constructing it is open. In sum: `couple²`
discharges `θ-core`; it does not reach `R-core` by this method;
and a `g`-carrying coherence field would be a genuinely new
posit.

## The path-groupoid model: the content is true

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
module path-model {u} (A : Type u) where
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

(A) is clause-D₀ — the load-bearing obligation. The `refl` probe
rejects it (the left side is the point `x`, the right an `hfil`
term): a genuine non-`refl` 2-cell. Concrete partial progress:
the model `interchange (idn x)⁴` is definitionally the ternary
`pcom (sym (lsplit refl refl R)) (lr R R) (sym (rsplit R
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

## The `is-contr` wrapper is false in higher models

The decisive obstruction, and a correction to the entire encoding
class. `swap-lift x` has the shape

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

So `couple²` as `is-contr (swap-lift x)` is NOT satisfiable by
all path-groupoid models — the model failure is at the level of
the CONTRACTIBILITY WRAPPER, not the coherence content. And it is
inherent to "`is-contr` of a Π-family pinned at finitely many
points": any variant
`Σ η ∶ (∀ {w} (a) → PathP …) , <pins>` has the SAME Π-over-`a`
freedom cut at finitely many points, so it is model-false the
same way. This refutes the entire encoding class, not one
formulation.

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
prop-valued unconditionally (`emb` is an embedding), model-true
(`emb` is an EQUIVALENCE in path groupoids, so surjective — every
`T` is hit, and the fiber contracts through `eqv-fibers`), and
non-inert when `T` is not an `emb`-image abstractly (`emb` is NOT
surjective from the five axioms — that is precisely a NEW
representability demand, sibling to `compose-contr`). The open
constructive gap: exhibit the `T` whose representability PROJECTS
(via `is-contr→is-set` + `ap fst`, the `unitl`/`unitr` pattern
one rung up) to θ-core and R-core. This certificate does not
close that projection.
