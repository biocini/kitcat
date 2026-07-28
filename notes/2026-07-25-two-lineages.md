# Review — 2026-07-25 — `Cat.Logic` against its two lineages

> **Relabelled 2026-07-27.** The polarity labels on the composition
> towers were swapped and the unit tier renamed `is-invertible±`.
> Identifiers below carry the pre-swap names; `src/Cat/Logic/TODO.md`
> records the change and the naming rule now in `Cat.Logic.Type`.
> The resources entry `mangel-classical-notions` is renamed
> `mmmm-classical-notions`, 2026-07-28.

Where the framed deductive-system theory stands with respect to (1) the
reflexive-graph theory of `Cat.Graph.Refl`, after Sterling, and (2) the
Melliès corpus — ribbon tensorial logic, balanced dialogue categories,
dialogue chiralities, and the dialogue duploids of Mangel–Melliès–
Munch-Maccagnoni.

Provenance follows `docs/provenance.md`. VERIFIED names a library module
machine-checked here; SOURCE-CHECKED means the vendored document states the
claim at the cited anchor; CONJECTURED covers every literature claim and every
reading offered here that is not checked. The bridge results reported below
are `Cat.Logic.Graph` and `Cat.Logic.Display`, documented in
`docs/deductive-systems/graphs.md` and `displays.md`, with ledger entries
T25–T31.

---

## 0. The axes are not orthogonal

They intersect in the sources, at one point, and the intersection is
load-bearing.

SOURCE-CHECKED (`mangel-classical-notions`, `article.tex:1526`): a
*non-associative category*, or unital magmoid — the carrier of the whole
duploid development — is defined as **a reflexive graph equipped with a
composition law satisfying only the neutrality equations**. Sterling's carrier
is the duploid line's carrier. The two axes are not two independent readings
of one object; one supplies the substrate the other builds on.

`Cat.Logic.Type` sits below their meeting point, and the reason is exact.

> **A virtual graph is the data of two reflexive graphs on one underlying
> graph, together with `reflect`.**

A twist is a reflexivity datum. VERIFIED (`Cat.Logic.Graph`): `graph⁺` and
`graph⁻` are reflexive graphs sharing vertices and edges, differing only in
which twist is the reflexivity. So against the two sources:

- **Sterling** studies one such graph. The framing is the pair.
- **Mangel** puts a *declared* composition on one such graph, subject to the
  two neutrality equations. `Cat.Logic` declares none — both cuts are
  projections of fibers of `reflect` — and derives one neutrality per hand.

The ladder, with each source at its rung:

```
  reflexive graph                       one reflexivity datum      [Sterling]
    │  a second reflexivity datum
    ▼
  a pair of them                        twist⁺, twist⁻; winding    [ribbon]
    │  + reflect  (two-slot representability)
    ▼
  virtual-graph                         Cat.Logic.Type
    │  + is-stable, is-composable, is-unital
    ▼
  deductive-system                      two associative cuts, one-sided units
    ├── + polarity assignment      ⟶  duploid grade               [Mangel]
    ├── + mediation                ⟶  category  (twists collapse, one cut)
    ├── + pole on the coterm family⟶  dialogue grade              [Melliès]
    └── + tensor/braid/balancing   ⟶  balanced dialogue           [Melliès]
```

---

## 1. The Sterling axis

### 1.1 Two graphs, and the crossing

VERIFIED (`Cat.Logic.Graph`), every claim `refl`:

| | |
| --- | --- |
| `term-is-cofan x` | `term x ≡ rx.cofan (graph⁺ G) x` |
| `coterm-is-fan y` | `coterm y ≡ rx.fan (graph⁺ G) y` |
| `var-is-cofan-center x` | `var x ≡ rx.cofan-center (graph⁻ G) x` |
| `covar-is-fan-center y` | `covar y ≡ rx.fan-center (graph⁺ G) y` |

Fans and cofans name no reflexivity, so the two argument *families* are read
off either graph. The *centres* are not shared: the term half is the centre of
one graph, the coterm half of the other, and the axiom pairs one from each.

That is where the crossing running through the whole theory comes from, and it
is not a sign convention. Each unit tier's target reads one graph's
reflexivity through the other graph's action, and the tier says each
reflexivity is the unique edge sent there — so **the unit tiers are the mutual
comparison of the two graphs**, and the crossed pairing (`pair⁻`, `pair⁺`) is
the index of which graph supplies the centre.

### 1.2 The opposite, and univalence

VERIFIED (`Cat.Logic.Graph`), both `refl`:

```agda
op-graph⁺ G : graph⁺ (opⱽ G) ≡ rx.op (graph⁻ G)
op-graph⁻ G : graph⁻ (opⱽ G) ≡ rx.op (graph⁺ G)
```

The involution is not the reflexive-graph opposite of a single graph; it is the
swap of the two composed with `rx.op`. Both components being fields is what
makes it strict, and strictness is where `docs/gloss.md` T16's identification —
kitcat's `op` as Melliès' `(−)op` — lands better in this layer than in the
record it was stated for, since there the strict involution was the
obstruction (T11, T12).

VERIFIED: `univalence-shared` is `refl`. Univalence is a condition on fans,
which name no reflexivity, so **the two graphs are path objects together and
the framing does not enter the condition**. Being a path object is a property
of the underlying graph alone; what the framing contributes over one is a
*shift* — `to-edge` is built from a reflexivity datum, so the two graphs
present the same identity system with basepoints displaced by the twists.
Section 2.1 reaches the same statement from the ribbon side.

### 1.3 Each hand is a lens over the other hand's graph

A lens states its unitor at its base's reflexive edge, and a hand's action is
stated at the twist its own axiom half does not carry. VERIFIED
(`Cat.Logic.Display`):

```agda
term-lens   : oplax-cov-lens (graph⁻ G) (term-fam   G)   -- unitor = absorb⁺
coterm-lens : lax-ctrv-lens  (graph⁺ G) (coterm-fam G)   -- unitor = absorb⁻
```

The covariant hand transports forward and its cancellation points back at the
vertex; the contravariant hand transports backward and its cancellation points
forward. The two unitor shapes a lens admits are exactly the two absorptions —
which is the sharp form of "the displays are reflexive up to one
transmission": on a bare framing the display has no reflexivity at all, and it
acquires one exactly at the cancellation.

Both families are discrete, so VERIFIED: `term-disp-univalent`,
`coterm-disp-univalent` — both displays are univalent with **no** condition on
the base. That matters, because §1.5 says the base is not in general a path
object and every uniqueness theorem about lens *structure* needs it to be.

A placement fact found along the way and now fixed: the absorptions consume no
tier. They are stated over the two pins and the two cancellation equations
alone, and `Cat.Logic.Base`'s `absorption` now carries them, with the unit-law
module opening rather than restating them.

### 1.4 Each cut is a fibration, and stability is an embedding

VERIFIED (`Cat.Logic.Display`): the coslice display over `graph⁺` takes its
displayed reflexivity from the cancellation alone, and

```agda
coslice-fibration a : rx.is-cov-fibration (graph⁺ G) (coslice a)
```

assembles from stability and the coterm cut — **the tier splits along the two
halves of contractibility**, existence from the cut and uniqueness from
stability. The fibration's operations are the hand's own on the nose:
`push-is-cut` and `lift-is-witness` are `refl`, so the composition *is* the
pushforward and the head-rewriting witness *is* the lift. A free consequence,
from `Cat.Graph.Refl.Fibration`: the coslice is univalent as a display, base
unconstrained.

Separately, VERIFIED (`Cat.Logic.Base`): `stable-is-embedding` is `refl` —
stability is `reflect` having propositional fibers, i.e. being an embedding at
every pair. And over hom-sets the judgments form sets, so

```agda
stable-from-hom-sets
  : (∀ {x y} → is-set (hom x y))
  → (∀ {x y} {m n : hom x y} → eval (reflect m) ≡ eval (reflect n) → m ≡ n)
  → is-stable
```

reduces the tier to injectivity of **transmission** — the edge surrounded by
one twist of each sign. In the truncated regime stability is therefore not a
hypothesis about representation at all; it is a statement about the framing.
This is the shape of O4 in `notes/2026-07-22-deductive-system-design.md`.

### 1.5 What Sterling's theorems reach

The base graph of a deductive system is not univalent: fans propositional
fails wherever an object carries distinct outgoing edges, and §2.4's model
makes that explicit. Every one of Sterling's *coherence* results hypothesises
univalence of the base — `cov-`/`ctrv-`/`unb-lens-structure-is-prop` in
`Cat.Graph.Refl.Lens`, and the classifying path objects and SIP case studies
in `Classify`. So for `Cat.Logic` the Sterling axis is **a language and a set
of constructions, not a theorem supply**.

What does transfer: the vocabulary, the displayed and fibration operations,
the total-opposite duality, and every univalence-of-a-*display* result, since
those hypothesise the components rather than the base — which is why §1.3 and
§1.4's four univalence certificates are unconditional.

One substantive theorem is in reach. `Cat.Graph.Refl.Univalent`'s
`characterisation-of-fibs` assumes no univalence of the base (`TODO.md` §3),
so the fibration ⟺ univalent-lens correspondence applies to the coslice: each
hand's composability data is *equivalent* to a lens of path objects over its
graph. Not yet stated.

### 1.6 A note on the two unitors

SOURCE-CHECKED (`sterling-reflexive-graph-lenses`, `paper.tex:2203`): an
unbiased dependent lens needs only its mid unitor for the display; exactly one
of the lax and oplax unitors may be added, and including **both** breaks
propositionality of fiberwise-univalent unbiased lens structure — the analogy
drawn is half-adjoint equivalences omitting one snake identity.

The framed theory has both absorptions available, so any unbiased presentation
of `judgment` over the one-sided base carries both and claims no
propositionality for the structure. Nothing is lost — a base that is not a
path object had already put it out of reach — but the shape is worth keeping
in view: it is the same reason a coherence tier is wrapped in a
contractibility rather than stated as a pair.

---

## 2. The Melliès axis

### 2.1 The twist is `(θ, θ⁻¹)` with the inverse law dropped

SOURCE-CHECKED (`mellies-ribbon-tensorial-logic`, `l.939`, Definition 6;
`mellies-braided-dialogue`, `l.3066`, Definition 9): a *balanced* category is
a braided monoidal category with a natural twist `θ_A : A → A` satisfying
`θ_I = id_I` and `θ_{A⊗B} = σ ∘ (θ_B ⊗ θ_A) ∘ σ`.

The shape matches. The count appears not to — one θ against two twists — but
θ is invertible in a balanced category, so `θ⁻¹` is a second natural
endo-family and the identification is exact:

> A framing is the pair `(θ, θ⁻¹)` with the inverse law **not imposed**.
> The cancellation is that law.

This lines up with the rest of the fragment. The unit tiers make each twist
the unique centre of the other hand's fiber — mutual inverseness *pinned by
representability* rather than declared — and the cancellation upgrades it to
the equation. Under §1.1's reading the same statement is that the two
reflexive graphs' reflexivity data are mutually inverse.

**The identity is forgotten, not absent.** Melliès' θ deforms an identity in a
category that has one; a framing replaces it. But the identity is recoverable:
over a path object with `reflect` an equivalence, both action maps at an object
are equivalences (the argument halves being contractible by
`is-univalent→op`), so every fiber is contractible — including the one over
the second projection, which is a genuine one-sided unit at *any* framing. The
twist is that unit exactly at the cancellation. DERIVABLE from landed pieces;
not assembled.

**The balancing law is not statable.** `θ_{A⊗B} = σ(θ_B ⊗ θ_A)σ` needs a
tensor and a braiding, and `θ_I = id_I` needs a unit. `Cat.Logic` has none, so
none of Melliès' twist *axioms* live at this layer. What it contributes to the
ribbon program is the bookkeeping instead:

**The winding parity theorem** (`docs/deductive-systems/framing.md`). An
expression built from `n` applications of `reflect` has `2n+1` leaves, so with
`k` payload edges it carries `2n+1−k` twists, whose parity is that of `k+1`.
Hence a statement about one edge can be winding-neutral — this is where the
unit tiers live — a unit law written as "composing with this edge changes
nothing" never can, and a cut of two edges necessarily carries one twist at
its junction, oppositely signed in the two hands. §2.4's model makes the last
clause literal.

This is a framing-number argument at the level of a proof system, with no
monoidal input, and it is the reason each hand gets exactly one unit law. It
is the strongest candidate here for content not in the Melliès corpus, and
equally a plausible re-derivation of framed-tangle parity — a
citation-research item before any novelty claim.

**Ruling input.** Ribbon-arc open ruling 1 asks whether `θ I ≡ refl` is a
field or a theorem. The answer at this level is neither: it is *one equation*,
the framing's own content, with every tier holding either way. That argues for
the monoidal-tier analogue being a separate propositional layer rather than a
field.

### 2.2 The pole: what a coterm is missing

SOURCE-CHECKED (`mellies-dialogue-deformation`, `l.1260`, Definition 2;
`mellies-ribbon-tensorial-logic`, `l.571`, Definition 2): a *tensorial pole*
is an object `⊥` with **both** representations of `C(− ⊗ −, ⊥)`, giving
`x ⊸ ⊥` and `⊥ ⟜ y`. A dialogue category is a monoidal category with a pole.
No compatibility between the two negations is imposed.

The resonance with `reflect` is specific. `judgment x y` is a function of a
term slot and a coterm slot, and `reflect` embeds `hom x y` into it — a
two-slot representability, which `virtual-graphs.md` calls a two-sided Yoneda
embedding. Its two partial applications, one slot held at its axiom, are
`coact-π` and `act-π`. Two representations of one two-slot object, one per
slot, is the pole's φ/ψ pattern.

Where it differs fixes what stage B owes. Melliès' representations land in
**objects**; `reflect`'s land in **judgments**, and there is no `⊥` and no
negation former. A coterm at `y` is `Σ v ∶ ob , hom y v` — a continuation to
an *unnamed* target. So:

> A coterm is a pole-free refutation: the negation of `y` totalised over all
> targets rather than taken at a chosen one. A pole is a distinguished vertex
> through which the coterm family is generated.

That casts the pole as a **cofinality condition on the fan**, in the same
genus as every other tier — a representability statement whose witness is
projected, not a hom-equivalence field. It answers ribbon-arc ruling 3
("representable refutation-composite embedding vs hom-equivalence field") in
favour of the first, in vocabulary the framed theory already has. CONJECTURED;
the exact form, and whether the two negations need two such vertices, is the
design surface stage B owes.

### 2.3 Chiralities: the two-sided base is Sterling's binary product

SOURCE-CHECKED (`mellies-dialogue-chiralities`, `l.902`/`l.2659`;
`mellies-dialogue-deformation`, `l.685`/`l.1970`/`l.898`/`l.2996`): a
*chirality* is a pair `(A, B)` with an adjoint equivalence between `B` and
`A^op`; a *dialogue chirality* adds an adjunction representing a pairing
distributor, with the slot-shifting family χ. The coherence theorems are
biequivalences `Chi ≃ Cat` and `DiaChi ≃ DiaCat`, in both of which the
projection `F ∘ G` is the identity **strictly**, all deformation data sitting
in the comparison.

VERIFIED (`Cat.Logic.Graph`): the base carrying `judgment`'s two variances is

```agda
base = rx.binary-product (rx.op (graph⁻ G)) (graph⁺ G)
```

built from the reflexive-graph suite's own operations — the tautological
chirality, in Sterling's language. And `base-rx-is-axiom` is `refl`:

```agda
rx base (x , y) ≡ (var x .snd , covar y .snd)
```

> **The chirality base's reflexivity datum is the framing, and at a diagonal
> vertex it is the axiom rule as a single edge.**

VERIFIED (`Cat.Logic.Display`): over that base `judgment` is the vertex family
of *one* covariant lens (`judgment-lens`), with transport `bipush`, unitor the
two cancellations together (`bipush-axiom`), and a univalent display. Over the
one-sided base the same family reaches only the unbiased lens with its two
injections. So the mixed variance that forces the unbiased notion is the
one-sidedness of the presentation, and the chirality presentation removes it.
That is a machine-checked instance, in reflexive-graph vocabulary, of Melliès'
thesis that the two-sided presentation is the natural home of the two
negations.

**Interchange is a cospan coherence.** VERIFIED (`Cat.Logic.Display`):

```agda
push-is-composite⁻ f g : bipush (twist⁻ x) g (reflect f) ≡ composite⁻ f g
push-is-composite⁺ f g : bipush f (twist⁺ z) (reflect g) ≡ composite⁺ f g
```

with `cospan-from-cuts` and `cuts-from-cospan` both ways. The sources are
distinct vertices and the legs point the same way. No display of `judgment`
can carry the agreement as an edge — a displayed edge relates data over the
two ends of *one* base edge, and the reflections compared sit at `(x , y)` and
`(y , z)`; a base making those diagonal would make composability reflexive.
That last clause is the argument, 📐, not a formalized impossibility.

And VERIFIED: `bipush-comp` — the transport composes, but onto a base edge
taking the term hand's composition on the backward coordinate and the coterm
hand's on the forward one. **Interchange is the missing functoriality of the
lens**, and a lens is exactly what survives without a mediation: transport and
a unitor, no functoriality.

### 2.4 Duploids, and the model that makes the winding literal

SOURCE-CHECKED (`mangel-classical-notions`, `article.tex`):

- `l.1551–1570` — a path `(f,g,h)` *associates* when `(h∘g)∘f = h∘(g∘f)`. `f`
  is **thunkable** when every length-3 path starting with `f` associates; `h`
  is **linear** when every one ending with `h` does.
- `l.1694` — `X` is *positive* when every map out of it is linear, *negative*
  when every map into it is thunkable; `(−)^op` reverses polarity.
- `l.1712` — a *positive shift* gives each `X` an object `⇓X` with a thunkable
  epi `ω_X`, universal among maps out of `X` for factorisation through a
  **linear** map; a negative shift is a positive shift on `M^op`.
- `l.1819` — a **duploid** is a non-associative category with both shifts in
  which every object is positive or negative.
- `l.830–1058` — the duploid of an adjunction: `g ∘ f` is defined **in two
  different ways depending on the polarity of the middle object** — push the
  right factor down when positive, pull the left factor up when negative.
- `l.3036` — central and thunkable maps coincide in a dialogue duploid.

**The two protocols are the two cuts.** `composite⁻ f g` keeps `f` as the
reflected head and transports `g` onto the coterm slot; `composite⁺ f g` keeps
`g` as the head and transports `f` onto the term slot. Which factor stays the
head and which is transported is Mangel's push/pull split.

| | duploid | deductive system |
| --- | --- | --- |
| choice of protocol | forced by the middle object's polarity | free; both available everywhere |
| compositions | one, two notations | two operations |
| unitality | two-sided | one law per hand, on opposite sides |
| associativity | fails in general | holds per hand, with the pentagon |

So a duploid is a deductive system **plus a polarity assignment** selecting a
hand at each object, which sharpens `notes/2026-07-22`'s "duploid-grade = D +
a polarity-partial mediation" into a function on objects with composition
`f ⨾^{pol y} g`.

**The defects are inverted, and it relocates the content.** Duploids put the
failure in associativity and keep two-sided units; the framed theory puts it
in unitality and keeps full associativity per hand. Consequence:

> thunkable and linear, as literally defined, are **vacuous per hand**. Every
> same-hand length-3 path associates. Their content is entirely mixed words.

And the mixed word is identifiable. In Mangel's own example (`l.1000–1058`)
both bracketings use the same two hands in swapped bracket positions, so the
non-associativity instance is the **mixed-bracket cell**, now VERIFIED as
well-formed in `Cat.Logic.Base`'s `tower`:

```agda
mixed-assoc   f g h : (f ⨾⁺ g) ⨾⁻ h ≡ f ⨾⁺ (g ⨾⁻ h)
mixed-leading f     : ∀ g h → mixed-assoc f g h
mixed-trailing h    : ∀ f g → mixed-assoc f g h
```

Nothing above inhabits them; a mediation does, since it makes both bracketings
instances of `assoc⁻`. The duploid names are withheld until the sign
correspondence is pinned: Mangel writes `g ∘ f` right-to-left with `±`
indexing the *middle object's polarity*, while `Cat.Logic`'s `±` indexes which
argument slot the second factor enters, and the registers cross — the `⁻` hand
is the one whose coslice is a *covariant* fibration. Pinning it needs an
instance, not an assertion.

**The model.** VERIFIED (`Test.FramedGroup`): an abelian group read as a
one-object virtual graph, framed by an arbitrary *pair* of its elements,
satisfies every tier — `system : deductive-system`. A fan there is the whole
group, so `univalent→prop` shows the graph is a path object only when the
group is a proposition. This is the first framed model off the path-object
boundary, and it makes two of the theory's conditions arithmetic:

```agda
→cancels    / cancels→    : the cancellation  ⟺  t⁻ · t⁺ ≡ e
→cuts-agree / cuts-agree→ : the cuts agree    ⟺  t⁻ ≡ t⁺
```

So the two cuts differ there by exactly the framing's own discrepancy — the
"opposite windings at the junction" of `framing.md`, made completely explicit
— and `both→` says holding both forces each element to be its own inverse.
Instantiated at ℤ the framing is a pair of integers and the discrepancy is
their difference; the instantiation is not done because `Core.Data.Int` has no
arithmetic laws (O6 in `notes/2026-07-22`).

**The shifts are natively in the house idiom.** Mangel's positive shift is a
universal factorisation — a unique linear `f†` with `f = f† ∘ ω_X` — and
uniqueness-of-a-factorisation is what `is-composable` and `is-stable` already
are: a contractible fiber whose centre is projected. The shifts transcribe
directly, as contractibility of a fiber of precomposition with `ω`, rather
than as declared structure with laws. That is the strongest argument for the
duploid layer sitting over `deductive-system` rather than beside it.

**Hasegawa–Thielecke is not reachable here.** Central = thunkable needs
centrality, hence a tensor and a braiding. This layer supplies the thunkable
half — pole-free and tensor-free — and nothing more.

---

## 3. Corrections made

### 3.1 `mediation.md`'s dichotomy

VERIFIED (`Cat.Logic.Base`): the derivation of `twists-agree` uses a left and
a right unit for *one* composition, so it goes through on either missing unit
law alone, with no interchange:

```agda
collapse⁻ : (∀ {x y} (g : hom x y) → twist⁻ x ⨾⁻ g ≡ g) → ∀ x → twist⁻ x ≡ twist⁺ x
collapse⁺ : (∀ {x y} (f : hom x y) → f ⨾⁺ twist⁺ y ≡ f) → ∀ x → twist⁻ x ≡ twist⁺ x
```

Since a mediation *supplies* those laws, each hypothesis is weaker as a
statement than interchange, and two collapses have to be told apart: **framing
collapse** (the twists are one edge) and **cut collapse** (the compositions
are one operation). Interchange gives both; a missing unit law gives only the
first, and nothing in the theory carries it to the second. The document's
"there is nothing between" is corrected accordingly, and the narrower claim it
also makes — no *shared* two-sided unit for *both* cuts with distinct twists —
stands.

Whether the two are separable is OPEN, and the group model constrains the
search rather than settling it: there they are equivalent, because `reflect`
is an associative product, so the cuts differ only by the junction's twist and
identifying the twists identifies them. A separating model needs a `reflect`
not of that form. Recorded as T30's ⚠️.

### 3.2 The ledger and the decomposition note

`docs/gloss.md` carried no entry for any of this. Section 7 now holds T25–T31:
the tiers' propositionality and the involution, the two graphs, the lenses and
the fibration reading, stability-as-embedding, interchange-as-cospan, the
collapse separation, and the group model. All are machine-checked in the
working tree and not commit-pinned; the section says so.

`notes/2026-07-25-cat-logic-decomposition.md` recorded layers 2 and 5 as
unplaced with a dependency knot between two spike copies of the tiers. The
knot was worse than recorded: the spikes inline a carrier with a *single*
chosen edge, so they state facts about a carrier the library does not have and
are superseded rather than promotable. The note now says so, and layers 2 and
5 have landed.

### 3.3 Placement left open

`Test.FramedGroup` sits beside the path-groupoid witness in `Test/`. Whether
framed models get a library home is undecided and is not a call to make in
passing.

---

## 4. What remains

Two openings need a ruling before code, both because they mint records against
questions already open on the ribbon arc:

**(a) The pole** — as a cofinality condition on the coterm family rather than
a hom-equivalence field (§2.2). This is ribbon-arc ruling 3.

**(b) The shifts** — as contractible fibers of precomposition (§2.4), which is
the duploid grade and roadmap Phase 4's substrate.

Three are open problems rather than tasks:

**(c)** Separating framing collapse from cut collapse, or proving them
equivalent (§3.1). The group model says where not to look.

**(d)** Pinning the sign correspondence between Mangel's polarity index and
the hand index, by an instance (§2.4).

**(e)** Stating each hand's composability as a lens of path objects through
`characterisation-of-fibs` (§1.5) — the one substantive Sterling theorem in
reach at the tiers.

And one is Lane's alone: the framework still has no project or gate in
`docs/roadmap.md`, which `notes/2026-07-25-cat-logic-decomposition.md` also
flags. Re-gating is a ruling.
