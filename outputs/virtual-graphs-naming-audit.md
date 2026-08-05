# Naming audit: Bb.VirtualGraphs

Every named phenomenon in the thirty modules of `src/Bb/VirtualGraphs/`,
checked against established usage in category theory, homotopy type
theory, type theory, and mathematical logic. The audit proposes. It
renames nothing.

## The test

A name is not audited by asking whether a reader could guess the right
sense. It is audited by asking whether the machine-checked content
establishes the properties that the cited concept requires.

Two questions per name.

1. **Definitional fidelity.** Does the corpus prove what the established
   concept demands, in the general case the corpus works in, and not only
   in a degenerate special case?
2. **Face-value hazard.** If a future reader or a future agent takes the
   name as vetted, which theorems of the established literature will they
   assume the object has already earned?

Question 2 is the operative one. This tree is a consolidation meant to
prepare a definition that does not yet exist. A name that imports a
settled concept invites a later worker to import that concept's theorems
with it. Where the corpus has not earned them, the name is a liability
and not a label. Documented intent does not lower a verdict. Intent
explains why a name is present. It is not evidence that the object
satisfies the concept.

Verdicts. **MATCHES**: the corpus proves the concept's defining
condition, and this audit names which condition it checked. **EXTENDS**:
compatible, with a deviation the prose states, and no theorem falsely
implied. **CONFLICTS**: taking the name at face value leads a reader to
assume properties the corpus does not establish, or actively refutes.
**SAFE**: no established sense to clash with.

## Summary

| Name | Verdict | What a reader would wrongly assume |
| --- | --- | --- |
| `Balanced`, `tower.balanced` | **CONFLICTS** | A twist natural against a braiding. The tree has no tensor and no braiding, so the defining law is not statable, and `pair⁺` refutes the invertibility it needs. |
| `twist⁺`, `twist⁻` | **CONFLICTS** | A ribbon twist. `pair⁺` proves the composite of the two twists is `twist⁻`, not a unit. Naturality holds only where it is empty. |
| `is-invertible⁺`, `is-invertible⁻` | **CONFLICTS** | A two-sided inverse. The tier gives one-sided absorption, and the corpus proves the twists do not compose to a unit. |
| `is-stable`, `Stability` | **CONFLICTS** | Finite limits and colimits, fiber sequences, a triangulated homotopy category. The predicate is `is-embedding reflect`, proved by `refl`. |
| `is-interchanging`, `Interchange` | **CONFLICTS** | The middle-four exchange, and 2-categorical coherence with it. The predicate equates two compositions of the same dimension. |
| `composable⁺/⁻`, `cut⁺/⁻` in two models | **INCONSISTENT (internal)** | `Groupoid.Path` and `Group.Abelian` name each cut for the twist it mediates with, inverting the tree's rule. Both files use the correct form elsewhere. |
| `Framing`, `framing⁺/⁻` | EXTENDS | Resemblance only. No fibrational or double-categorical content, and none implied. |
| `readback`, `Readback` | EXTENDS | A normalization algorithm or a normalization theorem. The module proves one retraction equation. |
| `Presentation` | EXTENDS | Generators and relations. There is no free construction and no quotient. |
| `judgment` | EXTENDS | Proof-theoretic results (cut elimination, subject reduction). None exist. |
| `is-neutral` | EXTENDS | The normalization sense (a stuck term), which `readback` invites in the same file. |
| `coterm` | EXTENDS | Verified against a secondary description only. The primary source resisted extraction twice. |
| `Display`, `coslice`, `slice` | EXTENDS | Displayed-category theorems. The base here is a reflexive graph, not a category. |
| `Extraction` | EXTENDS | Coq-style program extraction. The module projects a field from a fiber centre. |
| `Torsor` | EXTENDS | A group action and a shear isomorphism. Neither is built. |
| `thunkable`, `linear` | MATCHES | Checked: the pre-duploid associativity equations, term by term, in diagrammatic order. |
| `positive`, `negative` | MATCHES | Checked: the derived form at `article.tex:1694-1700`, which is not the duploid paper's Definition 1. |
| `Pentagon` | MATCHES | Checked: the pentagon diagram for `assoc⁺`. One hand only. |
| `Bool.Heap` | MATCHES | Checked: both heap axioms, and `a·b⁻¹·c` reduced over the two-element group. |
| `unital`, `is-unital` | MATCHES | Checked: all four unit laws proved in `Aligned.pinned`. |
| `Bool.Klein`, `Word`, `magmoid` | MATCHES | Checked: the group table, the generation theorem, the nLab definition. |
| `cut⁺`, `cut⁻`, `is-composable⁺/⁻` | MATCHES | Checked: cut as composition. No cut-elimination theorem is claimed or earned. |
| `Aligned` | SAFE, weak | Nothing. The name states a hypothesis, not the theorem. |
| `Engine`, `Tower`, `UnitShape`, `argument`, `term`, `conclusion` | SAFE | Nothing. |
| `Type`, `Graph`, `Carrier`, `Model`, `Defect`, `Shift`, `Readers` | SAFE | Nothing. |
| `virtual-graph` | SAFE, and apt | Nothing. The Cruttwell-Shulman sense of "virtual" fits the object. |

## CONFLICTS

### `Balanced`

**What the concept requires.** A twist, or balance, on a braided monoidal
category is a natural family of isomorphisms `θ_A : A → A` with
`θ_I = id`, subject to a compatibility square against the braiding. A
balanced monoidal category is a braided monoidal category carrying such a
twist (Selinger,
`resources/selinger-graphical-languages/graphical.tex:1074-1148`, after
Joyal and Street 1993). Three things carry that definition: a tensor
product, a braiding, and naturality of `θ` against the two.

Separately, and unrelated, the nLab page titled exactly `balanced
category` defines a balanced category as one where every morphism both
monic and epic is an isomorphism
(https://ncatlab.org/nlab/show/balanced+category).

**What the corpus proves.** `Balanced.lagda.md:38-95` takes readback and
the two invertibility tiers, and derives: each tier centre reads back as
the other twist (`centre⁻-twist⁺`, `centre⁺-twist⁻`), two cancellations
(`cancel⁻`, `cancel⁺`), two absorptions (`absorb⁻ : coact (twist⁺ y) k ≡ k`
and `absorb⁺ : act (twist⁻ x) t ≡ t`), and one far unit law per hand
(`unitl⁺`, `unitr⁻`). The result is two two-sided-unital magmoids on one
graph, offset by the double twist. That content is real, and the module
prose describes it correctly.

**Verdict: CONFLICTS**, on definitional fidelity, not on ambiguity.

The tree contains no tensor product and no braiding. A search for
`tensor`, `braid`, `monoidal`, and `⊗` across all thirty modules returns
one hit, in `TODO.md`, pointing at literature not yet vendored. So the
compatibility square that makes a twist a balance is not merely unproved
here. It is not statable, because the corpus lacks every ingredient the
statement needs.

The corpus also refutes the fragment of the concept it can state.
`Tower.lagda.md:318-319` proves

```
pair⁺ : twist⁻ x ⨾⁺ twist⁺ x ≡ twist⁻ x
```

and `Interchange.lagda.md:334-335` writes the tortile invertibility
demand as

```
inverse⁻ = ∀ x → twist⁻ x ⨾⁺ twist⁺ x ≡ twist⁺ x
```

The corpus proves the composite is `twist⁻`. The concept requires it to
be the unit of that hand, which is `twist⁺`. The two agree only when the
twists are one edge, and `inverse⁻-collapses`
(`Interchange.lagda.md:340-341`) proves exactly that: assuming the
tortile law forces `twist⁻ x ≡ twist⁺ x`. `inverse⁺-collapses` and
`twist-interchange-collapses` reach the same conclusion from the other
two directions.

So the correct statement is not that the name is ambiguous and the intent
was sound. It is that the name asserts a correspondence to an established
concept, and this corpus's own machine-checked proofs show the
correspondence fails outside a degenerate collapse. Inside that collapse
the two twists become one edge and the whole two-hand theory reduces to
an ordinary category, which is the `Aligned` case and not the subject of
this module.

**Face-value hazard.** A later worker who reads `Balanced` as vetted will
assume the twist is invertible, that it is natural, and that the
coherence theorem for balanced monoidal categories (Joyal and Street,
Theorem 4.5) applies. The first is refuted by `pair⁺`. The second is
addressed under `twist⁺`, `twist⁻` below. The third has no premises to
stand on.

Documented intent is on record at `src/Cat/Logic/Type.lagda.md:84-85`,
`Gist/FramedInterchange.lagda.md:1-6`, and `docs/roadmap.md:46-53`. Under
the test above it changes nothing.

**Alternatives.** Each names content the corpus proves.

- `Absorption`. The module's own `absorb⁻` and `absorb⁺` are the engine,
  and absorption is the true relation between the twists. Each is neutral
  for one of the two actions.
- `Cancellation`. `cancel⁻` and `cancel⁺` at `Balanced.lagda.md:56-62`,
  from which the rest follows. The corpus's prose already says "both
  cancellation orders".
- `FarUnits`. Names the deliverable. Each hand gains the unit law
  readback does not reach. "Far" and "near" are the tree's own vocabulary
  (`Readback.lagda.md:108-114`).
- `PerHandUnit`. States the conclusion directly. One two-sided unit per
  hand, and the two hands stay apart.

Withdrawn: `MutualInverse` and `TwistInverse`, which an earlier pass of
this audit proposed. `pair⁺` and `pair⁻` refute them. The twists are not
mutually inverse. Also rejected: `Ribbon` and `Tortile`, which name
strictly more structure and would repeat the error at greater cost.

### `twist⁺`, `twist⁻`

**What the concept requires.** A twist is a natural isomorphism from the
identity functor to itself. Naturality and invertibility are the content.

**What the corpus proves.** Two families of endo-edges filling the two
argument slots (`Framing.lagda.md:44-54`, `:96-106`). On invertibility,
see `pair⁺` above. On naturality, `Interchange.lagda.md:346-356` states
the two naturality laws and then proves

```
natural⁻-is-unitl : natural⁻ → ∀ f → twist⁺ x ⨾⁺ f ≡ f
natural⁺-is-unitr : natural⁺ → ∀ f → f ⨾⁻ twist⁻ y ≡ f
```

**Verdict: CONFLICTS.** An earlier pass of this audit wrote that the
families "are not natural, and they are not mutually inverse until the
`Balanced` layer makes them so". That sentence runs three distinct
conditions together and is wrong on two. The corrected reading:

- The `Balanced` layer does **not** make the twists mutually inverse.
  `pair⁺` and `pair⁻` show the composite lands on a twist, not on a unit.
- The `Balanced` layer does **not** make them equal. Equality is
  `collapse⁺` and `collapse⁻` (`Tower.lagda.md:173-181`), which consume a
  crossed pairing together with a far unit law, and which deliver the
  degenerate `Aligned` case.
- The `Balanced` layer makes each twist a two-sided unit for its own
  hand. Naturality then becomes derivable, and empty. Both sides of
  `natural⁻` reduce to `f`, because `twist⁺` has become a unit for the
  `⁺` hand. `Interchange.lagda.md:311-315` says so in prose: the tortile
  naturality law "carries no twist content there, because the edge it
  speaks about occupies the unit's place."

So naturality never holds contentfully. Where it holds, it holds because
the twist has stopped behaving like a twist.

**Face-value hazard.** A later worker will assume `θ` is invertible and
natural, and will reach for ribbon-category machinery. No rename is
proposed. The fields carry real information about the program's
direction, and `src/Cat/Logic/Type.lagda.md:81-104` explains the sign
discipline. What the fields need is the gap recorded at every definition
site, not only in `Cat.Logic.Type`, with
`Bb/WeakDeductiveSystem/Gist/TwistFidelity.lagda.md` cited where they are
declared.

### `is-invertible⁺`, `is-invertible⁻`

**What the concept requires.** An invertible morphism has a two-sided
inverse.

**What the corpus proves.** `Framing.lagda.md:63-64`:
`is-invertible⁻ = ∀ x → is-contr (fiber (coact-π {x} {x}) snd)`. The
centre is an edge whose coaction is the identity action.
`src/Cat/Logic/Base.lagda.md:87-94` gives the honest reading. The tier
says the centre is a right inverse on one side, and "nothing here says a
centre is the other twist".

**Verdict: CONFLICTS.** An earlier pass called this EXTENDS, because the
one-sidedness is marked in prose. Under the fidelity test that is not
enough. The condition is not invertibility of a morphism. It is
contractibility of one action fiber, which yields absorption on one side
and nothing on the other. The corpus then proves that the two twists do
**not** compose to a unit (`pair⁺`, `pair⁻`), so the reading a reader
reconstructs from the name is refuted rather than merely unproved.

`is-absorbing⁻` and `is-absorbing⁺` would name what the tiers deliver,
and would match `absorb⁻` and `absorb⁺` downstream.
`is-one-sided-invertible` is the smaller edit and keeps the current word.

### `is-stable`, `Stability`

**What the concept requires.** A stable ∞-category is pointed, has finite
limits and colimits, and every pullback square is a pushout square
(https://ncatlab.org/nlab/show/stable+(infinity,1)-category, and Lurie,
*Higher Algebra*, Chapter 1). Its homotopy category is triangulated.
Separately, stability under pullback is closure of a class of morphisms
under pullback (https://ncatlab.org/nlab/show/stability+under+pullback).
Separately again, a stable theory in model theory, after Shelah.

**What the corpus proves.** `Stability.lagda.md:62-63`:
`is-stable = ∀ {x y} (α : judgment x y) → is-prop (is-representable α)`.
`Stability.lagda.md:77-78` then settles what this is, by `refl`:

```
stable-is-embedding : is-stable ≡ (∀ {x y} → is-embedding (reflect {x} {y}))
```

**Verdict: CONFLICTS.** The literature pass found no source that calls an
embedding condition, or a propositional-fiber condition, stability. The
word sits on the most heavily loaded adjective available for a
category-like object, and the true name already sits in the file.

**Face-value hazard.** A reader who knows Lurie will assume finite limits
and colimits, fiber sequences, and a triangulated homotopy category. The
tree has none of these and claims none. The hazard is pure assumption
transfer, with nothing in the name to arrest it.

**Alternatives.**

- `reflect-is-embedding`, in a module named `Embedding` or
  `Representation`. This is the definition under another name, already
  proved by `refl`.
- `is-faithful`, in a module named `Faithful`. Standard for a map
  injective on homs. The cost: `reflect` is not a functor.
- `is-univocal`, in a module named `Univocity`. A fresh word with no
  categorical claim on it, saying "at most one representation".
- `Representation` as the module name, keeping `is-representable` and
  `normal` where they sit and renaming only the tier.

### `is-interchanging`, `Interchange`

**What the concept requires.** The interchange or exchange law relates
compositions of different dimension. For 2-categories it is the
middle-four identity between horizontal and vertical composition of
2-cells (https://ncatlab.org/nlab/show/interchange+law).

**What the corpus proves.** `Interchange.lagda.md:41-43`:
`is-interchanging = ∀ f g → composite⁺ f g ≡ composite⁻ f g`. Two
compositions of the same dimension are asked to agree.

**Verdict: CONFLICTS.** An earlier pass called this EXTENDS, because the
Eckmann-Hilton neighborhood is right. Under the fidelity test the
neighborhood does not carry the name. kitcat's condition is not the
interchange law, not a special case of it, and not a consequence of it.
It is a different statement about a different situation.

**Face-value hazard.** A reader assumes the tree has two-dimensional
structure, and with it the coherence the interchange law buys. The tree
has one dimension and two operations on it. `cuts-agree` states the
predicate exactly.

The name is not empty of value. `neutral-unit`
(`Interchange.lagda.md:252-302`) does run an Eckmann-Hilton-shaped
argument, deriving that the twists agree and the two cuts collapse. But
the hypothesis it consumes is the conclusion such an argument draws from
interchange, not interchange itself.

## The cut denotation: two modules invert it

The `⁺` and `⁻` suffixes read in three registers, and the registers cross
by design. `Framing.lagda.md:7-18` is the authority: the `⁺` hand is
built from the coterm-side coaction and cuts through `twist⁻`, the `⁻`
hand cuts through `twist⁺`, and "that crossing is what the framing is,
not an artefact of naming."

The crossing fixes one rule. The **positive** cut mediates with the
**negative** twist, and the negative cut mediates with the positive
twist. `Framing.lagda.md:77-78` and `:117-118` define `composite⁺` and
`composite⁻` accordingly.

The audit checked every declaration in the tree that names a cut. Twelve
modules follow the rule. Two invert it.

**`Groupoid/Path.lagda.md:106-110`**, in module `path`:

```
PG-composable⁻ : is-composable⁺
PG-composable⁺ : is-composable⁻
```

**`Group/Abelian.lagda.md:124-138`**, in module `framed`:

```
cut⁻ f k = f · (t⁻ · k)          -- mediates with t⁻, so this is the positive cut
cut⁺ f k = (f · t⁺) · k          -- mediates with t⁺, so this is the negative cut
composable⁻ : is-composable⁺
composable⁺ : is-composable⁻
```

Both compile, because both pass the inverted names into `tower` in the
positions the types demand (`Groupoid/Path.lagda.md:118`,
`Group/Abelian.lagda.md:188`). The checker is satisfied. A reader is not.

Each file then contradicts itself. `Groupoid/Path.lagda.md:260-263`
declares `C⁺ : is-composable⁺` and `C⁻ : is-composable⁻` in the
`one-twist` module, which is correct.
`Group/Abelian.lagda.md:412-417` declares
`cut⁺ : framing⁻.is-composable⁺ GM (λ _ → t⁻)` and
`cut⁻ : framing⁺.is-composable⁻ GM (λ _ → inv t⁻)`, also correct, and
stating the mediation rule on its face.

These are the two free-framing models, where `t⁻` and `t⁺` are arbitrary
and genuinely distinct. They are the modules where the rule carries the
most information, and the only two that drop it.

For contrast, so a reader does not chase it: `Engine.lagda.md:4-8` names
its hands for the slot each second factor enters, and says so in its
opening paragraph. Its carrier is the chosen-edge one, where `twist⁻` and
`twist⁺` are both `idn`, so no mediation distinction exists there to
invert. That is a declared register choice on a degenerate framing.

## MATCHES

Each entry names the condition the audit checked.

### `thunkable`, `linear`

**Checked at law level.** Munch-Maccagnoni's pre-duploid definitions,
read directly at
`resources/munch-maccagnoni-duploids/duploids.pdftext:180-263`. A
morphism `f` is linear when `f⊙(g⊙h) = (f⊙g)⊙h` for all `g`, `h`. It is
thunkable when `h⊙(g⊙f) = (h⊙g)⊙f` for all `g`, `h`. Against
`Tower.lagda.md:154-161`, where `thunkable f` quantifies
`associates f g h` over the two trailing factors and `linear h` over the
two leading ones. Reversing to applicative order (the repository's
duploid order convention) lines the two up term for term.

The paper proves at Proposition 6 that its thunkability agrees with
Führmann's thunk-force condition, so the Führmann lineage carries too.

One gap, not a naming problem. Neither `thunkable` nor `linear` carries a
citation at its definition site in this tree. `Polarity.lagda.md:1-8`
cites its source. `Tower.lagda.md:145-161` does not.

"Linear" collides three ways in the wider literature: linear algebra,
linear logic's multiplicatives, and linearly distributive categories.
kitcat inherits that collision from its source rather than creating it.

### `positive`, `negative`

**Checked at law level.** `Polarity.lagda.md:36-40` defines an object as
positive when every edge out of it is linear, negative when every edge
into it is thunkable. That is the derived form at
`resources/mmmm-classical-notions/article.tex:1694-1700`, which the
module cites at `:1-8`.

It is **not** the duploid paper's Definition 1, where polarity is a
primitive map `π : |D| → {+, ⊖}` (`duploids.pdftext:180-249`). The
difference is checkable inside this tree.
`Circle/Polarity.lagda.md:47-52` makes one object both positive and
negative, and `Word/Polarity.lagda.md:66-70` makes one object neither. A
total map into a two-element set can do neither.

### `Pentagon`

**Checked at law level.** `Pentagon.lagda.md:219-227` proves the
pentagonal diagram for `assoc⁺`, the associator of the positive
composition. That is the pentagon identity
(https://ncatlab.org/nlab/show/pentagon+identity) in its bicategorical
form, where the associator belongs to a composition rather than to a
tensor product.

**Face-value note.** The module covers `tower⁺` alone
(`Pentagon.lagda.md:30-36`). A reader must not assume coherence for the
`⁻` hand or for mixed words. The tree does not have it.

### `Bool.Heap`

**Checked at law level.** A heap is a set with a ternary operation
satisfying `t(b,b,c) = c = t(c,b,b)` and
`t(a,b,t(c,d,e)) = t(t(a,b,c),d,e)`, and any group gives one by
`t(a,b,c) = a·b⁻¹·c` (https://ncatlab.org/nlab/show/heap). Over the
two-element group `a·b⁻¹·c` reduces to `a ⊕ b ⊕ c`, which is the
reflection at `Bool/Heap.lagda.md:47-50`.

The module's point is the heap's defining feature. Choosing an element
turns a heap into a group, and `at false` and `at true`
(`Bool/Heap.lagda.md:144-155`) are the two groups the two choices yield.
`twist-moves-the-origin` (`:215-216`) carries one to the other. The best
name in the tree.

### `unital`, `is-unital`

**Checked at law level.** `Aligned.lagda.md:109-114` defines `unital e`
as neutral plus idempotent, and `Aligned.pinned` proves all four unit
laws from it (`unitl⁻` at `:148`, `unitr⁺` at `:178`, `unitl⁺` at `:215`,
`unitr⁻` at `:222`). So the edge is a genuine two-sided unit for both
hands at that layer.

**Face-value note.** In the general tree each hand has one unit law until
`Balanced` supplies the far one. `unital` is accurate where it is
declared, in `Aligned`, and does not describe the general carrier.

### `Bool.Klein`, `Word`, `magmoid`

**Checked.** `Bool/Klein.lagda.md:43-53` builds `Bool × Bool` under
componentwise xor, with the group laws proved at `:81-102`. That is the
Klein four-group.

`Word/Polarity.lagda.md:196-201` proves `gen-all`, that every canonical
descriptor is a cut word in the two twists. So the word model earns
"word" through a generation theorem rather than by assertion.

`magmoid`, used in prose, matches the nLab definition: a quiver with
composition, no associativity and no units
(https://ncatlab.org/nlab/show/magmoid).

### `cut⁺`, `cut⁻`, `is-composable⁺/⁻`

**Checked.** Cut as composition is the standard categorical reading of
Gentzen's rule (https://ncatlab.org/nlab/show/cut+rule), and each hand's
composition here is the representative of a cut judgment.

**Face-value note.** The tree has no sequent calculus and proves no
cut-elimination theorem. The name borrows the rule, not the Hauptsatz. No
source was found for `cut⁺` and `cut⁻` as an established pair, so the
superscripts are local notation under the tree's own register rule.

## EXTENDS

Each entry states what the audit checked and what it did not.

### `Framing`, `framing⁺`, `framing⁻`

A framed bicategory is a fibrant double category (Shulman, Theory and
Applications of Categories 20(18), 2008, and
https://ncatlab.org/nlab/show/framed+bicategory). A framing in topology
is a trivialization of the tangent bundle
(https://ncatlab.org/nlab/show/framed+manifold).

kitcat's framing is two families of endo-edges filling the two argument
slots (`Framing.lagda.md:1-6`). The audit checked whether any fibrational
or double-categorical content is present. None is. The relation to either
established sense is resemblance, and the corpus asserts nothing further.
The hazard stays low, because a reader must first believe a double
category exists before importing anything from one.

The adjectival forms carry more risk than the noun. `framed-interchange`
(`Interchange.lagda.md:54`) reads, out of context, as the interchange law
of a framed bicategory, and that phrase now touches two flagged names at
once.

### `readback`, `Readback`

Readback is standard normalization-by-evaluation vocabulary, synonymous
with reification and quotation, naming the map back from the semantic
domain to syntax
(https://en.wikipedia.org/wiki/Normalisation_by_evaluation).

`Framing.lagda.md:153-154` defines
`readback-of = ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f`. That is one
retraction equation, and the module states what it means at `:147-151`.

**Face-value note.** No normalization algorithm exists here, and no
normalization theorem. A reader must not assume termination, confluence,
or decidability of hom-equality from the name. Confidence on the
established sense: medium. The literature pass confirmed the word as an
attested synonym in secondary sources but did not open
Berger-Schwichtenberg or Danvy to check whether they use it.

### `Presentation`

**Downgraded from MATCHES.** A presentation of a category by generators
and relations is an isomorphism `C ≅ F(G)/R`, where `F(G)` is the free
category on a graph and `R` a set of relations
(https://ncatlab.org/nlab/show/presentation+of+a+category+by+generators+and+relations).

`Presentation.lagda.md:38-52` takes a wild category, one endo-operator
`cross`, one endo-edge family `pivot`, and three laws, and rebuilds the
carrier. The audit checked for the two components the concept needs.
Neither is present. There is no free construction on generators, and
there is no quotient by relations. What the module has is a pair of
translations with round trips, and the operator round trip is not on the
nose (`round-cross` at `:420-421` holds up to `unitr`).

So this is a presentation in the loose sense of "this data determines the
object and conversely", which is a real and proved result, and not the
generators-and-relations construction the phrase names.

### `judgment`

A judgment in the Martin-Löf sense is a meta-level knowledge claim
(https://ncatlab.org/nlab/show/judgment), not an element of a type.
`Type.lagda.md:38-39` makes `judgment x y` a function type.

The informal sequent-calculus reading (a judgment is a sequent) is close
enough that the prose at `Type.lagda.md:14-19` carries it. The more
accurate description sits in the sibling tree.
`src/Cat/Logic/Type.lagda.md:54-58` calls `reflect` a two-sided Yoneda
embedding, which is what a `judgment` is.

**Face-value note.** No proof-theoretic result is earned. No cut
elimination, no subject reduction, no derivability results.

### `is-neutral`

Two established senses. In normalization theory a neutral term is a
normal form with an eliminator applied to a variable, that is, a stuck
computation (arXiv:1304.0809). In the Capriotti and Kraus circle,
"neutral morphism" means equivalence
(`resources/kraus-infty-cwf/notes.tex:821`).

`Aligned.lagda.md:51-54` asks that both self-actions of an endomorphism
be equivalences. That resembles the Kraus sense without being it. The
Kraus condition is `iseqv(e)` on the morphism, and kitcat's is `is-equiv`
on two maps that `e` induces.

**Face-value hazard, local.** `Aligned.lagda.md` uses `readback` and
`is-neutral` in one file. `readback` invites the normalization reading,
under which `is-neutral` means stuck. One sentence citing
`resources/kraus-infty-cwf/notes.tex:821` would close it.

### `coterm`

In the λμμ̃-calculus and System L tradition after Curien and Herbelin,
syntax splits into terms, coterms (also stacks or continuations), and
commands. `Type.lagda.md:29-30` makes `coterm y` an edge out of `y`
paired with its far endpoint, which consumes where a term produces.

**Downgraded from MATCHES on evidence, not on content.** The literature
pass failed twice to extract text from Curien and Herbelin's paper and
relied on a secondary description. The audit therefore never compared
kitcat's definition against the source's own. The match is likely and
unverified.

### `Display`, `coslice`, `slice`

**Downgraded from MATCHES.** `Display.lagda.md:91-116` and
`Engine.lagda.md:332-370` build displayed structures, lenses, and
fibration conditions, and prove the fibration conditions rather than
assuming them. The coslice is the edges out of a fixed object, which is
the standard construction.

The base here is a reflexive graph, not a category (`Core.Rx`,
`reflexive-graphᴰ`). Displayed-category theory in the Ahrens-Lumsdaine
sense is displayed over a category. The idiom is used correctly over a
weaker base, and no displayed-category theorem follows from it.

### `Extraction`

Program extraction in a proof assistant obtains an executable program
from a proof term by erasing proof-irrelevant content.
`Extraction.lagda.md:1-7` projects a structure field out of a
contractible fiber, so one twist posits the other. The generic "project
out" sense is what the module uses. The collision stays inert, because
the tree has no code-extraction story. It would become live if one
arrives.

### `Torsor`

A G-torsor is an inhabited set with a free and transitive action, whose
shear map is an isomorphism (https://ncatlab.org/nlab/show/torsor).

`Circle/Torsor.lagda.md:59-67` proves that no family over the two
readback witnesses with points over both has a contractible total space.
The audit checked for a group action and a shear condition. Neither is
built. The module exhibits the symptom of torsorhood, namely witnesses
with no canonical basepoint, and the theorem named `torsor` is a
refutation, which reads oddly against the noun.

## SAFE

### `Aligned`

No established technical meaning. Two searches turned up no nLab page and
no categorical or type-theoretic definition. The only adjacent hit was a
paper-local "feature-aligned functor" in a machine-learning paper
(arXiv:2103.14770). So `Aligned` cannot conflict, and it carries no
face-value hazard.

`Aligned.lagda.md:1-11` builds the framed carrier at the diagonal framing
`twist⁻ = twist⁺ = rx`, and proves that interchange collapses the two
hands to one composition, so the graph carries an ordinary category.

**Weak.** The name comes from one hypothesis, that readback aligns the
reflection with the chosen edge. That hypothesis is shared with
`Bb.VgCategoryShape` and is not what distinguishes this module. What
distinguishes it is the diagonal framing and the collapse. This is also
the one place in the tree where the twist vocabulary would be accurate,
since it is exactly the degenerate case, and the name hides that.

**Alternatives.**

- `Diagonal`. The module's prose calls this "the diagonal framing"
  (`Aligned.lagda.md:5-6`). The condition is the image of the diagonal on
  twist families, so the standard sense of "diagonal" is the intended
  one.
- `Untwisted`. Names `θ² = id`, which
  `src/Bb/VgCategoryShape/README.md:126-132` already calls "the θ² = id
  fragment". It states which fragment this is, and makes plain that the
  general theory lives elsewhere.
- `Involutive`. The module family already speaks this way
  (`Interchange.lagda.md:118-123, 167-174`). One risk: the tree has an
  op-involution nearby (`Stability.lagda.md:104`).
- `Collapse`. Names the theorem. Rejected for internal reasons.
  `Balanced.lagda.md:145` has a `collapse` module, and
  `Tower.lagda.md:173-181` has `collapse⁺` and `collapse⁻`.

`Diagonal` and `Untwisted` are the two worth considering. `OneTwist` is
accurate but taken by `Bb.OneTwist`, where it means a different thing.

### `Engine`

No established meaning found. Two searches returned nothing
mathematical. `Engine.lagda.md:1-14` holds the chosen-edge carrier and
the fiber-contractibility derivation. The name carries no information and
no hazard. `ChosenEdge` appears in the module's own first line and would
say more. Observation, not a flag.

### `Tower`

Postnikov and Whitehead towers are inverse systems of spaces
(https://ncatlab.org/nlab/show/Whitehead+tower). `Tower.lagda.md:1-8`
stacks hypothesis groups. The echo is real in a homotopy-type-theory
library and weak in context. The module's subject is each hand's
composition and its associativity, so `Composition` or `Hands` would say
more.

### `UnitShape`, `shape`

Shape theory after Mardešić and Segal, and the shape modality of cohesive
homotopy type theory (https://ncatlab.org/nlab/show/shape+theory).
`UnitShape.lagda.md:1-14` computes the form of the unit-identification
datum. "Shape" is ordinary English inside a compound, and the `Unit`
prefix keeps the modality out of reach. A bare `Shape` module would be a
different matter.

### `argument`, `term`, `conclusion`

Generic proof-theoretic vocabulary. `argument x y = term x × coterm y`
(`Type.lagda.md:32-33`) pairs the two flanks around a hole. The closest
established name for a term paired against a coterm is the λμμ̃
*command*, but a command cuts them at the same type and kitcat's halves
sit at different objects. So `argument` is a reasonable choice, not a
missed one.

### `Type`, `Graph`, `Carrier`, `Model`, `Defect`, `Shift`, `Readers`, `Circle`, `Groupoid.Path`, `Group.Abelian`

Generic or plainly descriptive. `Readers` is apt: the edges of
`Bool/Readers.lagda.md:121-146` are readers of the argument. `Defect`
names a commutation defect and is used that way throughout
`Word/Defect.lagda.md`.

### `virtual-graph`

Exempt as a coinage, and worth a positive finding. In Cruttwell and
Shulman, *A unified framework for generalized multicategories* (Theory
and Applications of Categories 24(21), 2010), a virtual double category
has no required composites of loose morphisms. Multi-ary cells specify
what a composite would satisfy
(https://ncatlab.org/nlab/show/virtual+double+category).

`Type.lagda.md:21-43` is a graph whose composites are not given. They are
fibers of `reflect`, and their existence is a separate tier. The coinage
matches the prior connotation of "virtual" rather than fighting it.

## Cross-corpus consistency

The flagged names are not confined to `Bb.VirtualGraphs`. A rename here
would diverge from sibling usage. That cost is worth stating and does not
change any verdict.

**`Balanced`.** Live in `Cat.Logic` as `tower.balanced`
(`src/Cat/Logic/lemmata.md:113`, `:119-122`) and as three `Gist` module
names: `BalancedBase`, `BalancedProfile`, `BalancedWord`. Frozen in
`Bb.WeakDeductiveSystem` as `Gist.BalancedBase` and
`Gist.BalancedProfile`. Named in `docs/roadmap.md:29-30, 46-53, 61-67`,
`src/Bb/VgCategoryShape/README.md:86-99`, and
`src/Bb/OneTwist/README.md:66-69`. Roughly nine live `Test/` spikes use
it.

Two facts lower the cost. `src/Cat/Logic/Base.lagda.md:1-8` marks itself
retired as of 2026-08-03, and `Bb.WeakDeductiveSystem` is frozen. The
live surface that would diverge concentrates in `docs/roadmap.md` and the
`Test/` spikes.

The roadmap entries deserve their own note. `docs/roadmap.md:46-53` and
`:61-67` set "balanced duploid", "ribbon twist", and tortile structure as
targets. Those are goals, and the audit takes no position on them. The
finding is only that the current construction does not yet meet them, so
the target vocabulary should not name the modules that fall short of it.

**`is-stable`, `Stability`.** More entangled. `is-stable` appears in
`src/Cat/Logic/Base.lagda.md` (14 hits),
`src/Bb/WeakDeductiveSystem/Base.lagda.md` (18),
`src/Bb/VgCategoryShape/Type.lagda.md` (4), five `Bb.NaiveVirtualGraph`
`Gist` modules including `Gist.StableFiber` (23), and several live
`Test/` spikes. Each tree re-declares the predicate rather than importing
it, so the trees can carry different names without breaking. The cost is
that a reader learns two names for one predicate.

**`twist⁺`, `twist⁻`.** Structure fields in `Cat.Logic.Type`,
`Bb.WeakDeductiveSystem.Type`, and (one of them) `Bb.OneTwist`. No rename
is proposed, so no divergence arises.

**Outside this tree, noted only.** `hcategory`
(`src/Bb/VgCategoryShape/README.md:11-21`) sits on a term the literature
overloads at least three ways with no dominant sense.
`is-deductive-system` is a property of a carrier, while nLab's deductive
system is a collection of judgments and inference steps
(https://ncatlab.org/nlab/show/deductive+system), on a page that calls
its own terminology "not completely standard". The corpus already knows:
`src/Cat/Logic/Base.lagda.md:1-8` withdraws the human vouching for the
correspondence to "deductive system". Both are out of scope this round.

## Headline

Five names conflict, and they cluster. `Balanced`, `twist⁺`/`twist⁻`, and
`is-invertible⁺`/`is-invertible⁻` are one finding seen three times. The
tree borrows the vocabulary of balanced and tortile monoidal categories
for a structure with no tensor and no braiding, and its own proofs
(`pair⁺`, `pair⁻`, `inverse⁻-collapses`) show the twist laws hold only
where the two twists become one edge and the theory degenerates.
`is-stable` and `is-interchanging` are separate assumption-transfer
hazards on unrelated concepts.

One internal inconsistency is cheaper to fix. Two of the fourteen modules
that name a cut invert the tree's own denotation rule, and each of those
files uses the correct form elsewhere in itself.

The rest holds. Six names were confirmed by comparing the source's actual
condition against the actual Agda type: `thunkable`, `linear`,
`positive`/`negative`, `Pentagon`, `Bool.Heap`, and `unital`. Four more
were downgraded from MATCHES to EXTENDS once the stricter test was
applied: `Presentation`, `coterm`, and `Display` lost the verdict on
missing components or missing evidence. `Bool.Heap` and `virtual-graph`
are precise enough that a specialist would recognize the choice as
deliberate and correct.

## Sources

The full literature pass, with per-term confidence notes, sits at
`outputs/.notes/naming-audit-literature.md`. The anchors used here:

**nLab pages**

- balanced category. https://ncatlab.org/nlab/show/balanced+category
- balanced monoidal category. https://ncatlab.org/nlab/show/balanced+monoidal+category
- stable (infinity,1)-category. https://ncatlab.org/nlab/show/stable+(infinity,1)-category
- stability under pullback. https://ncatlab.org/nlab/show/stability+under+pullback
- framed bicategory, page titled "fibrant double category".
  https://ncatlab.org/nlab/show/framed+bicategory
- framed manifold. https://ncatlab.org/nlab/show/framed+manifold
- interchange law. https://ncatlab.org/nlab/show/interchange+law
- pentagon identity. https://ncatlab.org/nlab/show/pentagon+identity
- presentation of a category by generators and relations.
  https://ncatlab.org/nlab/show/presentation+of+a+category+by+generators+and+relations
- thunk-force category. https://ncatlab.org/nlab/show/thunk-force+category
- cut rule. https://ncatlab.org/nlab/show/cut+rule
- judgment. https://ncatlab.org/nlab/show/judgment
- heap. https://ncatlab.org/nlab/show/heap
- magmoid. https://ncatlab.org/nlab/show/magmoid
- torsor. https://ncatlab.org/nlab/show/torsor
- virtual double category. https://ncatlab.org/nlab/show/virtual+double+category
- Whitehead tower. https://ncatlab.org/nlab/show/Whitehead+tower
- deductive system. https://ncatlab.org/nlab/show/deductive+system

**Vendored resources, read directly**

- Selinger, *A survey of graphical languages for monoidal categories*.
  `resources/selinger-graphical-languages/graphical.tex:1074-1148` for
  balanced and twist, `:2047-2110` for tortile and ribbon.
- Munch-Maccagnoni, duploids paper.
  `resources/munch-maccagnoni-duploids/duploids.pdftext:180-263` for
  pre-duploid, linear, and thunkable, `:286-315` for the Führmann
  agreement.
- Mangel, Munch-Maccagnoni, and Melliès.
  `resources/mmmm-classical-notions/article.tex:1694-1700` for polarity.
- Capriotti and Kraus, semi-Segal types.
  `resources/capriotti-kraus-semi-segal/clean-arxiv.tex:554-562,
  1033-1038, 1591-1593` for wild category.
- Kraus, infty-cwf notes. `resources/kraus-infty-cwf/notes.tex:821` for
  neutral morphism.

**Papers located but not opened this session**

- Joyal and Street, *Braided tensor categories*, Advances in Mathematics
  102 (1993). Cited through Selinger.
- Shulman, *Framed bicategories and monoidal fibrations*, Theory and
  Applications of Categories 20(18), 2008.
  https://arxiv.org/abs/0706.1286
- Cruttwell and Shulman, *A unified framework for generalized
  multicategories*, Theory and Applications of Categories 24(21), 2010.
  https://arxiv.org/abs/0907.2460
- Lurie, *Higher Algebra*, Chapter 1.
- Curien and Herbelin, *The duality of computation*. Text extraction
  failed twice.
- Wikipedia, normalisation by evaluation.
  https://en.wikipedia.org/wiki/Normalisation_by_evaluation
