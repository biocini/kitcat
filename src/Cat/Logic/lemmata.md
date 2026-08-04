# Cat.Logic: lemmata

The theorem ledger for `Cat.Logic`: statement, citation, status,
date. Numbering continues `docs/gloss.md`, whose entries these
replace. Extended commentary on these results is in
[gloss.md](gloss.md), under the same number.

Statuses:

- ✅ machine-checked, committed (module cited)
- 🧪 machine-checked evidence module in `Gist/` (self-contained
  modulo Core, `Cat.*` definitions frozen at the cited commit)
- 📐 established by rigorous argument (countermodel or hand-checked
  path algebra), not mechanized
- ⚠️ partially conjectured, with the honest boundary stated

## The framed deductive-system theory

**Retired, 2026-08-03.** `virtual-graph`/`is-deductive-system`
(`Cat.Logic.Type`, `Cat.Logic.Base`) cannot express duploidal
structure: balanced strength collapses polarity, so no carrier has
P and N genuinely distinct, and a duploid needs exactly that
(`src/Cat/Logic/TODO.md`, item 7, the reflection theorem). The
entries below remain machine-checked facts about that construction.
The human vouching for its correspondence to *deductive system*
(`docs/provenance.md`, practice 3) is withdrawn: read this section as
a frozen record, not a foundation to build on.

**T25: Propositionality of every tier and of the package.** Each
of `is-stable`, `is-invertible⁻`/`is-invertible⁺`/`is-invertible`
is a proposition outright. `is-composable` is one over the
stability that indexes it. `is-deductive-system` is a proposition,
its composability component filled by a path over the moving
stability.

✅ `Cat.Logic.Base` (2026-07-25).

**T26: The framing is two reflexive graphs.** A twist is a
reflexivity datum, so a virtual graph carries two reflexive-graph
structures on one underlying graph. Fans and cofans name no
reflexivity, so the term and coterm families come from either
graph. The *centers* split: `var` is the cofan center of the
negative graph and `covar` the fan center of the positive one, so
the axiom pairs one from each.

✅ `Cat.Logic.Graph` (2026-07-25), every claim `refl`.

**T27: Each family is a lens over the graph of the twist it does
not hold, and each cut is a fibration.** A lens states its unitor
at its base's reflexive edge, and each action sits at the twist
its own axiom half does not carry: `term-lens` is oplax covariant
over `graph⁻`, `coterm-lens` lax contravariant over `graph⁺`, each
unitor that side's cancellation. Both displays are univalent with
no condition on the base, the families being discrete.

✅ `Cat.Logic.Display`, `Cat.Logic.Base` (`absorption`)
(2026-07-25).

**T28: Stability is an embedding condition.** `is-stable` is
`reflect` having propositional fibers at every pair of objects
(`stable-is-embedding` is `refl`). Over hom-sets the judgments
form sets, so the tier reduces to injectivity of transmission, the
edge surrounded by one twist of each sign (`stable-from-hom-sets`).

✅ `Cat.Logic.Base` (2026-07-25). Discharges the shape of the
truncated-regime obligation in
`notes/2026-07-22-deductive-system-design.md` (O4).

**T29: Interchange is a cospan coherence.** Over the two-sided
base each composite judgment is the transport with one leg held at
its twist, applied to one factor's reflection. The two land in the
fiber at the outer pair from distinct vertices with legs pointing
the same way. Agreement of the two cuts is agreement of that
cospan's two pushforwards, both directions.

✅ `Cat.Logic.Display` (`push-is-composite⁻`/`⁺`,
`cospan-from-cuts`, `cuts-from-cospan`, `bipush-comp`)
(2026-07-25).

📐 No display of `judgment` can carry the agreement as an edge.

**T30: Framing collapse is weaker than mediation.** The derivation
of `twists-agree` uses a left and a right unit for *one*
composition, so it goes through on either missing unit law alone,
with no interchange: `collapse⁺`, `collapse⁻`. Since a mediation
supplies those laws, each hypothesis is weaker as a statement than
interchange. Two collapses separate: the twists becoming one edge,
and the compositions becoming one operation. Interchange gives
both. A missing unit law gives only the first.

✅ `Cat.Logic.Base` (2026-07-25). Corrects the "nothing between"
reading in `docs/deductive-systems/mediation.md`.

⚠️ Whether the two collapses are separable is OPEN.

**T32: Stability is a theorem of the contractible negative cut.**
`axioms→stable : is-deductive-system → is-stable`. The negative
composite at the twist is a reflection (`composite⁻-twist`), so the
cut's contractible fiber transports to every image fiber of
`reflect`. `image-fibers-contr→is-embedding`
(`Core.Function.Embedding`) then closes the embedding. Stability is
not a field of the package.

✅ `Cat.Logic.Base` (`axioms→stable`,
`contr-cut⁻.stable-from-contr-cut⁻`) (2026-07-28).

**T33: The cancellations are theorems of the tiers.** Each tier's
centre reads back as the other twist: `centre⁻-twist⁺` and
`centre⁺-twist⁻`. Both cancellations (`cancel⁻`, `cancel⁺`) and
both twist absorptions (`absorb⁻`, `absorb⁺`) follow from the two
invertibility tiers alone.

✅ `Cat.Logic.Base` (`tower.balanced`) (2026-07-28). The certified
spike is `Cat.Logic.Gist.BalancedProfile`.

**T34: The four unit laws.** Each hand is two-sided unital with its
own twist as unit. `unitr⁺` and `unitl⁻` hold in `tower` with no
tier, from readback and each hand's cut. Under the two invertibility
tiers, `tower.balanced` adds `unitl⁺` and `unitr⁻`. Two unital
magmoids on one graph, offset by the double twist.

✅ `Cat.Logic.Base` (`tower`, `tower.balanced`) (2026-07-28).

**T35: The associativity profile is the pre-duploid triple.** The
deductive-system axioms (`is-deductive-system`) prove exactly
`assoc⁺`, `assoc⁻`, and `mixed-assoc`, and no more: the generic
`associates` property (associativity of a length-3 path regardless
of the middle edge's polarity) is independent, refuted by two finite
countermodels.

✅ `Bb.WeakDeductiveSystem.Gist.AssociatesCountermodel` (2026-07-27,
`just check` re-run clean 2026-07-28).

**T36: The associates defect is a determinate twist word, one per
flanking edge.** Each bracketing of `associates f g h` determines
the other up to a correction: `defect⁺ : f ⨾⁺ (g ⨾⁻ h) ≡ w⁺ (rise f)
⨾⁺ ((f ⨾⁺ g) ⨾⁻ h)` and `defect⁻ : (f ⨾⁺ g) ⨾⁻ h ≡
(f ⨾⁺ (g ⨾⁻ h)) ⨾⁻ w⁻ (zrunW h)`, both for every triple. No single
word works uniformly (`no-uniform⁺`, `no-uniform⁻`), and of sixteen
candidate placements only these two survive. Both corrections are
units exactly at the matching closure, thunkable for `w⁺` and
linear for `w⁻` (`thunkable→rise`/`rise→thunkable`,
`run→linear`/`linear→run`), and the winding grade forgets both
(`shift-associates`), so balance kills the measured defect.

✅ `Cat.Logic.Gist.AssociatesDefect` (2026-07-29), over the free
balanced word model `Cat.Logic.Gist.BalancedWord`.
