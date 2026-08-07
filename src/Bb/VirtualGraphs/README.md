# Bb.VirtualGraphs

## The construction

A virtual graph is a graph and one axiom. The graph is `ob` and
`hom`. The axiom is `reflect`, the representability condition: every
edge names a judgment over its own endpoints. A judgment takes a term
and a coterm and returns an edge between their far ends. Terms,
coterms, arguments, conclusions, and judgments all derive from the
two graph fields alone.

The tree collects the theorems the archive proves about
virtual-graph-shaped carriers, restated over this one carrier. Each
lemma module takes the carrier and a flat telescope of explicit
hypotheses; `virtual-graph` is the only record in the tree. The
hypothesis groups and the catalog behind the layout live in
`outputs/.plans/virtual-graphs-vendor.md`.

Twenty-six theory modules beside `Type`, in dependency order, then
the model modules.
`Embedding` holds representability, the embedding condition, the
carrier opposite, and the centred pair (a representability witness
split as a fiber times a path space). Nothing there reads a half-twist.
`Framing` holds the half-twist-parameterized vocabulary, split as
`framing⁻`/`framing⁺`/`framing` along which family each definition
reads, with the duality suite and the six pairings of a hand's two
judgments against each half-twist (`own`/`alt`/`mixed`, `is-natural±`).
`Tower` holds the two hands (`tower⁺` over `rx` plus the embedding
condition and the positive cut alone, `tower⁻` dually), the reading
of the opposite carrier's positive hand as this one's negative hand,
the mixed word, `associates` with its closures and coherence square,
the collapse laws, the absorption route to the near unit laws, the
four flanking operations with their law types, and the
tier-as-equation-plus-loop-space decomposition. `Pentagon` proves
the pentagon for each hand, the negative one through that reading.
`Polarity` holds the polarity definitions, generation, and the
unit-law converses. `Readback` holds what readback buys: the hands'
action identities and near unit laws, the residues, the embedding
condition from the contractible negative cut, and the
naturality-in-a-hand ⇄ far-unit-law equivalence.
`Cancellation` holds the D′ layer: centres, cancellations, far
unit laws, `at-strength`, the polarity collapse. `Neutral` holds the
other route to the same collapse, from two idempotent-flank
hypotheses instead of the two absorption tiers. `Interchange` holds
the framed-carrier theory over contractible cuts, the
hand-agreement results, and the tortile transcription. `Extraction`
holds the one-half-twist carrier where the negative tier's centre
defines the positive half-twist. `Diagonal` holds the diagonal chosen
edge, the h-category theory, with the two hands agreeing and the
embedding condition as theorems and the unit package contractible.
`Recognition`, `Shape`, and `Gluing` hold the candidate-relative
theory. Every half-twist-shaped datum there is bound by a quantifier,
instead of read from the carrier. `Recognition` holds the shared
candidate kit and judgment-level clauses. `Shape` holds the
per-object recognition shape. `Gluing` holds the cross-pair grammar
and the edge-indexed coherence conjunct. `Mediation` holds the mediation
clauses over a candidate pair, the self-referential form that names
no half-twist directly, and Kraus canonicalization ported to one hand.
`Presentation` holds the operator presentation of a fully
cancelling carrier, both directions, with its residue and
dictionary. `Graph` and `Display` read the framing in
reflexive-graph language: fan calculus, lenses, and the cut as a
fibration. `Engine` holds the chosen-edge theory: the
fiber-contractibility engine over composability and unitality, and
the reflexive-graph dictionary where every answer is definitional.
`UnitShape` computes the shape of the chosen edge's
unit-identification datum: a path in a hom type, whose
propositionality is a truncation condition. Its `obstruction` module
holds a second negative result: a propositional predicate that
delivers absorption forces every self-path of the chosen family to
die under `ap held`, unconditionally.
`CrossedUnit` holds the crossed pairing: the coterm hand's derived
filler feeds the term hand's tier one field early, so an exchange
hypothesis alone pins the chosen family as that tier's unique
inhabitant. `Reflexive` holds the carrier where the chosen edge
carries its own two absorptions as hypotheses rather than derived
facts. Its `redundancy` module drops the unit tier entirely once
stability is stated as an equivalence. `Stable` holds a second unit
tier, the equivalence-plus-idempotence form, three stability
formulations side by side, and the theorem that composability,
unitality, and stability all transport across the opposite carrier.
`Curried` restates the chosen-edge theory over a ternary `emb`
operator and two compositions as fibers over strings, where readback
is one statement rather than two. `Lens` packages the chosen edge's
judgment and hom families as lenses rather than fibrations: an
unbiased lens over the base graph for each family, and — over the
graph paired with its own opposite — a covariant lens where
interchange is exactly the missing functoriality, delivered once
`composites-agree`. `Displaced` holds the displayed carrier
`virtual-graphᴰ`, replaying the sequent vocabulary with every type
displaced over a chosen basepoint in each fiber, `reflect[_]` its
only field beyond the structural three.

The models, each a plain carrier instance passing its half-twists,
readback, and tiers explicitly to the theory modules.
`Word.Carrier`/`Model`/`Defect`/`Polarity` hold the free point at
cancellation strength: canonical descriptors, the sandwich
reflection, the winding grade, the associativity-defect analysis,
and the empty polarities. `Word.Mediation`/`Census`/`Recognition`
read the same free point against `Mediation`, `Recognition`,
`Shape`, and `Gluing`: the two-triple pinning of the half-twist pair, the
self-referential census of nearby candidates, and the per-object and
cross-pair recognition. Each either contracts at this carrier or
fails there. `Circle.Model`/`Thunkable`/`Polarity`/`Torsor`/`Shift` hold
the circle model (`--cubical`, an import island). It is a full
system with wild homs, where thunkability, polarity, and readback
each carry a one-winding freedom, and where retuning the readback
moves exactly two presentation laws. `Circle.Natural`/`Mediation`/
`Recognition` read the same model against the naturality, mediation,
and recognition theory. It carries a torsor structure on each of
three moduli (readback and the two naturality equations), a rotation
family where every triple associates while all four unit laws fail,
and recognition and gluing types that either retract onto the circle
of cancelling pairs or fail outright. `Bool.Readers` holds the
projection, four-reader, three-point, and reindexed-reader models
bounding the associativity and cut profiles, and the four-reader
model's failing negative naturality square. `Bool.Endo` holds the
commuting-involution models on `Bool`: full tiers and both
neutrality tiers throughout, one instance also satisfying every
unit law, another satisfying neither. `Bool.Klein` refutes the
extraction agreement. `Bool.Heap` carries two diagonal structures on
one reflection. `Bool.Sleeve` carries two word-model objects joined
by a one-directional sleeve, bounding what the cross-pair grammar
can recognize across a non-symmetric carrier.
`Groupoid.Path` and `Group.Abelian` inhabit every telescope at
arbitrary framings, two-half-twist and one-half-twist. `Groupoid.Path` also
carries both naturality tiers at any self-path family.
`Groupoid.Engine` is the discrete path groupoid read against the
five chosen-edge theory modules above: every hypothesis telescope
holds untruncated, with no h-level condition on the carrier.

## Provenance

`Type` arrived from `Test.NewDs.Carrier` on 2026-08-04, mathematical
content unchanged. The source module dates to 2026-08-03. It came
from a spike sequence that investigated recognition-based
alternatives to a carrier with primitive half-twist and readback fields.

The theorem and model modules arrived 2026-08-04, consolidated from
the committed archive per the plan at
`outputs/.plans/virtual-graphs-vendor.md`: `Cat.Logic` entire
(`Type`, `Base`, `Graph`, `Display`, and all fourteen `Gist`
modules), the `Bb.WeakDeductiveSystem` core and its free-framing
spikes, `Bb.OneTwist` entire, `Bb.VgCategoryShape` entire, and the
`Bb.NaiveVirtualGraph` unit-shape analysis. The per-module source
mapping is in this tree's `CHANGELOG.md`.

`Neutral`, `Recognition`, `Shape`, `Gluing`, `Mediation`,
`Bool.Endo`, `Bool.Sleeve`, `Word.Mediation`, `Word.Census`,
`Word.Recognition`, `Circle.Natural`, `Circle.Mediation`, and
`Circle.Recognition` arrived 2026-08-05, from the thirteen
2026-08-02/03 `Test.Spike*` files (hypothesis groups E and F) per
`outputs/.plans/virtual-graphs-vendor-phase2.md`. Each restates the
source file's checker-verified lemmas only. No spike's own reading
of what a result meant for the recognition line crossed over.

`CrossedUnit`, `Reflexive`, `Stable`, `Curried`, `Groupoid.Engine`,
and extensions to `Engine` and `UnitShape` arrived 2026-08-06, from
the seven `Bb.NaiveVirtualGraph` rows the phase-1 plan named as
deferred beyond `UnitShape`, per
`outputs/.plans/virtual-graphs-vendor-phase3.md`. `Lens` and
`Displaced` arrived the same day, from the remaining two rows —
a displayed carrier is now a second record in its own module, per
`outputs/.plans/virtual-graphs-vendor-phase4.md`. The
`Bb.NaiveVirtualGraph.Gist.PathGroupoid` model is the one row left
unvendored.

## Relationships

This is the common minimal carrier underlying every
virtual-graph-shaped construction in the library. `Cat.Logic` and
`Bb.WeakDeductiveSystem` add a `half-twist⁺`/`half-twist⁻` framing as record
fields, and `Cat.Logic` adds `readback`. `Bb.OneTwist` carries
`half-twist⁻` alone. `Bb.NaiveVirtualGraph` carries one chosen edge `idn`
in place of a framing. `Bb.VgCategoryShape` carries one chosen edge
together with readback.

Each of those records extends this one with more fields. Here the
extra data enters as explicit module parameters instead, so one
statement covers every stratum that can supply the parameters.

Four modules import the live `Core.Rx.*`: `Graph`, `Display`,
`Engine`, and `Group.Abelian` (the same accepted dependency
`Bb.WeakDeductiveSystem.Graph` and `.Display` carry). The eight
`Circle.*` modules import the live `HData.Circle` and are the
tree's `--cubical` island; no `--erased-cubical` module imports
them. A change to either can break this tree. Everything else
imports `Core.*` basics only.

Five carrier-free lemmas found while vendoring the recognition-line
spikes moved to `Core.*`/`HData.*` on 2026-08-06, per
`outputs/virtual-graphs-core-proposals.md`: `snd-contr` (with a new
companion `fst-contr`) to `Core.Transport.Properties`, the
`diagonal` module and `loops→is-set` to `Core.HLevel.Base`,
`equiv-cancel-l`/`equiv-cancel-r` to `Core.Equiv.Properties` as
`equiv-lc`/`equiv-rc`, `wind` and the renamed `cancell`/`cancelr` to
`Core.Kan`'s `module Path` (reached as `Path.wind`/`Path.lc`/
`Path.rc`), and `mult-r-equiv` to `HData.Circle.Mult`. Two more,
`ap-mult-base` and `slide-rot`, moved to `HData.Circle.Properties`
alongside a private copy already there. `Circle.Recognition` no
longer imports `Circle.Mediation`; that was the only reason it did.
