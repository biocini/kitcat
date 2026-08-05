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

Fifteen theory modules beside `Type`, in dependency order, then the
model modules.
`Embedding` holds representability, the embedding condition, and
the carrier opposite — nothing there reads a twist. `Framing` holds
the twist-parameterized vocabulary, split as `framing⁻`/`framing⁺`/
`framing` along which family each definition reads, with the duality
suite. `Tower` holds the two hands (`tower⁺` over `rx` plus the
embedding condition and the positive cut alone, `tower⁻` dually),
the reading of the opposite carrier's positive hand as this one's
negative hand, the mixed word, `associates` with its closures and
coherence square, the collapse laws, and the absorption route to
the near unit laws. `Pentagon` proves the pentagon for each hand,
the negative one through that reading.
`Polarity` holds the polarity definitions, generation, and the
unit-law converses. `Readback` holds what readback buys: the hands'
action identities and near unit laws, the residues, and the
embedding condition from the contractible negative cut.
`Cancellation` holds the D′ layer — centres, cancellations, far
unit laws, `at-strength`, the polarity collapse. `Interchange` holds
the framed-carrier theory over contractible cuts, the
hand-agreement results, and the tortile transcription. `Extraction`
holds the one-twist carrier where the negative tier's centre
defines the positive twist. `Diagonal` holds the diagonal chosen
edge — the h-category theory, with the two hands agreeing and the
embedding condition as theorems and the unit package contractible.
`Presentation` holds the operator presentation of a fully
cancelling carrier, both directions, with its residue and
dictionary. `Graph` and `Display` read the framing in
reflexive-graph language: fan calculus, lenses, and the cut as a
fibration. `Engine` holds the chosen-edge theory — the
fiber-contractibility engine over composability and unitality, and
the reflexive-graph dictionary where every answer is definitional.
`UnitShape` computes the shape of the chosen edge's
unit-identification datum: a path in a hom type, whose
propositionality is a truncation condition.

The models, each a plain carrier instance passing its twists,
readback, and tiers explicitly to the theory modules.
`Word.Carrier`/`Model`/`Defect`/`Polarity` hold the free point at
cancellation strength: canonical descriptors, the sandwich
reflection, the winding grade, the associativity-defect analysis,
and the empty polarities. `Circle.Model`/`Thunkable`/`Polarity`/
`Torsor`/`Shift` hold the circle model (`--cubical`, an import
island): a full system with wild homs where thunkability, polarity,
and readback each carry a one-winding freedom, and where retuning
the readback moves exactly two presentation laws. `Bool.Readers`
holds the projection, four-reader, three-point, and
reindexed-reader models bounding the associativity and cut
profiles. `Bool.Klein` refutes the extraction agreement;
`Bool.Heap` carries two diagonal structures on one reflection.
`Groupoid.Path` and `Group.Abelian` inhabit every telescope at
arbitrary framings, two-twist and one-twist.

## Provenance

`Type` arrived from `Test.NewDs.Carrier` on 2026-08-04, mathematical
content unchanged. The source module dates to 2026-08-03. It came
from a spike sequence that investigated recognition-based
alternatives to a carrier with primitive twist and readback fields.

The theorem and model modules arrived 2026-08-04, consolidated from
the committed archive per the plan at
`outputs/.plans/virtual-graphs-vendor.md`: `Cat.Logic` entire
(`Type`, `Base`, `Graph`, `Display`, and all fourteen `Gist`
modules), the `Bb.WeakDeductiveSystem` core and its free-framing
spikes, `Bb.OneTwist` entire, `Bb.VgCategoryShape` entire, and the
`Bb.NaiveVirtualGraph` unit-shape analysis. The per-module source
mapping is in this tree's `CHANGELOG.md`. The `Test.*`-sourced
material (the 2026-08-02/03 spike results, hypothesis groups E and
F, and their models) waits for a later pass; the plan's catalog
marks which is which, and also lists the `Bb.NaiveVirtualGraph`
rows still unvendored beyond `UnitShape`.

## Relationships

This is the common minimal carrier underlying every
virtual-graph-shaped construction in the library. `Cat.Logic` and
`Bb.WeakDeductiveSystem` add a `twist⁺`/`twist⁻` framing as record
fields, and `Cat.Logic` adds `readback`. `Bb.OneTwist` carries
`twist⁻` alone. `Bb.NaiveVirtualGraph` carries one chosen edge `idn`
in place of a framing. `Bb.VgCategoryShape` carries one chosen edge
together with readback.

Each of those records extends this one with more fields. Here the
extra data enters as explicit module parameters instead, so one
statement covers every stratum that can supply the parameters.

Four modules import the live `Core.Rx.*`: `Graph`, `Display`,
`Engine`, and `Group.Abelian` (the same accepted dependency
`Bb.WeakDeductiveSystem.Graph` and `.Display` carry). The five
`Circle.*` modules import the live `HData.Circle` and are the
tree's `--cubical` island; no `--erased-cubical` module imports
them. A change to either can break this tree. Everything else
imports `Core.*` basics only.
