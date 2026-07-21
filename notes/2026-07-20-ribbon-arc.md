# Plan — 2026-07-20 — the ribbon-dialogue arc

Ruled (Lane, 2026-07-20): the arc toward modeling Melliès'
ribbon tensorial logic is bumped up the roadmap — it is one of
the central motivations of the construction, and the braided
layer that landed this week is its foundation. This note maps
the arc; the staging below is proposed, the open rulings are
flagged at the end.

## The target

Ribbon tensorial logic is the internal logic of **balanced
dialogue categories** (`resources/mellies-braided-dialogue`,
Definition 12, `l.3366`): a dialogue category — monoidal with a
tensorial pole `⊥` exponentiating every object into left and
right negations, double negation *not* required involutive —
equipped with a braiding and a twist forming a balanced category
(Definition 9, `l.3066`). The published coherence companion is
Melliès, *Ribbon Tensorial Logic*, LICS 2018 (DOI
10.1145/3209108.3209129): proofs are ribbon tangles.

Two facts shape the arc:

- **Duals are not on the critical path.** The balanced dialogue
  category does ribbon phenomenology without dualizable objects
  (the manuscript's headline `Mod(H)` instance is modules of
  arbitrary dimension, Proposition 23, `l.4568`); classical
  ribbon categories are recovered on subcategories afterwards
  (Proposition 24). The target record is `balanced-dialogue`,
  not ribbon-with-duals.
- **Braided-not-symmetric is the point.** The record tower's
  deliberate independence of the two hexagons, with the
  symmetric identification exiled to a future layer, is exactly
  the regime ribbon logic lives in. The wild-homs commitment
  keeps the ladder from collapsing.

## Where the tree stands

Landed and load-bearing: the braided layer on the new spine
(`Braid`, `Hexagon`, `Indiscrete`, `Iso`, the swap-half
comparison in `Properties`), and the path groupoid as a category
instance (`Cat.Groupoid.∞-groupoid`, interchange from `pcom`).
Not yet existing: any balanced/twist record (the module *named*
`Twist` is the interchange-perturbation countermodel, not a
balancing), any dialogue/negation layer, any monoidal structure
on a path groupoid. The old chirality/dialogue design (op as
Melliès' dagger, "the dialogue distributor is literally
representable") survives only in `.attic/handoff.md` — the
`project_chirality_record.md` memory it points to was pruned in
the workflow port and must be re-derived on the new spine.

## The stages

**A — the balanced layer** (unblocked now). `balanced (B :
braided M)`: the twist as a loop family at both grades, ♭ form
at witness arguments per the field-shape genus, with the
balancing field `θ (U ●₀ V) ≡ ⊗₀-braid♭ U V ∙ ⊗₀-braid♭ V U ∙
(θ U ⊗ θ V)`-shaped and its grade-1 displacement; naturality of
the hom-grade twist free by its type, as with the braid.
Presentation comparisons (twist-on-pairings vs twist-on-normal-
forms) are `Cat.Monoidal.Properties` material by the standing
discipline.

**C1 — the loop-space instances** (unblocked now; runs *with* A
so the instance proves the field shape). The monoidal instance
on `∞-groupoid (Ω Y)`: `⊗₀-emb p = (l , r) ↦ l ∙ p ∙ r` — the
`pcom`/yon-unbiased pattern one level down, unit `refl`,
interchange by the `lsplit`/`rsplit` reassociations, spine by
`spine-tail` over the interchange line (the Groupoid/Twist
re-assembly pattern). The braided instance at `Ω² Y`: the flank
swap is the Eckmann–Hilton move — literally "the block moves
only along interchange lines", in the conjugated instance form
of the braided-layer note — and the hexagons are the EH
coherences, the first instances whose fields carry homotopical
content rather than contractibility. The candidate twist is the
self-braiding `c(p, p)` — the framed-E₂ balancing — which is
what stage A's field shape should be minted against.

**B — the dialogue layer** (needs its own design session before
code). The tensorial pole and negations in the house genus:
`hom (x ⊗ y) ⊥ ≃ hom x (¬ y)` wants to be *representability of
a refutation composite* — a second embedding with a contractible
spine, mirroring how the tensor itself is presented — rather
than a hom-equivalence field. This is the arc's genuinely new
design surface; the attic's representable-distributor hypothesis
is the starting conjecture, to be spiked on the new spine. Both
negations (left/right) enter since nothing is symmetric. The
helical/cyclic refinements (§3 of the manuscript) are optional
side rooms, not gates.

**D — balanced dialogue** (A + B). The `balanced-dialogue`
record (Definition 12), and the first genuine theorem of the
layer: the dialogical twist — the unique `twist : ⊥ → ⊥` of
Proposition 5 (`l.2188`) — agrees with the ribbon twist
(Proposition 14, `l.3490`). That agreement is
presentation-comparison shaped and should land in a Properties
module by the standing discipline.

**E — evidence tier** (parallel, not gating). The nontriviality
facts on the S² carriers, currently 📐 in the ledger from the
old-formulation era: the braiding on `Ω² S²` braided-not-
symmetric (π₃(S²) ≅ ℤ, the Hopf map), the T5/T11 loop families.
Mechanizing π₂-winding is feasible; π₃ machinery is a major
undertaking and stays argued-not-mechanized unless ruled
otherwise. The free-model/coherence theorem (ribbon tangles,
LICS 2018) is far-future.

## Open rulings

1. **Twist primitive.** Object-loop family `θ x : x ≡ x` with
   the ♭/witness form, or a composite-level loop? Is `θ I ≡
   refl` a field or a theorem? (Mint against `c(p, p)` at the
   Ω²-instance.)
2. **The `Twist` name.** The countermodel module holds the word
   the balanced layer wants. Rename the countermodel (e.g.
   `Cat.Monoidal.Shear` or `.Perturb`) and free `Twist`/
   `Balance` for the ribbon-side layer — or pick a different
   name for the balancing. Lane's call before stage A mints
   records.
3. **Negation genus** (stage B's session): representable
   refutation-composite embedding vs hom-equivalence field;
   one record or graded like the tensor; where the pole lives.
4. **Instance packaging**: module home and carrier form for the
   loop-space instances (pointed types, `Ω²` as the braided
   carrier); whether stage C1's monoidal-on-`Ω` lands before or
   with the braided-on-`Ω²`.
5. **Evidence tier**: how much of E to mechanize vs ledger.
6. **Sequencing vs the standing queue**: this arc vs the
   Properties backlog items 3–4 and the roadmap's earlier
   numbered projects.

## Absorbed into the LB certification program (2026-07-20)

This arc's stages are Phases 2–5 of
`notes/2026-07-20-lb-certification-program.md`, each with its
∂LB consumer named there. Two stage additions ruled in with the
program: the **centrality/transparency layer** (Müger centre,
silent-exchange soundness) runs ahead of stage A as the
program's Phase 1, and stage B gains the **`∗`-autonomous
specialization** (the pole dualizing — LB's involutive
boundary). The six open rulings above stand unchanged.
