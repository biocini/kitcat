# Inquiry — 2026-07-21 — interchange as structure: the choice-free core

The resumption brief for the next session, which IS this
investigation: a meta-level design session, carrying enough spike
work to determine the plan. **Its contract (Lane, 2026-07-21): the
session's output is a decisively formalized plan and an exact
roadmap, such that every session after it proceeds mechanically.**
Nothing else builds until that ruling lands — the parity
remainder in `2026-07-21-legacy-parity.md` is gated on it.

## The central question (Lane, confirmed at this abstraction level)

Should interchange be extracted from the axioms entirely,
everywhere: a **choice-free core** — embedding, interchange-free
pull fiber, unit — with resolutions as structure *over* it. Then
"monoidal category," the current two-field form, and the base
category record are all the same core with different resolution
data, and the count of resolutions (one at the base, two at the
refounded monoidal level) is a *choice*, never part of a
definition. This reformulates the monoidal axioms suite along
with `Cat.Type`/`Cat.Base` — which is why no further work builds
on either form before the ruling.

## The motivation (Lane's terms)

We have been circling the right way to formulate interchange and
the records based on it. Interchange is the **only unfree piece
of the development** — the one place that is genuine data rather
than property. Ideally the axioms record should be *property*,
not structure, and interchange always made that problematic.
Concretely: the contractibility fields are propositions; the
interchange field is a path between composite operators with
genuinely distinct inhabitants (CircleTensor's two routes,
machine-checked) — so no record containing it can be property.
The resolution reification made this visible: once every derived
cell classifies as interchange-free, generic over a choice, or
provably insensitive to it, the interchange fields read as data
mislocated inside a would-be-property record.

Flagged sub-question: `unit : ev (emb f) ≡ f` is also path-data
in the wild setting — whether the core is property up to unit, or
unit anchors through representability differently, is part of the
property audit (S2).

## The two formulating lenses

1. **Duploids / polarization** (ruled interesting, kept). `▿`/`▵`
   are the two sequencing protocols of composition — right factor
   evaluated at the identity context and fed left, versus its
   mirror. Pinning interchange identifies the protocols once and
   for all; duploid/polarized composition (LB program Phase 4,
   Hasegawa–Thielecke) is sensitive to exactly that
   identification. Hypothesis to examine: the thunkable/linear
   boundary as the vanishing locus of the composition-level ω —
   the flank boundary one level down.
2. **Chiralities (Lane, new this session).** Formulate the
   question at the foundations level through Melliès' dialogue
   categories and chiralities, using **the biequivalence of Chir
   with the 2-category Cat**: the two-handed composite calculus
   (over/under slots, the ▿/▵ pair) is a chirality-shaped
   decomposition of a category into its left and right hands,
   with interchange as the mediating datum between the hands. The
   biequivalence licenses posing "where does interchange live"
   invariantly — which side of the biequivalence the library's
   records present, and what the interchange datum is on the
   chirality side. Shelf: `resources/mellies-dialogue-chiralities`
   (with `resources/mellies-braided-dialogue` beside it); the
   attic's chirality design (`.attic/handoff.md` — op as Melliès'
   dagger, the representable dialogue distributor) re-derives on
   the new spine in this frame; the roadmap's Chir re-gating
   (project 1, phase 3) intersects here.

## Spike agenda (enough to determine the plan)

- **S1 — core-record prototype.** Mint the candidate
  `category`-core (graph, `emb`, primitive interchange-free
  pull fiber, unit) with resolution structure over it; re-derive
  the base spine over an arbitrary resolution (the `spine-tail`
  transposition — the monoidal playbook one level down); sort the
  `Cat.Base` derived theory into core-only vs
  resolution-consuming.
- **S2 — property audit.** Which axioms are propositions over
  (graph, emb) in the wild setting; unit's exact status; whether
  "is a category" can be property of the presentation with data
  residing exactly and only in the resolutions.
- **S3 — chirality formulation.** State the two-hand
  decomposition against the definitions in
  `mellies-dialogue-chiralities`; identify what interchange is
  under the biequivalence; test whether core + resolutions IS the
  chirality presentation of a category.
- **S4 — detection at the base level.** `∞-groupoid Circle` with
  a second, rot-deformed composition resolution; winding
  detection — establishing concretely that composition-level
  resolution choices are genuine data.
- **S5 — conservativity.** Sketch the comparisons: current
  `category-axioms` ≃ core + one resolution;
  current `monoidal-axioms₀` ≃ core + two resolutions (the
  `axioms₀-compare` shape) — the migration guarantee that the
  certified tower and the landed parity ports transcribe rather
  than perish.

## Ruling targets — what the session's plan must fix

1. The core record's exact field list and the resolution records'
   final form, at both levels, count-free.
2. GO/NO-GO on the reformulation: GO yields the exact migration
   roadmap ordering every module; NO-GO resumes the parity
   remainder (steps 0–6) unchanged.
3. The scope of the chirality connection — whether the
   dialogue/chirality layer enters the record design now or
   remains the formulating lens.
4. The updated mechanical roadmap for every following session.

## Standing state

The parity memo's mechanical remainder is gated on ruling 2 —
its steps stay valid transcription targets either way (unchanged
on NO-GO; re-packaged on GO, the ported material being
generic-over-choice throughout). Landed this session and standing
regardless: `Cat.Monoidal.Bifunctor`, `.Coherence` (interchange
block + pentagon), `.Indiscrete` (monoidal builder), `.Iso`
(monoidal half), the Properties closures, and
`Test/CircleUnitorTwist` (the unitor discrepancy winds −1). The
rack stays behind the braided theory. Nothing is committed.
