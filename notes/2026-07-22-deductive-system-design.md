# Design — 2026-07-22 — the deductive-system foundation

The ruling contracted by `2026-07-21-interchange-inquiry.md`. The
central question — whether interchange should be extracted from the
axioms everywhere, with a choice-free core and resolutions as
structure over it — is answered GO, and the ruling goes further than
the inquiry posed it: not only interchange but every structural
field is now either certified irreducible or extracted into a
propositional package, and the base record that results is the
foundation for everything that follows. Every claim below is
machine-checked, priced, or listed as a named obligation.

## The stratification, with certificates

| layer | fields | status | certificate |
| --- | --- | --- | --- |
| `virtual-graph` | reflexive-graph + `emb` | structure — the carrier and the model | `Test/OpTwist`: two full axiom packages on one graph (a composition and its opposite, distinguished only by `emb`, every axiom holding by conversion); `is-prop (Σ emb , axioms) → ⊥` |
| `is-composable` | `pull-contr`, `push-contr` | property (both `is-contr`) | by construction |
| `is-unital` | per hand: `is-equiv (pre idn)`, `is-equiv (post idn)`, `idem : idn ⨾ idn ≡ idn` | property as a package (Capriotti–Kraus) | transcription = obligation O1; the package is the minimal propositional bearer of the unit tier (equivalences powerless without idem, idem is Ω²-slack without equivalences) |
| `is-stable` | `is-contr (Σ u ∶ readback , pins)` | property (`is-contr`); readback = projected center | `Test/AnchorPin`, `Test/SliceAnchor` (positive regimes), `Test/ReadbackTwist` (independence from everything else) |
| mediation | ♭-interchange, declared 0..n | structure — irreducible | CircleTensor: two inhabitants over identical everything-else, distinguished by winding |

`is-deductive-system` = `is-composable × is-unital × is-stable` —
one propositional master predicate on a virtual graph. The record:

```
record deductive-system o h : Type₊ (o ⊔ h)
  virtual-graph  : reflexive-graph + emb
  is-composable  : pull-contr ; push-contr
  is-unital      : eqv (pre idn) ; eqv (post idn) ; idem▿ ; idem▵
  is-stable      : is-contr (fiber flank-restrict canonical-flank)
```

The name is Lambek–Scott: homs as deductions, composition as cut,
identities as the axiom rule, *prior to the equational identification
of the two cut disciplines*. The tiers carry their proof-theoretic
readings: `is-composable` is cut admissibility on both hands,
`is-unital` the identity-rule laws, `is-stable` eta — evaluation at
the axiom context returns the deduction, uniquely, normalized at the
flanks.

## The tiers, exactly

**`virtual-graph`.** Reflexive graph plus `emb`. The pairing calculus
(`over`/`under`/`ctx`/`composite`/`ev`, the actions, both sequencing
protocols, the swap transposition) is definitional over it. Basic
fact, axiom-free: `hom x y ≃ Σ F , is-representable F`. `rx` stays in
the graph — it is constitutive of the calculus (the cut point), and
its laws live in the tiers above. `emb` is the model: the type of
axiom-satisfying embeddings over a graph is the type of category
structures the graph carries (`OpTwist`), and its identity type is
the structure-identity principle on the nose since everything above
is property.

**`is-composable`.** Both fibers, pointwise:
`is-contr (fiber emb (emb f ▾ g))` and
`is-contr (fiber emb (f ▴ emb g))`. Symmetric by ruling (Lane,
2026-07-21): op must be a strict involution on the bare record
(pull and push exchange as fields), and the embedding property must
be derivable without a mediation — both fail one-handed. Composition
per hand is the fiber center; each hand's full associahedron tower
(pentagon included) is paths-in-contractible-iterated-fibers,
consuming no interchange — the current `Cat.Coherence` routing
through `is-representable-prop` is an artifact to be re-routed at
port time.

**`is-unital`.** Emb-action form (the March form), per hand, stated
over (virtual-graph, `is-composable`) — `idem` mentions the fiber
centers, so the dependence is honest type-former dependence. The
emb-action equivalences are required (not the composition-action
`is-equiv (idn ⨾ −)` forms) because the stability tier's canonical
flank paths — `absorb-l`/`absorb-r` at `idn`, derived from
equivalence-cancellation over `pre-distr`/`post-distr` plus `idem` —
must exist readback-free; the composition-action forms reach the
`⨾`-unit laws but not the emb-action absorptions without readback —
so the stability tier's statement would be circular over them.
The composition-action package and the coherent-unit/HAE forms are
comparison material (Properties), not fields.

**`is-stable`.** The name is ruled (Lane, 2026-07-22): Abel's
*stability*, the NbE law that reading back the evaluation of a term
returns the term. The signature move, same as `⨾` from `pull-contr`:
never declare the structure, declare a contractible fiber and
project. Readback `u : ∀ f → ev (emb f) ≡ f` is a torsor over loop
families when bare; the fiber form states: the fiber of
flank-restriction (evaluate a readback family at the identities)
over the canonical flank family is contractible. The pin is
op-symmetric — both hands' flank canonicals — which makes the two
absorptions' agreement at `idn` the one cross-hand fact the record
asserts, propositionally, at the only place the hands must meet
(`Core.Path.Exchange`'s `unitl refl ≐ unitr refl` seal is this cell's
Core-level anticipation). `unit := center .fst`; all downstream
consumers unchanged. Regimes: path-presented instances satisfy it
(`AnchorPin`; and `SliceAnchor` proves the stronger collapse — over
contractible slices the whole (emb, readback) package is
contractible, model unique outright); truncated instances satisfy it
one-line (obligation O4); orphan-wild presentations fail it and are
not base citizens (the delooped tiers are their own records — below).

## The two-handed shape

A deductive system has TWO compositions — no general one. Each hand
carries a complete unital associative theory with its own
associahedron tower; the two are op-mirror images, so the library
writes one and transports the other. Shared between hands: the
presentation, the anchoring, the unit element, the embedding
property and representability calculus (derivable through either
hand; propositional, so the derivations agree). Mixed words —
`(f ⨾▿ g) ⨾▵ h` — are well-formed terms governed by no law: mixed
coherence cells are per-morphism properties, and that lattice IS the
duploid texture (thunkable/linear/medial; the CatData `Neutral`
inventory transcribes as its map). A single composition is exactly
what a mediation purchases: the identification of the two centers,
with the towers identified for free through the shared propositional
fibers — no pentagon-comparison ever stated.

## Med(D) and the extended theory

For a deductive system D, Med(D) is its space of mediations
(♭-interchange structures). Everything downstream is positioned
relative to it:

- **category** = D + one point of Med(D). The only structural field
  beyond the model. Unit laws, spine, flanks all derive; the spine
  reconstitutes via `spine-tail` with `⨾` preserved definitionally
  (the conservativity comparison to the current `category-axioms` is
  strict in this direction — the F∘G-strict pattern of Melliès'
  coherence theorem, `resources/mellies-dialogue-deformation` §2).
- **duploid-grade** = D + a polarity-partial mediation; the
  thunkable/linear boundary is its frontier (LB Phase 4 substrate).
- **braided-grade** = D + two points; ω their comparison loop. The
  homotopy of Med(D) is the braided content: π₀ counts
  hand-identifications, loops are crossings, the flank restriction
  carries the twist. The chirality wing is the theory of Med(−).
- **the monoidal tier** = the same schema transcribed over a base C,
  in its LAX variant: tensor virtual-graph, tensor `is-composable`,
  but `⊗₀-unit` as bare structure — the delooping cannot be anchored
  (its slices are never contractible short of triviality) and its
  anchoring freedom is the unit-tier content (flank observables,
  θ_I, twist). One schema, two anchoring modes, two levels; the
  refounded `Cat.Monoidal` field list already regroups onto it
  (adding `⊗₀-push-contr`, propositional, is the only new field).
- **dialogue/chirality** = pairs of deductive systems through op
  (strict involution, native to the layer), mediating structure
  between the pair; the deformation paper's DiaChi apparatus has its
  base citizen.
- **the LB wing** hooks at the stability tier — `is-stable` is the
  record-level NbE contract (readback = quote∘eval, whence the name)
  — outside the pure theory, by design.

Threshold criterion, ruled: the central component admits carrier/model
structure and predicates whose propositionality proofs consume only
prior tiers; everything else lives in the anchoring wing
(gauge/NbE/computation rules) or the chirality wing (Med).

## The certificate suite

- `Test/ReadbackTwist` — ℤ-negation twist: readback independent of
  composable + unital + mediation (its ⨾ is standard addition — the
  twist is purely presentational); also certifies the `comp-eq`
  family needs readback (`pre′` is subtraction there).
- `Test/OpTwist` — emb is the model; definitional countermodel.
- `Test/AnchorPin` — pinned readback contractible over path
  presentations, any pin; instantiated at `Cat.Groupoid` with
  `unit refl` as pin.
- `Test/SliceAnchor` — over contractible slices, `Σ (emb , readback)`
  contractible outright (no pin); `OpTwist` is its converse bracket.
- CircleTensor (landed prior) — Med-multiplicity is real; winding.

## Obligations (named, wing-internal, none architecture-blocking)

- **O1** — CK transcription: propositionality of the `is-unital`
  package over (virtual-graph, `is-composable`) only. Constraint: the
  proof may consume nothing beyond the type former. Fallback if it
  provably needs the stability tier: merge `is-unital` into the
  stability fiber (one joint contractibility package) and re-audit.
- **O2** — HAE question: whether a coherent-unit package at fixed rx
  closes propositionally (the gist's direction); refines O1 either
  way.
- **O3** — the delooped negative instance (hom = ℤ × S¹,
  winding-switched loop family): formalize the stability-tier
  dichotomy's negative half; groupoid-level work.
- **O4** — the truncated-regime certificates: hom-sets ⟹
  `is-stable` (one line); the classical-continuity theorem (the
  full bundle is property in the truncated regime).
- **O5** — ribbon-syntax decision: whether the free balanced dialogue
  category's base satisfies `is-stable` is entangled with internal
  decidability of tangle equivalence (its own NbE theorem). Deferred
  to the mint of the free structure; the lax variant is its fallback
  home by construction.
- **O6** — Core export gaps found by the spikes: `Int.Properties` has
  no arithmetic laws (assoc/zero/negation proved locally in
  `ReadbackTwist`); `Bool.Properties` does not export its
  discriminator. Chore-ledger items.

## The mechanical roadmap

Next session drafts the new theory fresh in `Cat.*`, with the frozen
tree at `Cat.Depreciated.*` as the porting reference (and
`Cat.Depreciated.CatData.*` for the magmoid-era material):

0. `virtual-graph` + the pairing calculus (re-homed from
   `Cat.Type`'s `virtual`/`representable`, unchanged content) + the
   basic fact.
1. `is-composable` + the two-handed theory: compositions, per-hand
   associativity via the E₃-fiber route, the associahedron towers,
   op as strict involution — acceptance test: op involutive on the
   nose, no mediation consumed anywhere in this phase.
2. `is-unital` + absorption via cancellation, embedding property via
   the push field, representability calculus, per-hand unit laws and
   unitors and triangle. O1 stated.
3. `is-stable` in fiber form + its derived theory: the `comp-eq`
   family, `emb-normal`-adjacent cells, the gauge material. O4
   discharged here.
4. `deductive-system` bundle; morphisms of deductive systems
   (lax/colax hand-flavors); SIP/moduli statements.
5. The mediation record + the Med layer: spine reconstitution,
   flanks, `category` = D + mediation; conservativity comparisons
   (current `category-axioms` ≃ D + mediation, strict direction
   definitional — acceptance test: `⨾` preserved definitionally
   through the reshape); Legacy recovery.
6. Monoidal re-stratification onto the lax schema: regroup the
   refounded field list, add `⊗₀-push-contr`, re-certify instances
   (Groupoid, Indiscrete, CircleTensor transcribe; the twist
   observable relocates from unitor-agreement to the flank cells —
   re-derivation obligation from the refoundation, carried forward).
7. Properties comparisons throughout; then the parity remainder of
   `2026-07-21-legacy-parity.md`, re-packaged (its steps were ruled
   valid transcription targets on GO).

## Open rulings

- **R1** — the lax variant's name (the delooped tiers' schema:
  deductive-system minus the stability tier's normalization, bare
  unit): needed at the monoidal re-stratification (step 6).
- **R2** — O5's ribbon-syntax placement, deferred to the free
  structure's mint.
