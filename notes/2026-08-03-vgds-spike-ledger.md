# Virtual-graph spike ledger

Checker-verified spike results from 2026-08-02 and 2026-08-03, on the
virtual-graph deductive-system carrier. Each entry states the question,
the verdict, and the model scope the verdict holds over.

Spike discipline — carrier shape, verdict tagging, and the at-risk bar —
is recorded separately and still governs new spikes.


## neutral-readback

_2026-08-02 SpikeNeutralReadback result — readback independent of twist neutrality; only 3/9 tower laws survive dropping readback_


`src/Test/SpikeNeutralReadback.lagda.md` (checker-verified, 2026-08-02)
settles: dropping the `readback` field from `virtual-graph` leaves only
`assoc⁺`, `assoc⁻`, `mixed-assoc` standing — not seven, as the spike's
own opening brief assumed. `unitr⁺`, `unitl⁻`, `pair⁺`, `pair⁻`,
`unitl⁺`, `unitr⁻` all read `readback` directly in `Cat.Logic.Base`'s
proofs, so all six drop with the field.

Neutrality of both twists does not derive readback. A single
parametrized Bool-endofunction model (commuting involutions `a`, `b`
standing in for the two twists) yields two instances that separate the
claims: `unital` (`a = b = not`) satisfies all four unit laws and the
round law `Q(P m) ≡ m`, and still refutes readback. `neutral`
(`a = not`, `b = id`) satisfies both invertibility tiers and both
neutrality tiers, and refutes every unit law and the round law. No
nonabelian group model was needed — the simpler shape sufficed. Both
instances also carry `is-invertible⁻`/`is-invertible⁺`, so no tier of
`is-deductive-system`, restated on a readback-free carrier, entails
readback. Open: what statement, added to the reduced tier, would
recover it — not any unit law, not the round law.

**Why:** the collapse-diagnosis chain (`Cat.Logic.Gist.PolarityCollapse`
→ this spike) is Lane's active line on whether readback is free or
forced structure in a deductive system, part of the wider
[[ribbon-tensorial-logic-goal]] formalization program.

**How to apply:** before assuming which tower theorems survive a
readback-free carrier, or attempting to re-derive readback from a
weaker hypothesis, check this result first — it is machine-checked
(`just check Test.SpikeNeutralReadback`), not conjectured.

## neutral-tier

_"2026-08-02 SpikeNeutralTier result — neutrality (equivalence, not contractibility) fully replaces is-invertible when readback is kept"_


`src/Test/SpikeNeutralTier.lagda.md` (checker-verified, 2026-08-02) is
the readback-kept counterpart to
[[spike-neutral-readback-result]] (the readback-dropped carrier). Over
`Cat.Logic.Type.virtual-graph` unchanged (readback present), a strictly
weaker tier than `is-invertible⁻`/`is-invertible⁺` — one `is-equiv`
condition per hand on the *far* flanking operation, not fiber
contractibility — derives the full working content of the balanced
tier: both cancellations, both absorptions, and both of the previously
"balanced-only" unit laws `unitl⁺`/`unitr⁻` (via "an idempotent
equivalence is the identity"). Consequence: the polarity-collapse route
(`cut⁻-cross`, `cut⁺-cross`, `from-linear`, `from-thunkable`) runs
unblocked from this tier alone — the brief expected it blocked, and it
is not. Non-vacuous: `Cat.Logic.Gist.BalancedWord`'s free point (`BW`)
satisfies the tier and still refutes thunkability/linearity, so the
tier holds of a genuine non-category.

What it does *not* recover: the contractible form of `is-invertible⁻`
itself (the fiber gets a point and every point is forced to the same
edge, but nothing here names the fiber's own paths) — the tier is
strictly weaker there even though it is equal in everything the tower
actually consumes.

**Why:** same active line as [[spike-neutral-readback-result]] — Lane's
formalization thread on whether `readback`/`is-invertible` are free or
forced structure, part of the wider [[ribbon-tensorial-logic-goal]]
program.

**How to apply:** if `is-invertible⁻`/`is-invertible⁺` ever look like a
bottleneck (their contractibility is a strong ask), this result says a
plain equivalence condition on each hand's far flank is enough for
every consequence the tower actually uses — check this file before
reaching for the stronger tier, or before assuming it can't be
replaced.

## natural-tier

_"2026-08-03 SpikeNaturalTier result — naturality tier over a readback-free carrier is a genuine hypothesis, not a theorem; no single model gives non-unit twists with associates failing"_


`src/Test/SpikeNaturalTier.lagda.md` (checker-verified, `--cubical`,
2026-08-03) is the third leg of the readback/collapse thread, after
[[spike-neutral-readback-result]] and [[spike-neutral-tier-result]].
Built on the archived `Bb.WeakDeductiveSystem` tree (the live
`Cat.Logic` carrier as it stood before readback was added to
`virtual-graph`), it posits `is-natural⁻`/`is-natural⁺` — one
contractible-centre tier per hand, each twist paired with the hand
whose junction it does not fill — in place of readback.

Key findings:

- Contractibility does **not** reduce to inhabitation under stability
  alone (a correction to the hoped-for reading in the brief). The
  centred-pair type splits as `fiber reflect × (judgment path space)`;
  stability only makes the first factor propositional. The second
  factor needs an independent hypothesis (hom sets, in both models
  used here).
- The tiers derive the readback-free tower and one naturality square
  per hand, but no unit law and no crossed cut — confirmed by a
  circle-groupoid countermodel (`t⁺ = refl`, `t⁻ = rot`) that refutes
  all four unit laws, both crossed cuts, and idempotence.
- No single checked-in model gives *both* non-unit twists *and* a
  failing `associates` in one carrier. The circle model gives non-unit
  twists but `associates` holds there (degenerate). `Cat.Logic.Gist.
  BalancedWord`, forgotten to the readback-free carrier, refutes
  `associates` but turns out to satisfy all four unit laws anyway. That
  gap is the open target, not a settled either-or.
- Naturality is confirmed not derivable from stability:
  `Bb.WeakDeductiveSystem.Gist.AssociatesCountermodel`'s `four-reader`
  is a full deductive system (stability, both cuts, both invertibility
  tiers) on this carrier that refutes the negative tier outright.
- **Correction to the ledger's proposed countermodel** (hand-checked,
  marked `inferred`, not mechanized): a nonabelian group at
  `t⁻ = g`, `t⁺ = g⁻¹` does NOT refute naturality — the mutually-inverse
  twists make both sides of the naturality equation collapse to `m ≡ m`
  trivially. The reading that actually forces centrality is
  `t⁻ = g`, `t⁺ = 1` (a fixed identity, not the group inverse of `t⁻`).
  `four-reader` already discharges the intended job without building
  this group model.

**Why:** same active line as [[spike-neutral-readback-result]] and
[[spike-neutral-tier-result]] — part of the wider
[[ribbon-tensorial-logic-goal]] program on whether readback/unitality is
free or forced structure.

**How to apply:** before re-proposing a group-style countermodel for a
naturality-vs-conjugation question in this framing, check the twists'
relationship first — mutually-inverse twists trivialize naturality
equations rather than testing them; a fixed/identity twist on one side
is what isolates centrality.

## natural-truncation

_2026-08-03 SpikeNaturalTruncation result — the naturality tier truncates to hom-sets under absorption; the underlying equation is wild-compatible and decomposes the tier exactly_


`src/Test/SpikeNaturalTruncation.lagda.md` (checker-verified,
`--cubical`, 2026-08-03) is the fourth leg of the readback/collapse
thread, after [[spike-neutral-readback-result]],
[[spike-neutral-tier-result]], and [[spike-natural-tier-result]]. It
measures the naturality tier from that third spike against wildness.

Key findings:

- The tier's truncation is exact, not approximate: `centred≃` plus
  stability (making `reflect` an embedding, so `ap reflect` has a
  retraction) forces a trivial loop specifically at the edge
  `twist⁻ x ⨾⁻ m` (negative hand) / `m ⨾⁺ twist⁺ y` (positive hand), at
  every `m` — the precise statement, not "homs are sets" outright.
  Wherever the twists absorb, though, those flanked edges are every
  edge, so absorption alone upgrades the tier to forcing full hom-sets.
- `Cat.Logic.Gist.ThunkableSquare`'s circle model (ported via
  `forget-readback`, no restatement needed) refutes both tiers. It is
  not a degenerate escape: the model's twists absorb (all four unit
  laws hold), so it's a genuine balanced deductive system with non-set
  homs where specifically the naturality *tier* fails while the
  naturality *equation* holds.
- The obstruction has a clean general form (`diagonal.unfold`):
  wherever a family of path comparisons meets its own diagonal — which
  naturality does, at the twist — any propositional demand on the
  family becomes a demand on a loop space. `is-invertible` (fixed
  target) and associativity (compares two representatives of *one*
  judgment) both dodge this; naturality (two judgments that both vary
  with `m`) cannot.
- The equation form (`is-naturalᴶ⁻`/`is-naturalᴶ⁺`, naturality as a
  plain judgment-level path rather than a contractible centre) is fully
  wild-compatible: each hand's square follows via the same
  stability-uniqueness route `assoc⁺` uses, no h-level required. The
  tier decomposes exactly as equation + "leading judgment's loop space
  is a proposition." Under absorption, the equation collapses to
  exactly the far-side unit law the framing already withholds — so
  there is no way to make it free by re-presenting the twists; it would
  need the reflected composition to associate on the nose, which only
  strict (non-wild) carriers have.
- The equation is structure with a `rot`-winding torsor moduli, the
  same generator `Cat.Logic.Gist.ReadbackTorsor` measures on the same
  circle model. Explicitly left open (not overclaimed): whether the two
  moduli are literally the same type, only that both separate by one
  winding.

**Why:** same active line as the other three — part of the wider
[[ribbon-tensorial-logic-goal]] program on whether readback/unitality is
free or forced structure over a wild carrier.

**How to apply:** when a tier is stated as `is-contr` of a comparison
between two things that both vary with the same parameter (not a fixed
target, not one judgment under two bracketings), expect it to truncate
on a wild carrier — check whether the comparison meets its own diagonal
first (`diagonal.unfold`'s shape). The fix that survives wildness is
usually to state the plain equation and add contractibility only as an
extra, separately-flagged hypothesis when actually needed.

## natural-moduli

_2026-08-03 SpikeNaturalModuli result — readback and naturality moduli share one winding generator (opposite sign) but aren't shown equivalent as types; idempotence is not the residual difference_


`src/Test/SpikeNaturalModuli.lagda.md` (checker-verified, `--cubical`,
2026-08-03) is the fifth leg of the readback/collapse thread, following
[[spike-natural-truncation-result]]. It compares the readback modulus
(`Cat.Logic.Gist.ReadbackTorsor`) against the naturality moduli
(`Test.SpikeNaturalTruncation`'s `is-naturalᴶ⁻`/`is-naturalᴶ⁺`) on one
carrier — the circle model, forgotten onto the readback-free carrier.

Key findings:

- **General theorem, not model-specific**: over any carrier with
  stability, both cuts, and readback, naturality-in-a-hand and that
  hand's *far* unit law are inter-derivable (`with-readback.far⁻`/
  `from-far⁻` for `unitr⁻-law`, `far⁺`/`from-far⁺` for `unitl⁺-law`).
  This sharpens the open question from
  [[spike-natural-truncation-result]] into an exact characterization: a
  route from readback to naturality is exactly a route to the far unit
  law of that hand.
- **Claim (B) refuted, precisely.** The brief hypothesized idempotence
  of the twist as the residual difference between readback and
  naturality. It isn't: readback alone (no naturality, no extra tier)
  already gives idempotence via the *near* unit law specialized at the
  twist itself (`with-readback.idem⁻`, needing only readback + both
  cuts — the cheap route, not `Test.SpikeNeutralTier`'s far-flank
  machinery which needs an extra equivalence hypothesis). The far unit
  law specialized at the twist gives the same idempotence
  (`diagonal-of-far⁻`). So idempotence sits on the readback side of the
  ledger for either unit law — it cannot be what naturality adds.
- **Claim (A), the precise form it actually supports**: not a type
  equivalence. `readback-of M`'s witnesses are paths in the hom type
  (one per edge); `is-naturalᴶ⁻ M`'s witnesses are paths in the
  judgment type (one per edge and argument) — genuinely different
  shapes, and the spike does not paper over this with `funext`. What it
  does establish: both moduli are torsors under one common measure (a
  witness read at the unit edge, at the axiom, is a loop at `base`;
  each shift adds exactly one `loop`), and the model-local maps
  `to⁻`/`from⁻` (readback ↔ naturality, both needing absorption) send
  the readback shift to the *inverse* naturality shift — one shift on
  each side cancels (`generators`). The two generators correspond, in
  opposite orientation, not as one type.
- **Over the circle model specifically, readback and the far negative
  unit law are the same type by `refl`**
  (`moduli.readback-is-far⁻`) — the negative cut is literally the
  model's multiplication and the negative twist is its unit, so this
  model cannot separate the readback field from `unitr⁻-law` at all. A
  carrier that does separate them would have to be non-absorbing and
  wild; this spike exhibits none (`turn`, the non-absorbing circle
  model, has set-valued homs and carries no moduli to compare).
- Confirms `Cat.Logic.Gist.ReadbackTorsor`'s witnesses are literally
  this spike's `rb₀`/`rb₁` (`torsor-witness`/`torsor-shift`, both
  `refl`) — the readback field, once forgotten via `forget-readback`
  and restated as a predicate (`readback-of`), is the *same type*
  across the two spikes, not merely isomorphic.

**Why:** same active line as [[spike-natural-truncation-result]] and
the earlier three — part of the [[ribbon-tensorial-logic-goal]]
program on whether readback/unitality is free or forced structure over
a wild carrier.

**How to apply:** when comparing two "moduli" types (free-structure
freedoms) that look superficially similar (same winding count, same
generator shape), check whether the witnesses even live in the same
ambient type before asking if the types are equivalent — this spike's
readback witnesses are hom-paths and its naturality witnesses are
judgment-paths, and conflating them would have been the easy mistake.
A shared "measure into a common loop space" is weaker than a type
equivalence but can still pin down the sign/orientation relationship
exactly, which is often the more decision-relevant fact anyway.

## twist-mediation

_2026-08-03 SpikeTwistMediation result — Kraus-style recognition works for the twist pair via mediation (the two-cut defect structure), no idempotence and no unit assumption; the positive clause alone pins the pair uniquely at the word model_


`src/Test/SpikeTwistMediation.lagda.md` (checker-verified, `--safe
--erased-cubical`, 2026-08-03) tests whether Kraus's canonicalization
mechanism (*Identities via Idempotent Equivalences*, 2020 — his
recognition principle is idempotence, which forces the canonical
element to be a unit) has an analogue for the twist framing where the
canonical element is a genuine twist PAIR, not a unit. It runs on
`Cat.Logic.Gist.BalancedWord`'s free framed point `BW`, using
`Cat.Logic.Gist.AssociatesDefect`'s corrected-reassociation words
(`w⁺`/`w⁻`) as the candidate recognition principle ("mediation").

Key findings, hand-verified line-by-line (not just checker-trusted,
given how consequential this is):

- **The recognition works, and works with only the positive clause.**
  `mediation-contr : is-contr (Σ (W × W) mediates)` and
  `recognition : ∀ p → mediates p ≃ (p ≡ (τ̂ , ε̂))` — the Kraus shape,
  achieved. But `mediation⁺-contr`/`recognition⁺` show the POSITIVE
  clause alone (`mediates⁺`) already pins the pair uniquely; the
  negative clause is not needed for uniqueness. Two triples do all the
  work: `(ε̂, τ̂, ε̂)` (where `rise ε̂ = Z` makes the correction word
  collapse definitionally to `θ⁺` itself, isolating `θ⁺ ≡ ε̂`) and
  `(τ̂, ε̂, ε̂)` (where `rise τ̂ = S Z` unfolds the correction to
  `θ⁻ ⨾⁺ (θ⁺ ⨾⁺ (θ⁺ ⨾⁻ θ⁺))`, and cancelling the double twist on the
  right via `cancel-δ` isolates `θ⁻ ≡ τ̂`).
- **Associativity never enters the recognition.** The mediation clause
  at a triple IS the corrected reassociation — instantiating it at the
  two pinning triples substitutes for every place Kraus's proof would
  reach for `ass`. `assoc⁺` (this carrier's own genuine associator, on
  the hand that associates on the nose) appears only inside the ported
  Kraus tools (`eqv-2-out-of-3`), never in the recognition proper.
- **The recognition consumes no equivalence tier.** Kraus needs
  `is-eqv` because idempotence at a fixed element carries residual
  freedom that only an equivalence hypothesis kills. Mediation at a
  fixed candidate pair carries no such freedom on this model —
  `is-eqv⁺` is ported and used only for the `canonical`/
  `eqv-2-out-of-3` machinery, not for the pinning itself.
- **The negative clause is not idle, but doesn't pin alone.** It
  refutes the swapped pair `(ε̂, τ̂)` outright (`swap-not-mediates⁻`,
  via `bicyclic-persists`). But the equation it yields at its own
  reducing triple (`head⁻ : θ⁻ ⨾⁺ θ⁺ ≡ τ̂`) is satisfied by the swapped
  pair too (`swap-head`), so `mediates⁻` alone is left open — not
  settled either way.
- **`canon-is-twist⁺` measures the collapse concretely.** Kraus's `I`
  operator, ported and applied to any positive-hand equivalence, always
  lands on `ε̂` — the canonical element under his idempotence recognition
  is a genuine unit here too, confirming this framing's mediation
  principle is doing something idempotence provably cannot (produce a
  non-unit canonical pair).
- **A general (non-word-model) statement of `mediates` needs an
  abstract index.** `rise f`/`zrunW h` are model-specific `Nat`-valued
  evaluations with no carrier-level form. The existential-over-
  correction-words weakening does NOT support this recognition as
  written — both pinning triples use the exact index the model
  computes, not an existentially-quantified stand-in. `twist⁻-not-eqv⁺`
  also fixes the shape any general `is-eqv-pair` condition must take:
  each twist is an equivalence of its OWN hand only (`τ̂` is not a
  positive-hand equivalence), so a condition reading both twists in one
  hand is already empty at this model.
- Licenses a spike at the general carrier, and no more — this is one
  set-truncated model, and `mediates` being a proposition here is
  supplied by the model's h-level, not by anything general.

**Why:** part of the [[ribbon-tensorial-logic-goal]] program, same
active line as the readback/naturality spikes
([[spike-natural-moduli-result]] etc.), but a different question: not
whether readback is free/forced, but whether the twist PAIR itself has
a non-circular recognition principle (the 2026-07-27 one-twist verdict
already ruled out deriving one twist from the other by extraction, so
the canonical object has to be a pair).

**How to apply:** when a "two bracketings differ by a correction word"
result exists (any defect/coherence analysis), check whether
instantiating the correction clause at a couple of well-chosen small
triples pins the correction's parameters directly — this can produce a
Kraus-style recognition without ever invoking the associativity the
correction was compensating for, and without needing an equivalence
hypothesis if the model has no residual freedom at the fixed point.
`Bb.UnitalMagmoids`'s `Neutral`/`Unit` modules are proof-shape
references only, not literally importable, when working over
`Cat.Logic.Type.virtual-graph`'s two-cut presentation — they use an
architecturally different single-composition, Yoneda-embedding-based
`magmoids` record and already assume a chosen unital witness as a
parameter, so reaching for them directly would smuggle in exactly the
unitality collapse a mediation-style principle is trying to avoid.

## mediation-wild

_2026-08-03 SpikeMediationWild result — mediation's Kraus-style recognition contracts even over wild (non-set) homs at the circle model; witness freedom and identification freedom cancel exactly, with one honest residual step the model donates but the stated tier doesn't supply_


`src/Test/SpikeMediationWild.lagda.md` (checker-verified, `--cubical
--safe --no-guardedness`, 2026-08-03) tests the untested half of
[[spike-twist-mediation-result]]'s Kraus program: ingredient (ii),
where witness freedom at a fixed element cancels against
identification freedom. The word model is a set, so mediation there is
propositional for free and never exercises this. This spike moves to
`Cat.Logic.Gist.ThunkableSquare`'s circle model (wild, non-set homs) to
test it for real. I re-verified the delivered file myself (independent
`just check`, lint, prose-lint runs, plus hand-tracing the two
load-bearing constructions against their stated types) rather than
trusting the dispatched agent's self-report.

Key findings:

- **`mediates₂`: a carrier-generic restriction, not a new principle.**
  `Test.SpikeTwistMediation`'s `mediates⁺`/`recognize⁺` only ever reads
  the correction word at two triples, `(ε̂,τ̂,ε̂)` (level zero) and
  `(τ̂,ε̂,ε̂)` (level one). `mediates₂` asserts exactly those two clauses,
  generically over any `virtual-graph` with two cuts (`Bb.WeakDeductiveSystem.Base`'s
  tower). At the word model, `word.restrict θ⁻ θ⁺ M = M ε̂ τ̂ ε̂ , M τ̂ ε̂ ε̂`
  typechecks with **no coercion** — the generic two-clause statement
  literally *is* the restriction of `mediates⁺`, machine-confirmed, not
  asserted.
- **Step 1 succeeds outright: no information is lost.** The full
  `pin⁺`/`pin⁻`/`recognition`/`mediation-contr` chain from
  `SpikeTwistMediation` transfers to `mediates₂` verbatim (only
  substituting `M .fst`/`M .snd` for `M ε̂ τ̂ ε̂`/`M τ̂ ε̂ ε̂`). No index
  abstraction was needed — the brief's fallback path was not triggered.
- **The freedom is genuinely present at the circle, on both sides.**
  `mediates₂ tt (base,base)` is a loop-space square at `base`; the
  constant witness and its `rot`-shift separate by one winding
  (`circle.mediates₂-not-prop`, the exact mechanism of
  `ThunkableSquare.thunkable-not-prop`). The identification type
  `(base,base) ≡ (base,base)` in `pair tt = Circle × Circle` is *also*
  wild (`circle.pair-path-not-prop`) — both sides of the Kraus
  recognition carry freedom here, not just the witness side.
- **The equivalence tier holds at every pair, not just at the twists —
  and contributes nothing to the contraction.** `circle.eqv-all` shows
  every translation at the circle is an equivalence, so
  `is-eqv-pair tt p` is contractible for *every* `p`, not merely at
  `(base,base)`. The tier factor therefore drops out of the Σ for free
  (`Σ-contr-fst`); what it actually supplies is the *shape* of the
  condition (each component read in its own hand), which is what makes
  `Test.SpikeTwistMediation.twist⁻-not-eqv⁺` bite in the first place —
  it cancels no freedom at this model.
- **The two freedoms cancel exactly — the contraction goes through.**
  `circle.sides : pair tt → Circle × Circle` collects the two clauses'
  right-hand sides; it is a genuine equivalence
  (`Σ-dep-map-is-equiv`, composing two independent right-translation
  equivalences), and its fixing `(base,base)` (definitionally, via
  `mult base y ≡ y`) makes `ap sides` an equivalence too. Composing
  gives `circle.recognition₂ : mediates₂ tt p ≃ (p ≡ (base,base))` at a
  FIXED pair — the genuine Kraus-shaped statement, with witness freedom
  present on both sides, not vacuous. `circle.framed-contr` then
  contracts `Σ pair (is-eqv-pair × mediates₂)`, so
  `∀ x → framed x` is a **proposition** at this model.
- **The honest residual: one step the model donates, the tier doesn't
  supply.** The fiber map of `sides` is right-translation by the
  compound word `θ⁺ ⨾⁺ (θ⁺ ⨾⁻ θ⁺)`, not by `θ⁺` or `θ⁻` alone. The
  circle model makes *every* right translation an equivalence
  (`mult-r-equiv`, at any argument), which is what makes this step free
  here — but `is-eqv-pair` as stated only asserts translation-by-θ⁻
  and translation-by-θ⁺ are equivalences, not translation by that
  composite. A non-circle (or general) carrier would need to either
  supply that step directly or derive it from the stated tier; this
  spike does not attempt either, per its own scope.
- **The recognition is triangular, not componentwise.** Clause zero
  pins `θ⁺` alone; clause one pins `θ⁻` only using clause zero's
  answer (`pin⁻`'s proof literally substitutes `pin⁺` into its own
  chain). There is no independent per-component equivalence — the
  whole-pair equivalence is what holds, and that shape carries over
  from the word model to the circle model unchanged.
- **Degeneracy, named honestly.** Both twists are `base` at this
  model, so the *pinning* content of recognition (that the pair is
  forced to be THE twists, not merely some pair) is tested only up to
  the model's own symmetry — a wild carrier with two genuinely distinct
  twists would test pinning and freedom at once, and none exists in
  the library. The cancellation verdict stands regardless, because the
  freedom being cancelled lives in the witnesses, not in the pair.

**Why:** closes the ingredient-(ii) gap [[spike-twist-mediation-result]]
left open — same active line, part of the
[[ribbon-tensorial-logic-goal]] program. Together the two spikes show
mediation's Kraus-shaped recognition is not an artifact of the word
model's set-truncation: it survives moving to wild homs, with the
freedom cancellation verified rather than assumed.

**How to apply:** when a Kraus-style recognition principle is
suspected of only working because the ambient type happens to be a
set, don't just note the set-truncation as a caveat — build (or reuse)
a wild instrument and check whether the recognition equivalence still
states and proves at a genuinely non-propositional fixed point. Here
`Cat.Logic.Gist.ThunkableSquare`'s circle model, already forgotten onto
the readback-free carrier by `Test.SpikeNaturalTruncation`'s `disc`
pattern, was reusable directly (`Trunc.disc.M`/`stable`/`comp⁺`/
`comp⁻`) — check for an existing wild-carrier instantiation before
building a new one. When a Σ-contraction over wild data succeeds,
check whether it succeeds by a genuine equivalence argument
(`Σ-dep-map-is-equiv`-style, composing real per-component
equivalences) rather than by the family accidentally being trivial;
the fastest test is whether the "freedom" side (here,
`mediates₂-not-prop`/`pair-path-not-prop`) was independently shown
non-propositional before the contraction was attempted — a
contraction of something never shown to have content proves less than
it looks like.

## self-mediation

_2026-08-03 SpikeSelfMediation result — mediation restated with the candidate pair in every position (no carrier twist reference) is statable but does NOT recognize alone; a concrete counterexample survives both clauses; the equivalence tier alone pins the pair at the word model, with no clause read_


`src/Test/SpikeSelfMediation.lagda.md` (checker-verified, `--cubical
--safe --no-guardedness`, 2026-08-03) tests whether mediation's two
clauses can be restated with the candidate pair standing in every
position — including the fixed-twist flanks the original
[[spike-mediation-wild-result]] clauses read from the carrier — so
that a hypothetical minimal carrier (`ob`, `hom`, `reflect` only, no
twist fields) could still state "has a framing" self-referentially. I
independently re-verified the delivered file (own `just check`,
lint, prose-lint runs, plus hand-tracing `slack₀`, `post-unit`,
`φ-unit`, and `tier-pins` against their stated types) rather than
trusting the dispatched agent's self-report.

Key findings:

- **Statable, with one caveat.** The self-referential clauses
  (`selfclause₀`, `selfclause₁`) genuinely read no carrier twist —
  confirmed by scope (the `self` module opens `virtual-graph G using
  (ob)` only). But `is-composable⁺`/`is-composable⁻` (the two
  composability parameters every carrier still needs) unfold through
  `var`/`covar`, which DO hold `twist⁻`/`twist⁺`. So a genuine
  three-field carrier would still need to restate the two cuts
  without reference to a framing — "three fields" is not free just
  because the clauses themselves are twist-free.
- **The self-referential clauses alone do NOT recognize the pair —
  refuted by a concrete counterexample, not merely unproven.**
  `word.clauses-alone` exhibits `(ω̂ , ε̂)` (`ω̂ = Z∷[], S(S Z)`, a
  word not equal to any of `ε̂`/`τ̂`/`δ̂`) satisfying both
  `selfclause₀` and `selfclause₁`, while `ω̂ ≠ τ̂`. This is a real,
  machine-checked second solution, not a gap in the proof attempt.
- **`selfclause₀` is structurally weak, not just weak at one point.**
  `word.slack₀ : (a : W) → selfclause₀ tt (a , ε̂)` — the first clause
  holds at EVERY pair whose second component is `ε̂`, regardless of
  the first, via a two-line proof (`ap (λX → ε̂⨾⁺(X⨾⁻ε̂)) (sym
  (comp-unitl a))`). This happens because `corr₀ p = p .snd`
  unconditionally (by `corr₀`'s bare definition), so once the second
  component is fixed at `ε̂`, the clause can never discriminate the
  first — a structural fact about the self-referential form, not an
  artifact of the word model.
- **The tier alone pins the pair, with no clause read at all —
  the session's central, somewhat surprising result.**
  `word.tier-pins : (p : pair tt) → is-eqv-pair tt p → p ≡ (τ̂ , ε̂)`
  never mentions `selfmediates₂`/`selfclause₀`/`selfclause₁` in its
  statement or proof. The route: `is-eqv⁺ e`'s right-translation
  equivalence makes `e` a two-sided unit of `⨾⁺` (`post-unit`, via
  the counit/unit of the equivalence plus `equiv→lc`), and a
  two-sided `⨾⁺`-unit is provably `ε̂` (`unit-is-ε`, via an
  "injective self-map of ℕ with a pointwise inverse dominates the
  identity in both directions, hence is exactly identity" argument on
  the descriptor's denotation). The negative hand transposes through
  `a ⨾⁻ h` being definitionally `φW a ⨾⁺ h`, so `is-eqv⁻ a` makes
  `φW a` a `⨾⁺`-unit, hence `≡ ε̂`, hence (`φ-unit`) `a ≡ τ̂`. So at
  this model, the tier is already doing all the recognition work;
  `ω̂` fails the tier (`word.ω-not-eqv`) even though it satisfies both
  clauses.
- **Verdict (ii): tier + selfmediates₂ recognizes, tier is
  load-bearing, not optional.** `word.recognition₂`/
  `word.framed-contr`/`word.has-framing-is-prop` go through — but
  honestly qualified: since the tier alone already pins the pair at
  this model, the word model gives no evidence that the clauses
  narrow anything here. A carrier with a strictly weaker tier is what
  would actually test whether the self-referential clauses pull their
  weight.
- **The circle check is narrower than the brief assumed, and the
  agent corrected this rather than asserting the brief's claim.**
  At `(base,base)` the spiked and self-referential clauses ARE the
  same type (`circle.agree₀`/`agree₁`, both `refl`), so the witness
  and non-propositionality carry over (`circle.m₀`,
  `circle.selfmediates₂-not-prop`). But away from that one pair the
  two families differ (spiked clauses read fixed `base`, self-clauses
  move with `p`), so the WILD CONTRACTION does not transfer — only
  the pointwise coincidence at the actual pair does. The delivered
  module states only the narrower, checked claim.

**Why:** part of the [[ribbon-tensorial-logic-goal]] program's
freeze-input gathering, alongside the composite-translation spike
(tier clause count) — this one settles whether mediation's clauses
can be stated without carrier twist fields at all, ahead of any
"three-field carrier" freeze decision. Companion to
[[spike-mediation-wild-result]] (same base module, `mediation`) and
run in parallel with the sibling `is-eqv-pair`/composite-translation
spike — independent files, no shared state, both build on
`Test.SpikeMediationWild`.

**How to apply:** when generalizing a recognition-style clause by
substituting a candidate for every occurrence of a "true" reference
value (not just the position the correction term already uses), check
first whether any position's correction is UNCONDITIONALLY equal to
one of the candidate's own components by its bare definition (here,
`corr₀ p = p .snd` always) — if so, that clause has already lost its
only anchor to the outside value and is a strong candidate to degrade
into a self-consistency condition satisfied by more than the intended
witness. Test for this directly by trying obviously-adjacent
candidates (here, "same value in both slots" and "vary one slot while
fixing the other at the true value") before trusting that a
recognition principle transfers unchanged. Separately: when a
`refl`-provable equality is unexpected for a general lemma that's only
propositionally true (e.g. `comp-unitl`/`comp-unitr` are proved via
`ev-inj`, not stated as `refl`), remember that concrete ground
instances of decidable/computable structures often normalize away
definitionally even when the general lemma needs an inductive
argument — a `refl` at one specific pair is not evidence the general
statement is definitional.

## candidate-generator

_2026-08-03 SpikeCandidateGenerator result — neither candidate-relative invertibility (A) nor candidate-relative readback (B) alone replaces the equivalence-tier-plus-clauses conjunction; readback is the stronger single condition (pins the word model with no tier consumed) but does not contract at the circle, even combined with invertibility_


`src/Test/SpikeCandidateGenerator.lagda.md` (checker-verified, `--cubical
--safe --no-guardedness`, 2026-08-03) asks whether a single
candidate-relative condition can replace [[spike-self-mediation-result]]'s
conjunction (an equivalence tier plus two self-referential clauses,
which pin by different halves at different models). Two candidates:
(A) candidate-relative invertibility `inv[p]` — each action map has a
contractible fiber over the second projection, the old `is-invertible⁻/⁺`
with the candidate pair `p=(θ⁻,θ⁺)` substituted for the twists; (B)
candidate-relative readback `rb[p]` — reflection at the candidate axiom
returns the edge, for every edge. I independently re-verified the
delivered file (own `just check`, lint, prose-lint, plus hand-tracing
the load-bearing constructions against their stated types and against
`iso→equiv`'s actual `sec`/`retr` argument order) rather than trusting
the agent's self-report.

Key findings:

- **Statable with no leak, and confirmed cheaply this time.** `cand`
  builds `var[p]`/`covar[p]`/both action maps/`inv[p]`/`rb[p]` over
  `ob`, `hom`, `reflect` alone — no twist field, and (new relative to
  the sibling spike) no cut either; the kit doesn't even take
  `(S,C⁺,C⁻)` as parameters. (A) is pointwise propositional
  (`is-contr-is-prop` alone); (B) is not, refuted at the circle's
  actual pair by a `rot`-shift witness pair, same mechanism as
  `mediates₂-not-prop` in [[spike-mediation-wild-result]].
- **A real record-shape finding: the two candidates live at different
  quantifier depths.** `inv[p]` reads one object (each action map
  closes an argument half whose axiom sits there); `rb[p]` reads a
  pair of objects (the edge it recognizes runs between two). A record
  built on invertibility is naturally object-indexed; one built on
  readback is not. This wasn't asked for explicitly — the agent
  surfaced it as a consequence of stating both conditions side by
  side.
- **Word model: (A) excludes everything the conjunction excludes, but
  doesn't obviously PIN.** Six-pair census (actual, impostor `ω̂`, four
  degenerates, one perverse pair) — every non-twist pair fails `inv[p]`,
  by emptiness in three cases and non-uniqueness in three. The census
  is real evidence, but the agent explicitly declined to claim a full
  pinning theorem for (A) — that would need "unique one-sided inverse
  ⟹ injective denotation," left unbuilt, flagged honestly rather than
  asserted.
- **Word model: (B) pins outright, with NO tier consumed — stronger
  than the brief expected.** `rb[p]`'s defining equation alone makes
  the two candidate-translations mutually inverse by associativity
  alone (`recognize.sec`/`retr`, no unit law used), so the leading
  translation is an equivalence; `SpikeSelfMediation.word.post-unit`
  and `φ-unit` then return the twist pair directly from that one hand.
  `word.rb-contr` contracts `Σ p, rb p`, and the tier, both clauses,
  and invertibility all transport back along the pinning
  (`rb→inv`, `rb→eqv`, `rb→clauses`). I hand-verified this chain in
  full — `recognize.pin-b`'s four-step composition in particular is a
  genuinely elegant reuse of the SAME `rb` equation at a second
  instance (`f = ε̂`) after `pin-a` is already in hand.
- **Circle: the two candidates cleanly separate, and NEITHER
  contracts — the brief's "session's centre" resolves negatively.**
  (A) holds at every pair (vacuous, exactly like the eqv-tier in
  [[spike-mediation-wild-result]]) — both its fibers reduce to fibers
  of left/right translation, and every circle translation is an
  equivalence. (B) selects: `rb[p]` at `(a,b)` unfolds to
  `∀f, mult a (mult f b) ≡ f` (no extra `mult _ base` factor — my own
  recon corrected the brief's guessed form here, and the agent
  independently confirmed the correction), which holds exactly when
  `mult a b ≡ base` (`rb-base` necessary, `rb-cancel` sufficient, the
  loop step built from scratch via `mult-ap-rot`/`rot-square` since no
  propositionality shortcut applies here — this is real, non-trivial
  cubical work, not a restatement of an existing library lemma). That
  condition holds on a WHOLE circle of pairs (one for each `a`, taking
  `b = a⁻¹`), so `Σ p, rb p` retracts onto `Circle` and is provably
  not contractible (`rb-not-contr`, standard "retract of contractible
  is contractible, contradicts `loop-nontrivial`" argument). Adding
  (A) changes nothing, since (A) is vacuous there
  (`both-not-contr`) — so candidate (iv) ("B generates but needs A as
  its engine") is refuted too, not just (i) and (ii).
- **Subsumption: readback is strictly the stronger condition, but the
  old readback-derives-clauses argument does not transcribe whole.**
  `cand.fiber⁻-point`/`fiber⁺-point` (the candidate-relative analogue
  of `Cat.Logic.Base.balanced.centre⁻-twist⁺`) transcribe cleanly —
  `rb[p]` forces each fiber's point to the candidate's own component,
  no tier, no cut. But the `SpikeNeutralReadback.with-readback` unit-law
  bridge does NOT transcribe: it rewrites a cut into an action map by
  closing the term half at the CARRIER's own `var`, not the
  candidate's — a structural mismatch, not a missing lemma. So the two
  clauses carry residual content beyond `rb[p]` over a general carrier;
  the residue happens to vanish at the word model specifically, because
  there `rb[p]` already pins the candidate back to the carrier's own
  framing (so "the carrier's `var`" and "the candidate's" coincide
  after the fact).
- **Verdict: (iii), neither condition alone generates.** Readback is
  the stronger of the two — it pins the word model outright where
  invertibility only excludes, and it selects at the circle where
  invertibility is vacuous — but it does not contract at the circle,
  alone or combined with invertibility. The tier-plus-clauses
  conjunction stands; the census tables are the record of what each
  half of it is independently pulling weight for.
- **Self-correction, reported honestly rather than smoothed over.** My
  own recon (handed to the dispatched agent) had warned that
  candidate-relative `inv⁺[p]`'s word-model reduction would need
  meaningfully more work than `inv⁻[p]`'s, by analogy with
  `ThunkableSquare.tier⁺`'s longer proof chain relative to `tier⁻`'s.
  The agent found this overstated: evaluating the fiber condition at
  `t=(tt,τ̂)` (rather than blind symmetry with `inv⁻`'s `k=ε̂` evaluation)
  collapses `act-iso` to essentially the same one-line shape as
  `coact-iso`, via a single reused lemma (`far`, built from
  `BalancedWord.act-τ`). I confirmed this by hand-tracing `act-iso`
  directly — the warning was genuinely too pessimistic, not merely
  differently-solved.

**Gap against the newly-adopted [[spike-model-scope-discipline]]
rule:** this spike's closing section predates that rule (dispatched
before Lane stated it) and does not use the GENERAL/COUNTERMODEL/SHADOW
vocabulary. Read against it now: the word-model census entries are
COUNTERMODEL-grade (any model refutes a general claim); the pinning
results (`word.rb-contr`, `word.twists-inv`) and the circle results
(`circle.inv-all`, `circle.rb-not-contr`, `circle.both-not-contr`) are
all SHADOW-grade (`ob = ⊤` throughout, both models). Not retrofitted
into the file — flagging for Lane's call on whether to relabel it.

**Why:** the freeze-input gathering [[ribbon-tensorial-logic-goal]]
program continues — this spike was the direct follow-on to
[[spike-self-mediation-result]]'s open question (does one condition
subsume the conjunction its two halves needed separately).

**How to apply:** when a recognition-style condition is suspected of
subsuming a conjunction, check whether it does so by a genuine
contraction at EVERY relevant model, not just the one where it first
looks strongest — here (B) looked like the clean winner at the word
model (pins outright, no tier) but the circle model showed it merely
trades "excludes everything" for "selects a whole extra family," which
is a different and weaker property than contraction. A condition that
strictly dominates another pointwise (as B dominates A here) is not
automatically sufficient on its own — check the failure mode
(non-contraction) independently at each model rather than inferring it
from the dominance relation.

## grade-selector

_2026-08-03 SpikeGradeSelector result — the self-referential mediation clauses, stated candidate-relatively, do NOT select the generator along readback's orbit at the circle; readback's single cancellation condition already implies both clauses at every orbit point, because every clause word is degree-balanced (correction words restore degree, they never break it)_


`src/Test/SpikeGradeSelector.lagda.md` (checker-verified, `--cubical
--safe --no-guardedness`, 2026-08-03) tests whether the self-referential
mediation clauses of [[spike-self-mediation-result]], stated
candidate-relatively, supply the "grade-1 selector"
[[spike-candidate-generator-result]] found missing: readback alone
recognizes the whole subgroup a candidate generates at the circle
(every `(a, binv a)` on the orbit), not the generator itself. I
independently re-verified the delivered file (own `just check`, lint,
prose-lint, plus fully hand-unfolding the circle model's `⊛⁺`/`⊛⁻`
semantics myself and checking both endpoints of the two central path
constructions, `orbit.c₀`/`orbit.c₁`, against the literal clause
statements) rather than trusting the agent's self-report — this one
mattered more than usual, since it directly contradicted my own
hand-worked recon.

Key findings:

- **The clauses ARE statable at judgment level, with no composability
  tier — and this is the stronger reading, not a fallback.** `clauseʲ`
  builds `_⊛⁺_`/`_⊛⁻_` as composites of JUDGMENTS (not homs), via
  `coactʲ`/`actʲ` closing the term/coterm half at the candidate's own
  `var`/`covar` before any `reflect` is taken. This nests to arbitrary
  depth with no chosen representative required — resolving the sibling
  spike's stopping-rule worry: a positive-then-negative ("wild") word
  like `f⨾⁺(g⨾⁻h)` doesn't need a hom-level intermediate after all,
  because judgments compose directly; only comparing the result back
  to an EDGE requires representability, which the module never does
  away from the carrier's own framing.
- **At the carrier's own framing, the two forms agree — GENERAL,
  not SHADOW.** `carrier.to₀/to₁/from₀/from₁` show the
  judgment-level clause and `SpikeSelfMediation`'s edge-level clause
  carry each other whenever the candidate equals the carrier's actual
  twists, over ANY `virtual-graph` with stability and both
  composability tiers. This is the one GENERAL-grade result in the
  spike; everything else is SHADOW (one object) or COUNTERMODEL.
- **Word model: the impostor fails readback outright, and the clauses
  add nothing.** `word.impostor-no-rb` refutes `rb (ω̂,ε̂)` directly
  (readback would force `φW ω̂ ≡ ε̂`, contradicted since `φW ω̂`'s
  descriptor list is non-nil). Since readback already pins the word
  model completely (reusing `SpikeCandidateGenerator.word.rb-contr`),
  the clauses ride along for free (`word.contr`) — SHADOW-grade,
  consistent with the word model being where readback alone already
  settled everything.
- **Circle model: readback's cancellation alone forces BOTH clauses,
  at every orbit point — the decisive negative result.** For any `a`
  with `b = binv a` and `q : mult a b ≡ base`, `orbit.c₀`/`orbit.c₁`
  build the required paths using ONLY `mult-assoc`, `q`, and
  `mult-unit-r` (definitional at `base`) — no winding argument, no
  `loop`/`rot` machinery, and `a` is completely free. So
  `circle.rb→selects` shows readback implies both clauses everywhere,
  the conjunction's solution set equals readback's, and
  `circle.not-contr` (the same retract-onto-the-circle-contradicts-
  `loop-nontrivial` argument as the sibling spike) closes the route —
  COUNTERMODEL-grade, and one countermodel is enough to kill the
  general hope.
- **The reason, stated as clean arithmetic, not just a computation
  that happened to work out.** Read a candidate-relative word as a
  string in the two components: each edge letter contributes itself,
  each `⊛⁺` junction contributes one `a`, each `⊛⁻` junction one `b`.
  Define degree = (count of `a`) − (count of `b`). Both clauses are
  degree-balanced (`clause₀`: −1 against −1; `clause₁`: −1 against
  −1) — and this is not a coincidence of these two specific clauses:
  a correction word's entire purpose is to restore degree across a
  reassociation, so ANY clause built from mediation's correction-word
  mechanism will be degree-balanced by construction. Where readback
  holds, the two components are mutually inverse, so a degree-balanced
  equation is automatically an identity at every point of the orbit.
  **A genuine grade-1 selector needs a degree-UNBALANCED condition** —
  this names what property class would actually work, even though this
  spike doesn't build one.
- **My own recon's central algebraic claim was wrong, and the error is
  instructive.** I had substituted the orbit into
  `SpikeSelfMediation`'s EXISTING clauses, which use the carrier's
  GLOBAL `_⨾⁺_`/`_⨾⁻_` — and at the circle model, those cuts are
  UNCONDITIONALLY `mult f g` (`ThunkableSquare.circle.C⁺/C⁻`), reading
  no candidate or twist in the composition operation itself, only in
  the argument positions already substituted by `self`. This spike's
  `⊛⁺`/`⊛⁻` are different: they insert a FRESH candidate letter (`a`
  or `b`) at every single junction, not just at the positions `self`
  already substitutes. Conflating "candidate substituted into the
  twist argument slots" with "candidate-relative composition itself"
  is exactly the mistake — they produce different words, and my
  algebra (which used the former) landed on the opposite verdict from
  the correct one (which needed the latter). I confirmed this by hand
  before writing this memory: fully unfolding `⊛⁺`/`⊛⁻` at the circle
  model and re-deriving both `c₀`'s and `c₁`'s endpoints independently
  reproduces the module's own claims exactly.
- **A checker-hang variant worth knowing about, distinct from
  [[implicits-under-matching-heads]].** Elaborating `is-prop (selects
  Tier.word.BW q)` with unsolved metas hung the checker for over 25
  minutes: the metas forced `clause₀`/`clause₁` to unfold through
  `BW`'s `reflect` into nested `comp`/`onset`/`tabulate` on NEUTRAL
  descriptors (the word model's normalize-by-evaluation composition,
  not a pattern-matching head like `mult`/`rot`). Stating the same
  lemma with both path endpoints written out explicitly, inside an
  abstract-carrier module rather than instantiated at the concrete
  word model, made it instant. The existing memory is scoped to
  H-space/Circle models specifically (`mult`/`rot` blocking under
  implicit points); this is a different concrete model (`BalancedWord`)
  and a different mechanism (expensive definitional unfolding forced
  by metas, not a permanently-blocked Miller-pattern constraint) —
  same SYMPTOM (checker looks hung), different cause. Worth a
  dedicated memory rather than folding into the existing one.

**Why:** direct follow-on to [[spike-candidate-generator-result]]'s
open question — whether the self-referential clauses supply the
missing "grade-1 selector" readback alone can't provide. Part of the
[[ribbon-tensorial-logic-goal]] freeze-input gathering.

**How to apply:** when substituting a candidate pair into a
recognition-style condition at a wild model, check carefully whether
the candidate enters ONLY at designated argument positions (leaving
the ambient composition operation itself candidate-independent) or
whether the composition operation itself is being made
candidate-relative (inserting the candidate at every junction). These
produce genuinely different words even when the "obvious" substitution
looks the same on paper, and conflating them is easy to do silently —
verify by fully unfolding the composition at the concrete model before
trusting an algebraic reduction, rather than assuming a substituted
version of an existing clause is the same as a from-scratch
candidate-relative restatement of it. Separately: when a spike claims
a clause "selects" or "pins," check whether the underlying word is
degree-balanced in whatever grading the ambient group provides —
mediation's correction-word mechanism specifically can never produce
an unbalanced (hence selecting) condition, which is a reusable
negative result, not just a fact about this one spike.
