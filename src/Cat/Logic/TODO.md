# Cat.Logic — open items

State as of 2026-07-27. `src/Cat` typechecks, 62 modules. `src/Test`
typechecks apart from the two `Mag` spikes, which the `Mag.Type`
rewrite broke. Lint is clean.

Committed at `b979bb6` on branch `cat-logic-polarity`, which is the
rename and the docs together. Two commits sit on top of it: `618184e`
adds the agent suite, and `7dc65e8` applies the STE register across
the docs and adds a prose check to `bin/lint`. The tree is otherwise
clean; `src/Mag/` and four `Test` spikes are still untracked.

Prose is now gated. `just lint prose` reports 509 issues across the
repository and none in `src/Cat/Logic` or `src/Mag`. The `writing`
skill is the normative statement and
`docs/guidelines/prose-and-comments.md` states the scope. Keep new
prose in that register.

## Done

The rename pass is applied.

- `is-unital±` → `is-invertible±`, with `is-invertible-is-prop`,
  `op-invertible±`, and the `is-deductive-system` field renamed
  `invertible`.
- Composition register flipped: `composite±`, `inj±`,
  `is-composable±`, `contr±`, `⨾±`, `assoc±`, `unitl`/`unitr`,
  `tri±`, `collapse±`, `pentagon±`, `pair±`, `C±`,
  `push-is-composite±`. Framing register untouched.
- `mixed-leading` → `thunkable`, `mixed-trailing` → `linear`.
- Consumers fixed: `Test/FramedGroup`, `Test/TwistFidelity`,
  `Test/SpikeFramedCut`, `Test/SpikeNeutralUnit`.
- The three-register naming rule is written into `Cat.Logic.Type`,
  beside the twist fields.

Checks that landed as predicted: `mixed-assoc` is now
`(f ⨾⁻ g) ⨾⁺ h ≡ f ⨾⁻ (g ⨾⁺ h)` — Mangel's valid word — and
`unitr⁺ : f ⨾⁺ twist⁺ y ≡ f`, `unitl⁻ : twist⁻ x ⨾⁻ g ≡ g` now agree
with `Test/FramedInterchange` on the nose.

Module prose in `Base`, `Display` and `Graph` has been reread and
rewritten against the new labels. `Base`'s header no longer claims the
twists are mutually inverse — it says each has a uniquely determined
one-sided inverse, and names `absorption` as where the mutual claim
lives. `push-is-composite±` in `Display` were relabelled so each matches
the composite it produces.

`docs/deductive-systems/` and `docs/gloss.md` are reconciled.
`unitality.md` is now `invertibility.md`, retitled and relinked from
`README.md` and `framing.md`. `mediation.md` needed no change: after the
swap its pending-read / pending-write sentences and both `collapse±`
hypotheses already read correctly. The two `notes/2026-07-25-*` files
are dated records, so they carry a relabelling banner rather than a
rewrite.

### Still to do from the pass

Nothing. The remaining work is the `Mag` rebuild against
`src/Mag/TODO.md`, and the fresh briefing block for the sibling agent.

## Settled this session

1. **The unit tier is misnamed.** Read through the string,
   `coact-π e ≡ snd` is `t⁻ · e · k ≡ k`, i.e. `t⁻ · e = 1`; and
   `act-π e ≡ snd` is `e · t⁺ = 1`. So the two tiers say *`twist⁻`
   has a unique right inverse* and *`twist⁺` has a unique left
   inverse* — invertibility of the framing, not unitality. The name
   is a holdover from the one-`rx` reflexive-graph formulation.
   Rename to `is-invertible⁻` / `is-invertible⁺`, record
   `is-invertible`.

2. **Form B, and position (C).** The tier stays the `snd`-target
   form. The cancellation (`pin ∙ K`, equivalently `t⁻ · t⁺ = 1`,
   equivalently "the twists are mutually inverse") is **not** a
   field of `virtual-graph` and **not** a tier — it is structure in a
   ribbon layer above the deductive system, which is where the
   literature puts a twist: a balanced category is a braided one
   *equipped with* θ. `virtual-graph` and `is-deductive-system` stay
   as they are, all-property and propositional.

3. **The handedness labels on the towers are backwards** relative to
   the duploid dictionary, and must be swapped. Names and docs only —
   the operations are unchanged and no proof moves.

4. **`mixed-leading` / `mixed-trailing` are Mangel's thunkable and
   linear** — the universal closures of the one failing mixed word at
   a fixed leading/trailing edge, which is his definition. Align the
   naming. Note the prefix rule: neither is a proposition, so no
   `is-`.

## The handedness swap — scope

`Cat.Logic.Base` currently has `composite⁻` carrying the `var`
junction (hence `twist⁻`) and `composite⁺` carrying `covar` (hence
`twist⁺`). `Mag` and `Test.FramedInterchange` have it the other way,
and that is the one the literature selects: aligning the provable
mixed word with Mangel's valid word forces

> ⁺ = the `twist⁻`-carrying junction (CBV, value-demanding)
> ⁻ = the `twist⁺`-carrying junction (CBN, "frozen")

So `Cat.Logic` moves and `Mag` does not; afterwards both read the
same way.

Identifiers affected: `composite±`, `inj±`, `is-composable±`,
`cell±`, the `op-*` lemmas, and whatever `Cat/Logic/Display.lagda.md`,
`Cat/Logic/Graph.lagda.md`, `Test/FramedGroup.lagda.md` and
`Test/TwistFidelity.lagda.md` inherit.

Docs affected: `actions.md` and `towers.md`, whose pending-read /
pending-write sentences swap with the names — landing on ⁺ = future
and ⁻ = buffer, which is the CBV/CBN alignment.

## Docs reconciliation

- `Cat.Logic.Base`'s header, `docs/deductive-systems/README.md`,
  `framing.md`, `towers.md` still describe the form-A tier. Under the
  ribbon layer they are describing the balanced layer, not the base
  notion — relocate rather than rewrite.
- `invertibility.md` and `Cat.Logic.Base`'s mid-file prose already
  describe form B; they need the rename only.
- **Interchange is the ultra-thin / involutive line, not the cyclic
  line.** It is `θ⊥² = id`; cyclic is `θ⊥ = id` and is strictly
  stronger. Correct wherever glossed.
- **Twist locus.** Melliès' dialogical twist is one automorphism of
  the pole, unique by Yoneda; ours is a per-object pair, i.e. the
  balanced `θₓ`/`θₓ⁻¹`. Keep the two distinct in prose; they meet
  only at the pole.
- **Twists replacing identities has no source.** Phrase per
  `docs/provenance.md` as "not aware of a prior unit-free
  formulation; searched the vendored sources", naming them.
- **Do not call the framed carrier a duploid**, nor the towers its
  subcategories. A duploid is a unital magmoid — one two-sided
  identity per object — so per-hand one-sided unitality sits strictly
  below it. The nearest duploid *phenomenon* is `ω_X`; say
  "analogous", never "corresponds".

## Open: spike form B + (B) in full before changing the definition

Position **(B)** is to post `twist⁻` only and extract `twist⁺` as the
`⁻` tier's centre — the tier mentions `coact-π`, hence `var`, hence
`twist⁻` alone, so it is stateable before `twist⁺` exists.
`Test/ExtractedTwist.lagda.md` has the shape and shows the coterm-side
absorption and the positive right unit law falling out with no
readback and one fewer structure field.

**The case for it.** `virtual-graph` returns to a single reflexivity
datum, so the carrier for the category form and for the
deductive-system form converge; the difference between the theories
becomes the *flavour* of that reflexivity edge — whether it is a
trivial or a non-trivial isomorphism.

**The hesitation.** How much of the present form's symmetry is lost.
`opⱽ` is currently definitional on the carrier; under (B) the carrier
is asymmetric, so `op` moves up to carrier-plus-`⁻`-tier, and its
involutivity requires the opposite's extracted twist to be the
original's posited one.

**The deciding lemma.** Is `act-π (twist⁻ x) ≡ snd` derivable? With
readback and `mixed-assoc` it reduces exactly to right-cancellability
of `_⨾⁻ twist⁺` (`Test/FramedInterchange.lagda.md`,
`cancel⁺-from-cancellable`); nothing in readback or the cuts supplies
that. **The same lemma decides `op`-involutivity under (B).**

Do not change the definition until form B + (B) is worked out
entirely. Likely its own session.

## Resources

- `resources/munch-maccagnoni-duploids/` — vendored 2026-07-27,
  committed at `0cf05bf`, hash verified. **PROVISIONAL, not audited**,
  so it supports no load-bearing citation yet. The duploid dictionary
  above leans on it and on `mangel-classical-notions`, which is also
  unaudited. Both need statement audits before any of this reaches the
  ledger. Nothing in the tree cites either yet, and nothing should
  until the audits are run.
- Worth vendoring: Melliès, *Asynchronous Games 3*. It is the only
  place the future/buffer gloss could be source-checked at all —
  *future*, *buffer*, and any treatment of asynchrony, buffering,
  scheduling or delay appear nowhere in the six Melliès/Mangel
  sources currently on the shelf.
- What the gloss does shadow, and can be honestly re-anchored to, is
  Mangel's order-of-evaluation semantics: CBN parks a **"frozen"**
  expression (buffer-like), CBV demands a value first (future-like),
  and that attaches to the two *compositions*, not to the twists.
- The sourced side-assignment is term = proof/program side, coterm =
  counter-proof/stack side. `framing.md`'s "a covariable is a mailbox
  you enqueue into" is on the sourced side and stands.

## Also pending

A fresh briefing block for the sibling agent, written after the
renames land, so the narrative and the identifiers change together.
