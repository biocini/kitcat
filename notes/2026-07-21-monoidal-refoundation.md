# Checkpoint — 2026-07-21 — the monoidal refoundation

State of the mini-programme opened by
`notes/2026-07-21-unpinned-spine-brief.md`, at the close of its
first session. Everything below is machine-checked under `--safe`;
instance files use full `--cubical` per the Phase 0 ruling.

## Rulings landed (Lane, 2026-07-21)

1. **The record carries two interchange fields.** `ι⁺ ι⁻ :
   is-rep A → is-rep B → A ▿₀ B ≡ A ▵₀ B`, no axiom relating them;
   the one-field-plus-loop form is a constructor
   (`Cat.Monoidal.Legacy.Twist.twist`), not the record. The freeze
   on the final field shape still awaits agreement of the circle,
   tangle, and crossed G-set instances, per the brief's guardrail.
2. **Layering closed by endpoint types.** Both fields preserve
   factor order, so the record cannot express transposition; the
   braid remains a separate layer above, and the balancing is
   expected as a theorem about how the two layers interact.
3. **The balanced-overlay approach is superseded.** The twist
   candidate is derived (the discrepancy of the per-field unitors);
   what survives of the overlay is only the interaction question,
   deferred to the first braided instance.
4. **Archive in place, redevelop the namespace.** Executed: the
   prior suite moved wholesale to `Cat.Monoidal.Legacy` (paths
   renamed, every module re-checked); `Cat.Monoidal` redeveloped.

Standing diction norm (global CLAUDE.md): session coinages do not
graduate into deliverables; landed names come from the mathematics.

## The tree

- **`Cat.Monoidal`** — the context calculus at both grades;
  `monoidal-axioms₀` (two interchange fields, pull-fiber
  contractibility as the sole contractibility axiom, readback; `ω`
  derived); `theory₀` split into cells consuming no interchange
  path / `over-interchange` (comparisons over an arbitrary one;
  the compatibility cell is `slide`, `⊗₀-coh→∙` holds by `refl`;
  spine over any path a theorem) / the representability calculus
  (choice-invariance certified by `image-contr-invariant`) /
  `unitors` / the comparison boundary (`absorb-coh` per path,
  `unitr-agreement`/`unitl-agreement`); `monoidal-axioms₁` (the
  displaced record: displaced embedding, one displaced interchange
  field over each level-0 field, displaced pull fiber as `⊗₁-wit`
  at the level-0 pull centers, displaced readback, enrichment law);
  `theory₁` with `over-interchange₁` (displaced spine over any
  interchange pair via `Σ-contr-contr` + `SinglP-contr` — no new
  Kan cells; `spine-tail` is the one-dimensional case of the
  singleton over a line of path types); the bundle `monoidal`.
- **`Cat.Monoidal.Properties`** — `unpin`/`pin⁺`/`pin⁻` and
  `axioms₀-compare : Legacy.monoidal-axioms₀ C ≃ (Σ M ,
  interchange-agree M)`: the archived presentation is the new
  record with pointwise agreement of its two fields. Round trips
  are record lines with propositional fills; no Kan filling.
- **`Cat.Monoidal.Legacy`(+ eight submodules)** — the archive,
  checked under its new paths. Downstream theory (Bifunctor, Braid,
  Hexagon, Coherence, Iso, the old Properties, Indiscrete, Twist)
  lives here until redeveloped.
- **`HData.Circle`** — Type/Base/Mult/Properties under the
  Nat-format aggregator: `winding-equiv : (base ≡ base) ≃ Int`;
  `rot`, `mult`, unit laws, translation equivalences;
  `Circle-is-groupoid`; `self-path-equiv : ((x : Circle) → x ≡ x)
  ≃ (base ≡ base)` (inverse `conj`, with `conj loop ≡ rot` by
  `refl`); `rot-mult`, `mult-assoc`, `mult-l-cancel`,
  `mult-faithful`; nontriviality (`loop-nontrivial`,
  `rot-nontrivial`).
- **`Test/CircleTensor`** — the first inhabitant:
  `Emb x (l , r) = mult l (mult x r)` on `∞-groupoid Circle`;
  pull-fiber contractibility by currying, left-translation
  cancellation, one transport along `mult-assoc`, first-slot
  faithfulness, and the path singleton; `ι⁺` the plain
  reassociation, `ι⁻` its composite with the pointwise rotation;
  `routes-differ` refutes their agreement through `winding`.

## The load-bearing facts, for cold re-entry

Spine-contractibility over a fixed interchange path and pull-fiber
contractibility are interderivable, so the archived axioms are the
new ones plus a welded choice; the choice is invisible to the
axioms (`Legacy.Twist.Mω`) but detectable in derived cells, and
demanding absorption coherence across a deformation kills it
(`twist-reduces-to-omega`) — hence comparisons are stated one
interchange path at a time. On set-level carriers the agreement
type is automatically inhabited and the presentations coincide:
the classical monoidal bottom rung is the 0-truncated shadow of
this record.

## Next steps

1. **Braided instance** (Ω²-flavored carrier). Decides whether the
   balancing is a field or a theorem by fiber projection, and
   tests the conjecture that the unitor agreement types are
   equivalent to `ω` vanishing at unit flanks (the `θ I ≡ refl`
   normalization in derived form, cf. `Legacy.Twist`'s `Hω`).
2. **Free rack, design session before code** (`HData.Rack`; the
   current `Ra` stub is hole-ridden and posits its coherence as
   constructors). Target: present the free rack by normal forms —
   a generator with its crossing history, classically `A × F(A)` —
   with the operation extracted from contractible fibers and
   self-distributivity plus its tower derived; the one-generator
   case should have components `Int` through the circle machinery
   (`conj`/`rot` realize the shift). Slots into the evidence phase
   beside the braided instance as the initial crossing algebra;
   also feeds the record-freeze guardrail.
3. **Component count of the interchange-path space** for the
   circle instance (`≃ Int`). Kernel landed (`self-path-equiv`);
   what remains is the classification of function-space paths over
   the squared context, by iterating the same evaluation argument.
4. **Downstream redevelopment** (Bifunctor, Braid, Hexagon,
   Coherence, Iso over the new namespace), pulled by need — the
   archive serves consumers meanwhile, and `pin⁺` bridges.
5. **Promotions**: `subst-∙`, `transport-inv` →
   `Core.Transport.Properties`; `Int` discreteness ( `DecEq-Int`,
   instance, set-ness) → `Core.Data.Int` mirroring Nat's layout;
   `ua-unglue` → `Core.Univalence`; `ap-retr` → `Core.Path`
   candidate; check `Core.Data.Dec` for an existing `dec-map`.
6. **Conventions and chores**: fix which field carries the
   deformation in instances before any certificate cites a sign
   (as minted, the circle's `ω` winds negative at the detection
   point); `All.lagda.md` path updates stay in the deferred-chores
   batch; the stale `Test/` probes (`Probe`, `Probe2`,
   `ProductSpike`, `Scratch`, timestamped files) predate the
   refoundation; no profiling pass has been run on the new
   namespace yet.

## Consumers to keep named

The ∂LB certification program's Phase 2 headline (the model where
an identity type carries `Int`) reads off item 3; the kernel's
two-tier conversion boundary reads the locus where the two
interchange fields agree; the graded cut elimination reads the
displaced spine over each interchange pair, now supplied by
`theory₁.over-interchange₁` with no per-grade axioms.
