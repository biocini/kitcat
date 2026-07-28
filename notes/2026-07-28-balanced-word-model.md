# 2026-07-28: the free balanced word model

Objective at open: line 9 item 1 at (D′) strength — the word
model of the bare framed point, as the oracle for the (D′)
associates profile. The session also executed the Test spike-zero
distribution, the Bb archive process, and two tooling rulings.

## What was done

1. **The line 9 grammar corrected.** The pre-cut sketch in
   `src/Cat/Logic/TODO.md` (centre absorptions as rewrites) was
   replaced with the post-cut grammar: `assoc⁺`, `assoc⁻`,
   `mixed-assoc`, the four unit laws at each hand's own twist,
   readback as the transmission relation. Generating data decided
   (Lane): the bare framed point first.
2. **The word problem solved empirically before formalizing.**
   Bounded congruence closure over all words to six leaves:
   classes double per leaf (2, 2, 4, 8, 16, 32). Words interpret
   faithfully into weakly monotone eventual translations of ℕ
   (`t⁺ ↦ id`, `t⁻ ↦ suc`, `⨾⁺` composition, `⨾⁻` through
   `φ f 0 = 0; φ f (n+1) = f n`): 64 classes, 64 distinct
   canonical descriptors, zero clashes, and every small canonical
   descriptor reached. Scripts and results vendored at
   `outputs/.notes/balanced-word-model-*`.
3. **`Test.SpikeBalancedWord` delivered, 948 lines, green.**
   Normal forms as descriptors (no quotient), both cuts
   admissible, decidable equality, the carrier a set, the full
   (D′) instance (`virtual-graph` with readback, the two-field
   predicate, stability by `stable-from-hom-sets`), and the
   measurements. Implementation brief at
   `outputs/.plans/balanced-word-model.md`.
4. **Test distributed under spike zero** (policy vendored at
   `src/Test/CLAUDE.md`): twelve chosen-edge spikes →
   `Bb.NaiveVirtualGraph` (Base + Gist, AnchorPin lemmas ported);
   twelve stratum witnesses →
   `Bb.CatsWithExplicitInterchange.Gist`, with the gloss T21
   citation re-pointed to checked code; four removals with
   grounds (CohTest: dead import; SpikeFramedVirtual: preserved
   in `Bb.WeakDeductiveSystem.Base`; ListTest: its definitional
   claim is false; PathTest: subsumed by
   `Core.Data.List.Properties` `nil-path-contr`); three probes
   converted to literate form and gated.
5. **The archive grew and got its process.** `Cat.Depreciated`
   (49 modules) → `Bb.CatsWithExplicitInterchange`; the Magmoid
   suite extracted to `Bb.UnitalMagmoids` after an entanglement
   check came back clean; `src/Bb/CLAUDE.md` states the process
   (README with provenance, per-tree CHANGELOG, `Bb.index`);
   READMEs and CHANGELOGs in all six trees; the stale `CatData`
   citation in `docs/composite-rx-refactor/stage-4-cat-rebuild.md`
   resolved — it was a planning name never adopted; the leaf was
   always `Magmoid`.
6. **Tooling rulings executed.** Width is 100 everywhere (prose
   raised from 72; `bin/lint`, `docs/guidelines/api-surface.md`);
   `just check-tree` sweeps every `.lagda*` form, which surfaced
   the broken probes the old `.lagda.md`-only glob hid.

## Strongest findings and decisions

- **The (D′) profile gate closes on the refutation side.**
  `associates t⁻ t⁺ t⁺` fails in the word model: left bracketing
  `t⁺`, right bracketing the descriptor `([1], 1)`. Generic
  `associates` is underivable at (D′); the profile is exactly
  pre-duploid plus `mixed-assoc`, the four unit laws, and the
  twist-flanked family. The countermodel that finite reader
  carriers could not supply is the free point itself. Corollary
  bound for line 3: `t⁻` is not thunkable, `t⁺` is not linear.
- **The winding conjecture holds.** The endo-homs carry a
  ℤ-grade, the eventual-translation shift: additive over `⨾⁺`,
  predecessor of the sum over `⨾⁻`, every grade inhabited, the
  double twist the `+1` generator. The obstruction to
  `associates` is one-sided invertibility on the nose:
  `(t⁺ ⨾⁻ t⁺) ⨾⁺ t⁻ ≡ t⁺` by `refl`, the reverse composite not
  `t⁺` — the bicyclic signature, syntactically.
- **The NbE reading became the construction.** Readback's
  doctrine gloss (reification retracts evaluation) is the word
  model's architecture: evaluation into `ℕ → ℕ`, laws by
  injectivity of evaluation, cuts as admissible functions per the
  seam's cut-freeness line.
- Failed strategy, with reason: two hand-derived normal-form
  grammars died on critical pairs — a one-directional
  `mixed-assoc` orientation leaves `t⁺ ⨾⁻ (t⁻ ⨾⁺ w)` reducible
  but unreduced, and the φ-atom grammar missed
  `δ · φ(τ·y) = φ(y)`. The congruence data, not inspection,
  chose the carrier.
- Failed strategy, with reason: delegated builds stalled twice —
  an unbudgeted reading phase produced no code, and a
  transcript-resume behaved as a cold start. What worked: the
  brief plus the vendored empirical artifacts as mandatory
  inputs, a hard reading budget, green checkpoints per stage,
  and bounded checker timeouts.
- Process finding: the session scratchpad is shared with
  subagents and was clobbered mid-session; the empirical scripts
  survived only because they were vendored to `outputs/.notes`
  at creation time.
- Archive findings en route: `reference/february26-ternary-cat/`
  is the true pre-archival Magmoid snapshot, and its `Prod`
  carries a working embedding proof the archived `Prod` disables;
  `reference/magmoid-formulation/Data` is the earlier
  composition-primitive fork point, pre-Yoneda, distinct from
  the archive.

## Verification state

- verified: `Test.SpikeBalancedWord` by recorded
  `just check Test.SpikeBalancedWord` (2026-07-28, exit 0, zero
  warnings; the lead re-ran it independently of the builder).
  `src/Bb` 98 of 98 by `just check-tree src/Bb`. `src/Test` 9 of
  9. `Bb.index` green. `just lint changed` clean at the
  100-column width. Prose gates ≤ 2.0 on every touched `docs/`
  file. Obligation inventory for everything added today: zero
  holes, zero postulates, zero unsafe flags.
- verified, pre-existing failure: the whole-tree
  `just check-tree` stands at 319 of 323; the four failures are
  `Data.Thin.{Category,Cover,Properties,Separated}` with open
  interaction metas, untouched today, the known deferred chore —
  visible now because the whole-tree sweep runs where recent
  sessions checked per directory.
- inferred: the descriptor model is the free balanced point —
  empirically certified through six leaves (64/64, reachability
  complete); formal initiality is line 9 items 2 and 3. The
  refutation and the (D′) instance need no freeness, so the
  profile verdict is unconditional.
- unverified: `t⁺` thunkable and `t⁻` linear as general (D′)
  theorems (two-line unit-law computations, not yet Base
  lemmas); the portability of the february26 `Prod` embedding
  proof into the archive.
- Commits: none. The entire session sits uncommitted on
  `cat-logic-polarity`.

## Open questions and risks

1. Line 9 items 2 and 3: morphisms of systems, then the free
   system and initiality — the coherence theorem as an NbE
   result, now with its concrete target.
2. `Test.SpikeBalancedWord` is a spike-zero candidate for
   promotion to `Cat.Logic.Gist` once its results enter the
   ledger.
3. `docs/gloss.md` still lacks entries for the record-cut
   theorems and for today's profile verdict. Ledger chore.
4. The `Data.Thin` four remain red with open metas; deferred.
5. The february26 `Prod` proof reclamation, and the Bb candidacy
   of `reference/magmoid-formulation/Data`, await rulings.
6. The two duploid source audits remain overdue.

## Next steps

Line 9 item 2 (morphisms), then the seam's indiscernibility
statement, with the `Bb.VgCategoryShape` successor program
behind them. The word model is the fixed point of reference for
all three.

## Artifacts

- Library: `src/Test/SpikeBalancedWord.lagda.md`;
  `src/Bb/{NaiveVirtualGraph,UnitalMagmoids}/` (new trees);
  `src/Bb/CatsWithExplicitInterchange/` (moved tree + `Gist`);
  `src/Bb/CLAUDE.md`, `src/Bb/index.lagda.md`, per-tree READMEs
  and CHANGELOGs; `src/Test/CLAUDE.md`.
- Records: `src/Cat/Logic/TODO.md` (grammar correction, the
  settled profile block, header refresh); `docs/gloss.md` (T21
  re-point); `docs/composite-rx-refactor/*` (citation
  re-points); `docs/guidelines/{api-surface,module-anatomy}.md`
  (width ruling).
- Working artifacts: `outputs/.plans/balanced-word-model.md`
  (the brief); `outputs/.notes/balanced-word-model-*` (the
  empirical certification: four scripts and the results note).
- Tooling: `bin/lint` (prose width 100), `justfile`
  (`check-tree` sweeps `.lagda*`).
