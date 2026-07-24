# Session log — 2026-07-20 — the composition-notation audit

Pass 1 of the formatting-regulation chore reformats the coherence
layer for readability **without changing any proof term** — short
declarations collapse to one line, must-break signatures drop the
name off the type's line so the whole type fits after the colon
(the "colon-down" form), redundant parens around bare identifiers
are stripped. Proof terms stay byte-identical, so the module
re-checks cold with no shift, and the displaced layer that
consumes the level-0 lemmas keeps typechecking against unchanged
base paths.

Term-*changing* conversions are deliberately held out of Pass 1:

- a 3-fold `∙`-chain rewritten to native ternary `pcom`;
- a flat >3-fold chain rewritten to `Chain` (`begin … ≡⟨ ⟩ … ∎`)
  reasoning, which also appends a trailing `∙ refl` via `_∎`.

Both change the term, and a higher path can depend on the exact
binary-concatenated structure of a level-0 chain — the displaced
layer consumes the level-0 step-lemmas as `Fam (Q.step-l₁ m)` and
`comp-pathp₂ Fam Q.step-l₁ Q.step-l₂ …` base paths, so rewriting
`step-l₁`'s body shifts the type its level-1 witness must inhabit.

Ruling (Lane): the 3→`pcom` question is subtle — do not
auto-rewrite. `Chain` adoption qualifies **primarily for the
outermost concatenation** of a lemma; nested bracketings are
broken into named sub-lemmas first, each rendered with path
notation for its own top-level concatenation. This log records
every candidate so Pass 2 analyses them one by one, converting
where a native ternary formulation exists (usually the more
efficient form) and reworking the dependent higher-path proof in
the same step.

## The composition ladder (refined norm)

| paths | form |
| --- | --- |
| 2 | direct binary `∙` |
| 3 | ternary `pcom p q r` — **new work only**; existing 3-chains logged here, never auto-rewritten |
| >3, flat, outermost | `Chain` reasoning, profile-gated (the trailing `∙ refl` is a term change) |
| >3, nested | break inner brackets into named sub-lemmas; each sub-lemma's top level uses the row above |

## Triage tag

A candidate is **depended-upon** when its name — or that of its
enclosing definition — appears in a higher-path position (a
`PathP` / `Fam` / `comp-pathp₂` base line), so converting it
shifts a type the displaced layer must inhabit. Independent
chains convert freely in Pass 2; depended-upon ones need their
consumer reworked in the same step.

## Candidates — `Cat.Monoidal.Hexagon`, level-0 modules

`hexagon-r₀`:

| site | form | candidate | depended-upon |
| --- | --- | --- | --- |
| `κ` (in `μ`) | 3-fold `∙` body | `pcom` | yes — `μ .snd`; `μ` feeds `⊗₁-wit-∙` at `bot̂` |
| `step-l₁` type RHS | 3-fold `∙` interface | `pcom` | yes — `Fam (Q.step-l₁ m)` |
| `step-l₂` type (both sides) | 3-fold `∙` interface | `pcom` | yes — `Fam (Q.step-l₂ m)` |
| `step-r₂` body | nested 3-deep conjugation | sub-lemma decomposition, then `pcom`/`Chain` per level | yes — `Fam (Q.step-r₂ m)` |
| `⊗₀-hexagon-r` type (both sides) + body | 3-fold `∙` | `pcom` | yes — object hexagon; consumed by `⊗₁-hexagon-r` and the derived field |

`hexagon-l₀`: the slot-mirror of each row above (`κ`, `step-l₁`,
`step-l₂`, `step-r₂` nested body, `⊗₀-hexagon-l`), same forms and
tags.

Non-candidates (left as-is): `sl`, `sr`, `ℓt`, `ℓc`, `rt₁`–`rt₃`,
`rc` — all 2-fold `∙`; the σ-lines — single `ap`/`refl`.

## Pass-1 formatting status

Complete and cold-checking clean (term-preserving throughout):

- `Cat.Monoidal.Hexagon` — level-0 **and** level-1: 154 atom-parens
  stripped, all signatures to their tightest tier, bodies compacted;
  net −28 lines.
- `Cat.Monoidal.Coherence` — 2 sig pull-ups, 4 body compactions
  (`ι-mult-r₀/l₀`, `assoc●₀/₁-nrm`); net −6 lines. No atom-parens.
- `Cat.Monoidal.Bifunctor` — 1 sig pull-up, 10 body compactions;
  net −11 lines. No atom-parens.

## Not yet done

- **Pass 2** (this log): the deliberate `pcom`/`Chain` conversions.
  Hexagon's candidates are tabled above; the systematic
  dependence-tagged enumeration for Coherence and Bifunctor is the
  opening step of Pass 2 (both carry the same displaced-layer
  `comp-pathp₂` base chains, so most level-0 chains there are
  depended-upon too).
- The rest of live `Cat.*` — Pass-1 formatting on the same rule.
- `Core.*` — deferred to a later conversation.
- Codify the composition ladder and the three-tier signature rule
  into `docs/styleguide.md` once the conventions have settled.
