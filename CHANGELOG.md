# Changelog — kitcat lab notebook

The chronological record of what changed in this repository: what
landed, what was verified, what failed, and what it superseded.
**Newest entry first.**

- **To resume work**, read the latest session log in
  [`notes/session-logs/`](notes/session-logs/) — that is where
  current state, open questions, and next steps live.
- **To understand what happened**, read down this file.
- Standing targets and their gates: [`docs/roadmap.md`](docs/roadmap.md).

This is a lab notebook, not release notes: entries are dated,
concise, and honest about verification status (`verified` /
`unverified` / `blocked` / `inferred`).

---

## 2026-07-13 (second session) — pipeline reliability and the audited shelf

Object: the resources/ pipeline and the research suite, taken from
"designed" to "certified and reliability-hardened". No Agda changed.

**Landed.** The content-digest layer (statement-level digests in the
source's own terms; Rijke digested at full Part II depth by a
22-lecture fan-out) and custody mechanics (`just resources-verify`:
hashes, entry standing, consumed-by; fetch URLs and `.pdftext`
provenance recorded per entry; the chiralities extraction normalized
onto the flake-pinned poppler). The directory's doctrine encoded:
reference shelf + citation store, **information flows from resources
out, never the reverse**. Then an 8-reviewer certification — four
against the original feynman suite at `~/feynman-skills`, four
internal — certified the port **faithful** (13/13 prompt pairs, 4/4
architecture axes, zero DEFECT) and the subagent system **correctly
implemented**, and its findings were applied: the contract's new
**Layer scope** section (the source's fight-for-its-life discipline
the port had dropped, with retroactive records for `/prove` and
`/hott`), the verify protocol promoted into the contract with 15
prompts deduplicated to name-and-defer, the drifted `[unvetted]`
restatement (the review's one FATAL) deleted everywhere with a lint
canary against recurrence, skill handoffs wired, and mechanize's
audit legs closed.

**The ruling that reframed the layer (Lane):** the pipeline must be
reliable whether or not Lane reviews it. The load-bearing gate for
ingested knowledge is now the **human-free statement audit**
(identity hash-verified + digests adversarially verified against the
source, fresh-quote evidence required, records hash-bound);
ratification/veto is Lane's self-initiated discretion, never a
pipeline queue; and mathematical claims stay CONJECTURED until
machine-checked, whoever approved what. First exercise: all six
entries audited (rijke 152/155 CONFIRMED, shelf-wide 175/183), eight
corrections applied — including two dropped "locally small"
hypotheses on the mechanization target and our own memo's `†`
notation contaminating a source entry — confirming re-pass clean,
source errata recorded. `docs/gloss.md` T16 re-attributed to the
source's `(−)op` and upgraded 📐⚠️ → 📐 under the new audit-keyed
rule.

`verified`: authoring lint (with canary), resources-verify (7 hashes,
0 FATAL; all six entries audited — load-bearing capable),
unidirectional sweep, sync, shellcheck. `superseded`: the
PROVISIONAL blocking rule ("no load-bearing citation on a
PROVISIONAL entry") and the ratification queue — replaced by
audit-as-gate with discretion open. Commits `af73f50`, `e1d9f62`.
Session log:
[`notes/session-logs/2026-07-13-reliability-audited-shelf.md`](notes/session-logs/2026-07-13-reliability-audited-shelf.md).

## 2026-07-13 — the fresh review and the shim/prompt surface split

Object: the hardened context layer, reviewed fresh and then
restructured. No Agda changed.

**Landed.** A fresh-eyes adversarial review (an 8-reviewer workflow
with per-finding adversarial verification against rulings R1–R13)
produced 58 verified findings; all 5 FATAL, 18 MAJOR, and the
relevant MINORs were fixed — R7 Rijke propagation, R2 ingest wiring,
R6 writer dispatch, the writer↔verifier citation contradiction, the
marker-shedding-on-ratification policy, a `bin/lint` soundness fix,
and a new `just lint changed` non-regression width gate for the
in-flight tree. The flake was fixed (`poppler_utils` → `poppler-utils`
would have broken it at HEAD) and pinned with `flake.lock` (agda
2.8.0 + curl/git/gnutar/perl). Six `resources/` entries were brought
to the R11 bar by delegated `ingest` runs (`petrakis-dep-arrows`
re-ingested as LaTeX-source canonical; a `mellies-dialogue-
chiralities` duplicate removed; line-anchored maps added).

Then the **workflow surface was re-expressed as the shim/prompt
split**: full workflow bodies are masters at `.agents/prompts/`, small
auto-trigger shims at `.agents/skills/kitcat/`, Claude Code reaches
them via two directory symlinks, pi reads `.agents/` directly, and
`.pi/prompts` + `.feynman/` were removed. `.agents/CLAUDE.md` was
established as the context-layer source of truth (the repo-user /
agent-facing division of labor made explicit) and now carries the
durable R1–R13 design decisions (R10 externalization).

**Verified.** authoring lint, `just sync`, the flake devshell build
(agda 2.8.0 + all layer tools), symlink integrity, tree independence
(reworded free of the external codename, re-checked), and the 18↔18
shim/prompt pairing — all green. `verified`: those checks.
`unverified`: `just check-all` under the flake was run once during the
shakedown (green) but no Agda changed since. `blocked`: the review's
verify phase hit the monthly spend limit once (Fable 5) and was
resumed on Opus 4.8 via `resumeFromRunId` with no findings lost.

**Superseded.** The 2026-07-11 R4 ruling that "dissolved the
shim/prompt indirection" (merged skill = command) is reversed by the
split above. The old per-skill three-symlink topology (54 symlinks)
is replaced by two directory symlinks.

Three commits: `1b50416` (the amended 2026-07-12 `/log` close, with
the external codename scrubbed from history — `dev` is local-only),
`38dcb3c` (apply-pass + surface redesign), `4c7d34b` (resolved
deferrals). Session log:
[`notes/session-logs/2026-07-13-fresh-review-surface-split.md`](notes/session-logs/2026-07-13-fresh-review-surface-split.md).
Six `resources/` entries remain PROVISIONAL pending ratification.

**Coda (same session, post-`/log`, commit `118cd4b`).** The Rijke
foundational entry (`resources/rijke-hott/`) was given a comprehensive
part-organized section map — 3 parts, 22 lectures, 247 line anchors at
`<lecture>.tex:LINE` (extracted per-lecture by a 22-agent workflow,
spot-checked against the source). A new `/hott` skill (the 19th) does
reference lookups grounded in that map: the standard formulation
SOURCE-CHECKED at the line, plus the kitcat cross-reference. Adding it
needed only the two masters — the directory symlinks surfaced it in
both harnesses — the first exercise of the new surface design.

## 2026-07-12 — the context-layer hardening arc

The feynman-derived context layer was audited against a studied
reference implementation of the same workflow discipline (like-with-
like, benched on this repo's own mathematics work) and hardened into
the library's own. Landed: `.agents/methodology.md` (the five working
principles stated as kitcat's own, with kitcat exemplars); the
bind-once cross-agent contract `.agents/CLAUDE.md` with the 18 skills
slimmed to defer to it; the roster restructured (`analyzer` = merged
theoretician + structural analyst; `coder`/`reviewer` renamed; new
`ingest`/`writer`/`suite-maintainer`); every working protocol
(spike/killcheck-refl/STUCK-wall/graduation) encoded from root
CLAUDE.md through the agents; a repo-owned `flake.nix` pinning the
latest stable Agda + ingestion tools; `just sync` gating on drift and
a new `just lint authoring` gate; the `/prove` pipeline command;
`resources/` given a canonical-source-format + `.pdftext` cache
convention; and the Rijke foundational entry (arXiv 2212.11082) as
the first live ingestion. The layer was corrected to full public
independence (no external-repo references; the methodology stands on
kitcat's own exemplars). notes/plans + notes/research became local
working memory. `verified`: authoring lint, spike-echo, symlink
integrity, tree independence, flake syntax. `unverified`: `just
check-all` under the flake (no Agda changed; last green `593f44a`).
`blocked`: five `resources/` entries + Rijke are PROVISIONAL pending
ratification. Superseded: the reboot's harness-mechanics claims
(re-audited against live builds) and the ad-hoc convention set.
Commits `f70cf94`, `6103b7f`, `202dfe7`, `9e4dfaf`. Session log:
[`notes/session-logs/2026-07-12-context-layer-hardening.md`](notes/session-logs/2026-07-12-context-layer-hardening.md).

## 2026-07-11 — the context-layer reboot (feynman port)

The repository's context management layer was rebooted: the
feynman.is research workflows were ported into a kitcat-owned,
harness-generic suite (`.agents/skills/kitcat/` — sixteen workflows
+ the HARNESS.md capability rosetta + the `spike-echo` diagnostic),
morally translated from ML research to mathematics research, and
**verified live on both harnesses** (Claude Code via `.claude/skills/`
symlinks; Pi natively plus typed `/name` adapters in `.pi/prompts/`
and `.feynman/prompts/`) — all from one canonical file per workflow.
Landed alongside: `docs/provenance.md` (binding honesty standards:
strict VERIFIED/SOURCE-CHECKED/CONJECTURED/`[unvetted]` labels, nine
practices, AI-contribution statement, date-stamped policy context);
the `resources/` vetted-sources convention (hash-verified vendored
documents, gitignored, records tracked); `docs/roadmap.md`;
CLAUDE.md rewritten as the cross-harness contract (root AGENTS.md
deleted — Pi prefers it over CLAUDE.md, verified in source); README
adapted (identity, provenance section, build; dead credits fixed).
The agent roster shipped with it: six definitions in `.agents/`
(`researcher` and `verifier` ported from the feynman originals;
four Agda specialists written fresh from the contract), registered
across all three harnesses by symlink — discovery verified live.
A six-lens whole-suite review (Opus) ran before staging; its 2
FATAL and 6 MAJOR findings are fixed (verified: the fixes are in
the staged tree). A nine-unit adversarial porcelain sweep then cut
the tooling that had no established place — `log-failure`/`Log/`,
the `deps` cluster, `benchmark`, `html-deploy`, `check-dirty`,
lint's imports check — fixed `mmv`'s unsafe rename sweep, and kept
the verified core (`check`/`check-all`, `sync`, `lint`
width+flags, `new`, `html`/`html-serve`, `stats`/`wip`);
`src/Test/` and `Stash/` are now gitignored scratch (Gloss the
upgrade path), and `All.lagda.md` no longer imports untracked
scratch (clean clones typecheck again — verified). Branch renamed
to `dev`.
**Superseded and retired to `.attic/`**: the pre-reboot context
layer — design.md, architecture.md, lexicon.md, styleguide.md,
coh.md, handoff.md (replaced by this file + the session-log chain +
the roadmap), six pre-reboot research memos, the four agent
definitions, and the docs-drift porcelain (recipe removed).
No Agda changed; `just check-all` not run (last green `593f44a`);
everything staged, commit pending Lane's go-ahead. Session log:
[`notes/session-logs/2026-07-11-context-layer-reboot.md`](notes/session-logs/2026-07-11-context-layer-reboot.md).

---

## 2026-07-11 — Cat.Codep: the coherence tower, closed by theorem

*Retroactively reconstructed 2026-07-12 (the mathematics work of the
day; the reboot above is the same day's later infrastructure
session).* The coherence overlay landed: `Cat.Codep.Coherent`
(θ-core derived, the gauge cluster collapsing to no fourth cell —
T6/T7/T19) and the Mac Lane `Triangle` (weak/full/mirror — T8), with
the parity theorem's Route-B upgrade on `Op` (T9). The theorem
ledger `docs/gloss.md` (T1–T20) and five frozen `Gloss.*`
certificates (EightFieldWall, PathGroupoid, PcomConservation,
PropPinning, TriangleFace23 — all `@ 9133396`) were committed
together in exact ledger↔certificate bijection. TEL-independence
(T11, S² countermodel + EightFieldWall), the op-involution regress
(T12), and the prop-pinning trichotomy (T13) established; the
interchange / Kelly / Melliès / binary-ancestor identifications
(T14–T17) recorded 📐. `verified` (`check-all` exit 0). This
session's commits `cfccb0b`, `9133396`, `2327309`, `593f44a`.
Session log:
[`notes/session-logs/2026-07-11-codep-coherence-tower.md`](notes/session-logs/2026-07-11-codep-coherence-tower.md).

## 2026-07-10 — Cat.Codep: hcategory reshape + the opposite category

*Retroactively reconstructed 2026-07-12.* The representable core was
reshaped to the flat-carrier `hcategory` record (collapsed tower),
and the opposite category `Cat.Codep.Op` landed with the parity
theorem — pre/post definitionally swapped, every mirror axiom
derivable (T9), giving strict self-duality of the category core
(T10); the eval axiom is self-mirror, so bias is chirality (T3). The
`Gloss.PcomConservation` (T20) and `PathGroupoid` (T18) spikes were
produced here (certificates frozen the next day, `2327309`).
`verified` (per-commit machine-checked). Commits `40e6743`,
`ed94308`, `97e3157`. Session log:
[`notes/session-logs/2026-07-10-hcategory-reshape-opposite-category.md`](notes/session-logs/2026-07-10-hcategory-reshape-opposite-category.md).

## 2026-07-09 — Cat.Codep: the representable trilayer

*Retroactively reconstructed 2026-07-12 (the overnight session; git-
local dates place it on the 9th).* The `Cat.Type`-style category was
rebuilt as `Cat.Codep`: a category presented through a representable
embedding `emb : hom ↪ composite`, the 4-field
representability-canonical carrier, and the `structure` / `axioms` /
`category` trilayer split (defeating a walking-arrow termination
class). Ancestors of ledger T1 (`Cat.Codep.Base`) and T4
(`Cat.Codep.Coherence`); the conservativity battery's path-groupoid
witness is the T18 ancestor. `verified` (five commits
machine-checked). Commits `dc52571`, `2376d5b`, `bd75cd1`,
`b5756c1`, `9bddaf8`. Session log:
[`notes/session-logs/2026-07-09-codep-representable-trilayer.md`](notes/session-logs/2026-07-09-codep-representable-trilayer.md).
