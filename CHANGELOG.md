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
