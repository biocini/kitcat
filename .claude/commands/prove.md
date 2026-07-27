---
description: Bounded proof/experiment loop - try hypotheses (induction principles, generalizations, encodings, lemmas), measure with the kernel, keep what checks, record what fails, repeat.
argument-hint: <goal>
disable-model-invocation: true
---

Start a bounded proof loop for: $ARGUMENTS

This command runs a bounded foreground loop in which the proof checker is the
oracle. It is for closing obligations, making a module build, discharging a
specific lemma, minimizing an axiom dependence, or any goal where "did the
check pass?" is the success signal.

## Step 1: Gather

If `outputs/.prove/prove.md` and `outputs/.prove/prove.jsonl` already exist,
ask the user (AskUserQuestion) whether to resume or start fresh. If resuming, also verify
that `outputs/.prove/prove.sh` still matches the toolchain block's check
command; regenerate it if not. If `CHANGELOG.md` exists, read the most recent
relevant entries before resuming.

Otherwise, collect the following from the user before doing anything else:

- What to achieve (close N obligations in file X, make module Y check, prove
  lemma Z, eliminate axiom A from declaration D, reduce check time)
- The metric name and direction: obligations open (lower is better), build
  passes (boolean), axioms used (lower is better), check wall-time (lower is
  better)
- Files in scope for changes
- Maximum number of iterations (default: 20)

## Step 2: Toolchain and environment

Resolve the toolchain block first (`.euler/TOOLCHAIN.md` or a
`## Toolchain` section in the project `CLAUDE.md`). The check command comes
from it, never from guesswork. If the block defines `probe`, run it now as
the environment sanity check and record the outcome. If the toolchain block
is missing, ask the user for the check command and sorry token(s) and record
them; if the checker cannot execute at all, stop — a proof loop without its
oracle is pointless. Do not run a degraded loop.

Then ask the user (AskUserQuestion) where to run:

- **Local** — run in the current working directory
- **New git branch or worktree** — so the main line stays clean
- **Container** — run check commands inside an isolated container with the
  project's toolchain image
- **Plan only** — produce the loop plan and session files without iterating

Do not proceed without a clear answer.

## Step 3: Confirm

Present the full plan to the user before starting:

```
Goal:                [goal]
Metric:              [metric] ([direction])
Check command:       [command from toolchain block]
Files in scope:      [files]
Environment:         [chosen environment]
Max iterations:      [N]
```

Ask the user to confirm (AskUserQuestion). Do not start the loop without
explicit approval.

## Step 4: Run

Initialize the session: create `outputs/.prove/prove.md`,
`outputs/.prove/prove.jsonl`, and `outputs/.prove/prove.sh`. These are the
loop-state files: fixed names, one active loop per project (see `.claude/rules/euler.md`);
concurrent loops use separate worktrees.

- `prove.sh` — the exact check invocation (from the toolchain block) plus the
  obligation-count grep, so every iteration is measured the same way.
- `prove.md` — the human-readable log: goal, baseline, per-iteration entries,
  decision log.
- `prove.jsonl` — one JSON object per iteration:
  `{iteration, hypothesis, files_changed, check_command, check_result,
  metric_value, decision, reason}`.

Run the baseline first: execute `prove.sh`, record the starting metric
(obligations open, build status, etc.). Do not start editing before a baseline
exists.

Each iteration:

1. **Hypothesis** — state what you are trying and why ("generalize the
   induction hypothesis over the context", "introduce a size measure for
   termination", "extract lemma L before the main induction").
2. **Edit** — make the change within the scoped files.
3. **Check** — run `prove.sh` via shell. Record the command, result, and
   metric value. Never predict the outcome; only the run counts.
4. **Log** — append to `prove.md` and `prove.jsonl`.
5. **Decide** — keep the change, revert it, or record the failed hypothesis.
   Decisions follow the metric: a change that does not improve the metric (or
   strictly needed intermediate state explicitly justified in the log) is
   reverted.
6. Repeat. Do not stop unless interrupted, the goal is met, or
   `maxIterations` is reached.

The failed-strategy journal is a first-class deliverable. For each failed
hypothesis, record the reason in `prove.md`: wrong induction principle,
missing lemma, encoding mismatch, termination checker rejection, universe or
size constraint, etc. Future runs read this journal before re-attempting the
same target.

After the baseline and after meaningful milestones (goal met, half the
iterations consumed, a previously-blocking obligation discharged), append a
concise entry to `CHANGELOG.md`: what changed, what the checker said, what
failed, and the next step.

## Completion

When the loop ends (goal met, budget exhausted, or `/prove off`):

- If the metric goal was met, run one final full `check` (not just
  `check-file`) and record it before declaring success.
- Audit obligations and unsafe markers in the scoped files with the toolchain
  block's grep lists; disclose every hit.
- Write the outcome summary at the top of `prove.md`: final metric value vs.
  baseline, obligations remaining with `file:line`, and the honest status
  label (`verified`, `unverified`, `blocked`, `inferred`).

## Subcommands

- `/prove <text>` — start or resume the loop
- `/prove off` — stop the loop, keep data
- `/prove clear` — delete all state and start fresh
