---
name: jobs
description: Inspect what is running and what is pending in this repository — background typechecks and doc builds, scheduled follow-ups, src/Test/ spikes with ages, open plan ledgers, watch entries, session-log recency, and the latest next-step preview. Use when asked what's running, job status, background status, open follow-ups, stale spikes, or where the work stands. Delivers a concise status report in chat; writes nothing.
section: Project & Session
topLevelCli: true
---

# Jobs

Report the current running and durable state of this repository.

Read `.agents/skills/kitcat/HARNESS.md` first; it maps every
capability named below to the tools in your harness.

This is an execution request, not a request to explain the workflow.
Begin with the inspection, not with prose about the protocol.

This skill is read-only: it writes no files anywhere — not in
`notes/`, not in `src/`. Its only output is the status report
delivered in chat, and that report is also the recording location
for BLOCKED capabilities.

## Inspect

1. **Running background work** — With the background-process
   capability, list active and recently finished background tasks:
   typecheck runs (`just check-all` / `check`),
   doc builds, and anything else launched in the
   background. For
   each, report what it is running, how long it has been running or
   how it exited, and where its output can be read. When the
   capability has no visible tool, report
   `Background work: BLOCKED — no visible tool` and state the manual
   check: run `ps aux | rg -i 'agda|just'` in a terminal to see live
   processes, or rerun the check directly with `just check-all`.

2. **Scheduled follow-ups** — With the scheduling capability, list
   queued one-shot and recurring follow-ups: what fires, when, and
   what it will do. When the capability has no visible tool, report
   `Scheduled follow-ups: BLOCKED — no visible tool` and state the
   manual check: run `crontab -l` or open the harness's own
   scheduler listing to check for queued work.

3. **Durable state sweep** — With the file-read, file-search, and
   shell capabilities, sweep the on-disk state:
   - `src/Test/` — timestamped spike files, newest first, each with
     its age taken from the filesystem. Spikes are scratch by
     design; report age, do not judge it.
   - `notes/plans/` — run ledgers; report each plan whose task
     ledger still has entries not marked done, blocked, or
     superseded, with a one-line summary of what remains open.
   - `notes/watches/` — watch entries and when each was last
     updated.
   - `notes/session-logs/` — the most recent session log and its date; flag
     when the newest log predates the newest change elsewhere in
     the sweep.
   - `docs/roadmap.md` and the latest `notes/session-logs/` entry — read
     the standing targets and the next-step preview; report them.
     This skill writes neither.
   A directory that does not exist or is empty is a finding, not an
   error: report it as absent or as empty, whichever the filesystem
   shows.

4. **Report** — Summarize in chat, grouped in this order: running
   background work; scheduled follow-ups; durable state (spikes,
   open plans with any failures they preserve, watches, log
   recency, the latest next-step preview); failures needing attention (background tasks that exited
   nonzero, warning exits — exit 42 is failure in this repository —
   stalled plans); and the next concrete
   command for anyone wanting logs or detail (`just wip`,
   `just stats`, or the specific output path of
   a background task). Be concise and operational.

## Honesty rules (binding)

- Report what IS; mark what cannot be checked. A capability with no
  visible tool is reported BLOCKED with the manual command a human
  could run — the state behind a blocked capability is never
  simulated, and background state is never claimed to exist or to
  be absent when it could not be inspected.
- Ages, dates, and exit states come from the filesystem and the
  visible tools, never from estimation or memory.
- Nothing found is a report, not a silence: an empty sweep says so
  explicitly, per section.
- Anything actionable the sweep surfaces (a spike worth promoting,
  a plan worth closing, a watch worth refreshing) is a proposal
  stated in the report — never executed as a side effect of this
  skill.
