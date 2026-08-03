---
description: Create a research watch baseline for a mathematical topic or mechanization area, with an optional scheduled follow-up when scheduling tools are visible.
argument-hint: <topic>
disable-model-invocation: true
---

Create a research watch baseline for: $ARGUMENTS

Derive a slug per euler.md §File naming. Use this slug for all files in this
run.

Requirements:

- Before starting, outline the watch plan: what to monitor (new papers on a
  topic, new mechanizations in a library or archive, changes to a specific
  upstream library the host project depends on), what signals matter, what
  counts as a meaningful change, and the requested or sensible check
  frequency. Write the plan to `outputs/.plans/<slug>.md`. Continue after the
  plan per euler.md §Invocation semantics.
- Start with a baseline sweep of the topic.
- Create the recurring or delayed follow-up with the session's scheduling
  tooling (CronCreate, or the `schedule` skill) only when it is available.
- If no scheduling tool is available, do not claim a recurring watch was
  scheduled. Record `Scheduling: BLOCKED - no scheduling tool available` in
  the plan and baseline artifact, then give the exact command or prompt the
  user can run later to refresh the watch.
- Save exactly one baseline artifact to `outputs/<slug>-baseline.md`.
- End with a `Sources` section containing direct anchors (URLs, file paths)
  for every source used.
