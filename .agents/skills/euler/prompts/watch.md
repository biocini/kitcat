---
description: Create a research watch baseline for a mathematical topic or mechanization area, with an optional scheduled follow-up when scheduling tools are visible.
args: <topic>
section: Research Workflows
topLevelCli: true
---
## Tool Discipline (Read First)

Tool names are literal. Use only tools visible in the current tool set.

- Web search and fetch: use the visible search/fetch tools; do not invent names
  like `google_search`, `WebSearch`, or `search_google`.
- To ask the user a question, write plain chat text and wait for the next user
  message, unless a visible user-question tool exists. Do not invent one.
- Do not use `Task` as an agent dispatcher. Use only the visible subagent tool
  when it exists.
- If a tool returns `Tool not found` or `Invalid URL`, do not retry the same
  invalid call. Map to a canonical visible tool and valid arguments, or record
  the capability as blocked.

Create a research watch baseline for: $@

Derive a short slug from the watch topic (lowercase, hyphens, no filler words,
≤5 words). Use this slug for all files in this run.

Requirements:

- Before starting, outline the watch plan: what to monitor (new papers on a
  topic, new mechanizations in a library or archive, changes to a specific
  upstream library the host project depends on), what signals matter, what
  counts as a meaningful change, and the requested or sensible check
  frequency. Write the plan to `outputs/.plans/<slug>.md`. Briefly summarize
  the plan to the user and continue immediately. Do not ask for confirmation
  or wait for a proceed response unless the user explicitly requested plan
  review.
- Start with a baseline sweep of the topic.
- Use the visible scheduling tool to create the recurring or delayed
  follow-up only when one is visible in the current tool set.
- If no scheduling tool is visible, do not claim a recurring watch was
  scheduled. Record `Scheduling: BLOCKED - no scheduling tool available` in
  the plan and baseline artifact, then give the exact command or prompt the
  user can run later to refresh the watch.
- Save exactly one baseline artifact to `outputs/<slug>-baseline.md`.
- End with a `Sources` section containing direct anchors (URLs, file paths)
  for every source used.
