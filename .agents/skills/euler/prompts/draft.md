---
description: Turn formalization or research findings into a polished paper-style draft — mechanization reports and write-ups with explicit claims, equations, and citations.
args: <topic>
section: Research Workflows
topLevelCli: true
---
## Tool Discipline (Read First)

Tool names are literal. Use only tools visible in the current tool set.

- Web search and fetch: use the visible search/fetch tools; do not invent names
  like `google_search`, `WebSearch`, or `search_google`.
- Library search: use shell (`rg`, `grep`, `find`) or any visible
  LSP/navigation tools over the host library.
- To ask the user a question, write plain chat text and wait for the next user
  message, unless a visible user-question tool exists. Do not invent one.
- Do not use `Task` as an agent dispatcher. Use only the visible subagent tool
  when it exists.
- If a tool returns `Tool not found` or `Invalid URL`, do not retry the same
  invalid call. Map to a canonical visible tool and valid arguments, or record
  the capability as blocked.

Write a paper-style draft for: $@

Derive a short slug from the topic (lowercase, hyphens, no filler words, ≤5
words). Use this slug for all files in this run.

Requirements:

- Before writing, outline the draft structure: proposed title, sections, key
  claims to make, source material to draw from, and a verification log for the
  critical claims, statements, and correspondences. Write the outline to
  `outputs/.plans/<slug>.md`. Briefly summarize the outline to the user and
  continue immediately. Do not ask for confirmation or wait for a proceed
  response unless the user explicitly requested outline review.
- Use the `writer` subagent when the draft should be produced from
  already-collected notes (research files, formalization reports, plan
  ledgers), then use the `verifier` subagent to add inline citations and
  verify anchors.
- Include at minimum: title, abstract, background (the informal
  mathematics), related work and prior mechanizations, encoding and design
  decisions (for mechanization reports), the main development or synthesis,
  fidelity discussion (what the formal statements establish vs. the informal
  claims), limitations, conclusion.
- Use clean Markdown with LaTeX where equations materially help.
- Follow the system prompt's provenance rules for all results, statements,
  tables, and quantitative or mechanical claims (obligation counts, build
  outcomes). If evidence is missing, leave a placeholder or a proposed plan
  instead of claiming an outcome.
- Never claim a proof checks, a module builds, or an obligation is closed
  without a recorded checker run in the source material. Mechanization reports
  must include the obligation inventory: `none`, or an enumerated list with
  locations and justification.
- Generate charts only when a chart tool is visible and the underlying
  source-backed quantitative data supports the visual; otherwise write a
  chart specification or table. Use Mermaid for module/dependency structure
  only when the structure is supported by the artifacts. Every diagram,
  chart spec, or table needs provenance.
- Before delivery, sweep the draft for any claim that sounds stronger than
  its support — especially "fully formalized", "verified", "equivalent to the
  informal theorem". Mark tentative results as tentative and remove
  unsupported claims instead of letting the verifier discover them later.
- Save exactly one draft to `papers/<slug>.md`.
- End with a `Sources` appendix with direct anchors (URLs, file paths,
  theorem numbers) for all primary references.
