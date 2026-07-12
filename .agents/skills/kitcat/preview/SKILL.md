---
name: preview
description: Preview or export a written artifact locally — the library's rendered documentation via just html / just html-serve, or a single Markdown/LaTeX document (notes/*.md, docs/*.md) rendered to HTML or PDF and opened locally. Use when asked to preview, render, view, open, or export a document, note, plan, review, or the docs site. Local preview only; nothing is published or deployed.
section: Utilities
---

# Preview

Preview or export a written artifact locally.

Read `.agents/skills/kitcat/HARNESS.md` first; it maps every
capability named below to the tools in your harness.

Everything this skill does is local. It publishes and deploys
nothing, and a harness-rendered page is never shared
onward — viewing it is the user's decision.

## Targets, in order

1. **The library's rendered docs** — when the request is about the
   docs site or the library as a whole, run `just html` via the
   shell capability to build it, or `just html-serve` via the
   background-process capability to build and serve it; report the
   local URL and how to stop the server.
2. **A single document** — for one file (`notes/*.md`, `docs/*.md`,
   or any Markdown/LaTeX source), use the doc-preview
   capability: render with the harness-native renderer when one is
   visible; otherwise convert with pandoc via the shell capability
   to HTML (or PDF when export is requested) and open the result
   locally with the platform opener. When falling back, say so —
   the user should know they got the degraded path.
3. **An already-rendered file** (PDF, HTML) — open it directly via
   the shell capability.

When the request names no target, preview the most recently
modified artifact under `notes/` or `docs/`; state which file was
chosen.

## Rules

- This skill writes only rendered exports (HTML/PDF). They go to a
  temporary directory created via the shell capability (mktemp -d),
  or to the exact path the user names when requesting an export;
  nothing is written inside the repository. It never edits the
  source document.
- When doc-preview has no visible tool and pandoc is absent, report
  `doc-preview: BLOCKED — no visible tool` with the manual command
  a human could run (`pandoc <file>.md -o <file>.html` then open
  the result); never claim a preview was shown when it was not.
- Export to PDF requires a LaTeX installation for pandoc; when it
  is missing, deliver HTML and report the PDF path as BLOCKED with
  the manual command.
