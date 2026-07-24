---
description: Run an internal critique of a mathematical artifact — paper draft, mechanization report, or formalization — with likely objections, severity, and a concrete revision plan.
args: <artifact>
section: Research Workflows
topLevelCli: true
---
## Tool Discipline (Read First)

Tool names are literal. Use only tools visible in the current tool set.

- Web search and fetch: use the visible search/fetch tools; do not invent names
  like `google_search`, `WebSearch`, or `search_google`.
- Library search: use shell (`rg`, `grep`, `find`) or any visible
  LSP/navigation tools over the host library.
- The proof checker runs via shell using the project's check command when the
  artifact under review makes mechanical claims and a toolchain block exists.
  Never simulate, predict, or assume a check result; only a recorded run
  counts.
- To ask the user a question, write plain chat text and wait for the next user
  message, unless a visible user-question tool exists. Do not invent one.
- Do not use `Task` as an agent dispatcher. Use only the visible subagent tool
  when it exists.
- If a tool returns `Tool not found` or `Invalid URL`, do not retry the same
  invalid call. Map to a canonical visible tool and valid arguments, or record
  the capability as blocked.

Review this mathematical artifact: $@

Derive a short slug from the artifact name (lowercase, hyphens, no filler
words, ≤5 words). Use this slug for all files in this run.

This is an execution request, not a request to explain or implement the
workflow instructions. Carry out the workflow with tools and durable files. Do
not answer by describing the protocol, saying what you would do, or stopping
after a plan.

Do not ask for confirmation. Briefly summarize the plan to the user and
continue immediately unless the user explicitly asked to review the plan
first.

Required artifacts:

- Plan: `outputs/.plans/<slug>-review.md`
- Evidence notes: `outputs/.drafts/<slug>-review-evidence.md`
- Final review: `outputs/<slug>-review.md`

Workflow:

1. Create `outputs/.plans`, `outputs/.drafts`, and `outputs`.
2. Write `outputs/.plans/<slug>-review.md` with:
   - artifact identifier and source type (paper draft, arXiv ID, local file,
     mechanization report, library module set, etc.)
   - review criteria: correctness of statements, rigor of proofs, fidelity of
     any informal→formal correspondence, definition integrity (no gaming,
     no vacuousness), completeness claims vs. obligation reality, related-work
     positioning, writing quality
   - verification checks needed: which claims can be checked against sources,
     which against the library, and which against the kernel (when a
     toolchain block exists)
3. Continue immediately. Do not end after planning.
4. Inspect the artifact:
   - For local files, read or parse the file directly.
   - For PDFs, use available PDF/document parsing tools. If PDF parsing fails,
     use any available fallback extraction, record the failure, and still
     produce a blocked or partial review artifact.
   - For arXiv IDs or URLs, fetch the paper/source directly and record the
     URL.
   - For formalization artifacts, resolve the toolchain block; run the
     obligation and unsafe-marker greps on the implicated files.
   - Inspect linked code, libraries, supplemental material, or citations when
     they are reachable and materially affect the review.
5. Write evidence notes to `outputs/.drafts/<slug>-review-evidence.md` before
   writing the final review. Include quoted/paraphrased claims, observed
   definitions and statements, reported results, fidelity correspondences,
   reproducibility facts, and every inspected source path or URL.
6. Use the `researcher` and `reviewer` subagents only if the subagent tool is
   available and the artifact is large enough to benefit from delegation. If
   subagents are unavailable, fail, or would only add overhead, do the
   lead-owned review directly. Never merely say a subagent was spawned; either
   call the tool or continue yourself.
7. Write exactly one final review artifact to `outputs/<slug>-review.md`
   with:
   - Summary Assessment
   - Strengths
   - Critical Issues
   - Major Issues
   - Minor Issues
   - Reproducibility and Verification (checker runs performed, obligation
     inventory when applicable)
   - Inline Annotations tied to sections, claims, statements, or declarations
     where possible
   - Recommendation
   - Sources
8. If the artifact cannot be parsed or critical evidence is unavailable, still
   write `outputs/<slug>-review.md`. Mark the affected sections with
   `Verification: BLOCKED`, explain exactly what failed, and distinguish
   blocked checks from actual weaknesses of the artifact.
9. Before responding, verify on disk that `outputs/<slug>-review.md` exists.
   If it does not exist, create it immediately as a blocked review artifact
   with the failure reason.

Never end with planning-only chat. Never ask what to do next. Never claim the
review is complete unless `outputs/<slug>-review.md` exists.
