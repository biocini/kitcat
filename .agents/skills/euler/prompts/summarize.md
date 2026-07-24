---
description: Summarize a mathematical source — paper, textbook chapter, lecture notes, mechanization file, or local artifact — using the RLM pattern: source stored on disk, never injected raw into context.
args: <source> [--window-size <chars>] [--overlap <chars>] [--tier1-threshold <chars>] [--tier2-threshold <chars>]
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

Summarize the following source: $@

Derive a short slug from the source filename or URL domain (lowercase,
hyphens, no filler words, ≤5 words — e.g. `homotopy-type-theory-book`). Use
this slug for all files in this run.

## Why this uses the RLM pattern

Standard summarization injects the full document into context. Above ~15k
tokens, early content degrades as the window fills (context rot). This
workflow keeps the document on disk as an external variable and reads only
bounded windows — so context pressure is proportional to the window size, not
the document size. Mathematical texts amplify the problem: definitions are
load-bearing hundreds of pages later, so losing early content is fatal.

Tier 1 (below the Tier-1 threshold) is a deliberate exception: direct
injection is safe for short inputs and windowed reading would add unnecessary
friction.

## Runtime knobs (context-window controls)

Support both inline flags and environment variables so users can tune
context-window behavior per run or globally.

- `--window-size <chars>` or `EULER_SUMMARIZE_WINDOW_CHARS` (default: `6000`)
- `--overlap <chars>` or `EULER_SUMMARIZE_OVERLAP_CHARS` (default: `500`)
- `--tier1-threshold <chars>` or `EULER_SUMMARIZE_TIER1_THRESHOLD` (default: `8000`)
- `--tier2-threshold <chars>` or `EULER_SUMMARIZE_TIER2_THRESHOLD` (default: `60000`)

Rules:

- Inline flags override environment variables.
- Validate `window-size > overlap` and `tier1-threshold < tier2-threshold`; if
  invalid, stop and report a clear configuration error.
- Log resolved values once per run:
  `[summarize] config window=<w> overlap=<o> tier1=<t1> tier2=<t2>`.

---

## Step 1 — Fetch, validate, measure

Run all guards before any tier logic. A failure here is cheap; a failure
mid-Tier-3 is not.

- **GitHub repo URL** (`https://github.com/owner/repo` — exactly 4 slashes):
  fetch the raw README instead. Try
  `https://raw.githubusercontent.com/{owner}/{repo}/main/README.md`, then
  `/master/README.md`. A repo HTML page is not the document the user wants to
  summarize. (For mechanization repos, also note the index/root file that
  imports all modules, when the README names it.)
- **Remote URL**: fetch to disk with
  `curl -sL -o outputs/.notes/<slug>-raw.txt <url>`. Do NOT pipe the response
  through a context-returning fetch tool — that bypasses the RLM
  external-variable principle.
- **Local file or PDF**: copy or extract to `outputs/.notes/<slug>-raw.txt`.
  For PDFs, extract text via `pdftotext` or equivalent before measuring.
- **Empty or failed fetch**: if the file is < 50 bytes after fetching, stop
  and surface the error to the user — do not proceed to tier selection.
- **Binary content**: if the file is > 1 KB but contains < 100 readable text
  characters, stop and tell the user the content appears binary or
  unextracted.
- **Existing output**: if `outputs/<slug>-summary.md` already exists, ask the
  user whether to overwrite or use a different slug. Do not proceed until
  confirmed.

Measure decoded text characters (not bytes — UTF-8 multi-byte chars would
overcount). Log: `[summarize] source=<source> slug=<slug> chars=<count>`

---

## Step 2 — Choose tier

| Chars | Tier | Strategy |
|---|---|---|
| < `<tier1-threshold>` | 1 | Direct read — full content enters context (safe for short inputs) |
| `<tier1-threshold>` – `<tier2-threshold>` | 2 | RLM-lite — windowed bash extraction, progressive notes to disk |
| > `<tier2-threshold>` | 3 | Full RLM — bash chunking + parallel researcher subagents |

Log: `[summarize] tier=<N> chars=<count>`

---

## Tier 1 — Direct read

Read `outputs/.notes/<slug>-raw.txt` in full. Summarize directly using the
output format. Write to `outputs/<slug>-summary.md`.

---

## Tier 2 — RLM-lite windowed read

The document stays on disk. Extract `<window-size>`-char windows via bash:

```python
# WHY f.seek/f.read: line-offset reads are not char-offset reads.
# For exact char-boundary windowing across arbitrary text, bash is required.
with open("outputs/.notes/<slug>-raw.txt", encoding="utf-8") as f:
    f.seek(n * <window-size>)
    window = f.read(<window-size>)
```

For each window:

1. Extract key claims, definitions, and theorem statements (with their
   numbers).
2. Append to `outputs/.notes/<slug>-notes.md` before reading the next window.
   This is the checkpoint: if the session is interrupted, processed windows
   survive.
3. Log: `[summarize] window <N>/<total> done`

Synthesize `outputs/.notes/<slug>-notes.md` into `outputs/<slug>-summary.md`.

---

## Tier 3 — Full RLM parallel chunks

Each chunk gets a fresh researcher subagent context window — context rot is
impossible because no subagent sees more than `<window-size>` chars.

WHY overlap matters: mathematical arguments span chunk boundaries — a proof
can run several pages, and a definition invoked far from its statement changes
the reading. The configured overlap ensures a cross-boundary claim appears
fully in at least one adjacent chunk. When a chunk boundary falls mid-proof,
the BOUNDARY PARTIAL rule below is what keeps the synthesis honest.

### 3a. Chunk the document

```python
import os
os.makedirs("outputs/.notes", exist_ok=True)

with open("outputs/.notes/<slug>-raw.txt", encoding="utf-8") as f:
    text = f.read()

chunk_size, overlap = <window-size>, <overlap>
chunks, i = [], 0
while i < len(text):
    chunks.append(text[i : i + chunk_size])
    i += chunk_size - overlap

for n, chunk in enumerate(chunks):
    # Zero-pad index so files sort correctly (chunk-002 before chunk-010)
    with open(f"outputs/.notes/<slug>-chunk-{n:03d}.txt", "w", encoding="utf-8") as f:
        f.write(chunk)

print(f"[summarize] chunks={len(chunks)} chunk_size={chunk_size} overlap={overlap}")
```

### 3b. Confirm before spawning

Briefly summarize: "Source is ~<chars> chars -> <N> chunks -> <N> researcher
subagents. Continuing with the chunked pass." Then continue automatically. Do
not ask for confirmation or wait for a proceed response unless the user
explicitly requested review before launching.

### 3c. Dispatch researcher subagents

```json
{
  "tasks": [{
    "agent": "researcher",
    "task": "Read ONLY `outputs/.notes/<slug>-chunk-NNN.txt`. Extract: (1) definitions and theorem statements with their numbers, (2) key claims and proof ideas, (3) cited references. Do NOT use web search or fetch external URLs — this is single-source summarization. If a statement or proof appears to start or end mid-way at the file boundary, mark it BOUNDARY PARTIAL. Write to `outputs/.notes/<slug>-summary-chunk-NNN.md`.",
    "output": "outputs/.notes/<slug>-summary-chunk-NNN.md"
  }],
  "concurrency": 4,
  "failFast": false
}
```

### 3d. Aggregate

After all subagents return, verify every expected
`outputs/.notes/<slug>-summary-chunk-NNN.md` exists. Note any missing chunk
indices — they will appear in the Coverage gaps section of the output. Do not
abort on partial coverage; a partial summary with gaps noted is more useful
than no summary.

When synthesizing:

- **Deduplicate**: a claim in multiple chunks is one claim — keep the most
  complete formulation.
- **Resolve boundary conflicts**: for adjacent-chunk contradictions, prefer
  the version with more supporting context.
- **Remove BOUNDARY PARTIAL markers** where a complete version exists in a
  neighbouring chunk.
- **Preserve numbering**: theorem/definition numbers are the anchors; never
  renumber or invent numbers.

Write to `outputs/<slug>-summary.md`.

---

## Output format

All tiers produce the same artifact at `outputs/<slug>-summary.md`:

```markdown
# Summary: [document title or source filename]

**Source:** [URL or file path]
**Date:** [YYYY-MM-DD]
**Tier:** [1 / 2 (N windows) / 3 (N chunks)]

## Key Claims
[3-7 most important assertions, each as a bullet, each with its theorem/section anchor]

## Field Context
[Where the source positions itself, which prior work or research line it claims
to extend, and what remains source-inferred rather than externally checked. Do
not invent author/background; use `/lit` for a corpus-level view.]

## Technical Hinges
[2-4 contributions or decisions the source turns on — definitions, encodings,
key lemmas — ranked by originality and importance. For each hinge, name the
contrast with prior work when the source gives enough evidence.]

## Methodology From Primitives
[Approach, definitions, proof techniques, and failure modes explained from
first principles. Omit only when the source has no technical core.]

## Limitations
[What the source explicitly flags as weak, incomplete, assumed, or out of
scope — including axioms or non-constructive principles it relies on]

## Follow-up Questions
[3 questions that would change the next research or formalization decision,
grounded in the source's discussion, limitations, results, or open problems]

## Verdict
[One paragraph: what this document establishes, its credibility, who should
read it, and whether it is a formalization target]

## Sources
1. [Title or filename] — [URL or file path]

## Coverage gaps *(Tier 3 only — omit if all chunks succeeded)*
[Missing chunk indices and their approximate byte ranges]
```

Before you stop, verify on disk that `outputs/<slug>-summary.md` exists.

Sources contains only the single source confirmed reachable in Step 1. No
verifier subagent is needed — there are no URLs constructed from memory to
verify.
