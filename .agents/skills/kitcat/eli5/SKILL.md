---
name: eli5
description: Explain a theorem, a docs/gloss.md ledger entry, a module, or a paper in type theory, category theory, univalent mathematics, or programming language foundations in plain English — six fixed sections, minimal jargon, one strong analogy, and strict separation of what is machine-checked in this repository from what a source merely claims. Use when asked to ELI5 something, explain a result simply, remove jargon, or say what a dense proof, module, or paper actually means. Delivers the explanation in chat; large-document runs leave checkpointed working notes in notes/research/.
argument-hint: <theorem|gloss-entry|module|paper-or-url> [--window-size <chars>] [--overlap <chars>] [--tier-threshold <chars>]
args: <theorem|gloss-entry|module|paper-or-url> [--window-size <chars>] [--overlap <chars>] [--tier-threshold <chars>]
section: Research Workflows
topLevelCli: true
---

# ELI5

Explain in plain English: $ARGUMENTS

Read `.agents/skills/kitcat/HARNESS.md` first; it maps every
capability named below to the tools in your harness.

Derive a short slug from the target (lowercase, hyphens, no filler
words, at most 5 words). Every file this run writes uses that slug.

This is an execution request, not a request to explain the workflow.
Resolve the target and begin; do not narrate the protocol.

## Resolve the target (local-first)

The target is a theorem or `docs/gloss.md` entry, a module, or a
paper; consult what the repository holds before any web capability:

- **Theorem or ledger entry** — the `docs/gloss.md` entry and its
  status marker, the literate prose of the
  module that proves it, and the `src/Gloss/` certificate when the
  entry names one — via the file-read and file-search capabilities.
- **Module** — the module's own literate prose first, then the
  prose of the imports its central idea leans on.
- **Paper** — a `resources/<slug>/` vendored entry first (cite it
  by entry when it covers the source); otherwise locate the paper
  with the paper-search capability against the primary venues
  (arXiv math.CT / cs.LO / math.LO / math.AT, nLab, 1lab,
  TypeTopology, author pages), then fetch it. Given only a topic,
  anchor on the clearest of 1–3 representative papers.

Whatever the target, check `docs/gloss.md` for related mechanized
results — the only claims the explanation may mark VERIFIED.

## Configuration

Three knobs control the windowed reading below; inline flags
override environment variables, defaults apply when neither is set.

- `--window-size <chars>` or `KITCAT_ELI5_WINDOW_CHARS` (default 6000)
- `--overlap <chars>` or `KITCAT_ELI5_OVERLAP_CHARS` (default 500)
- `--tier-threshold <chars>` or `KITCAT_ELI5_TIER_THRESHOLD`
  (default 8000)

Validate window-size > overlap; on violation, stop and report a
configuration error. For an on-disk document, log the resolved
values once: `[eli5] config window=<w> overlap=<o> tier=<t>`.

## Get the source onto disk

Repo-internal targets (a gloss entry, a module, design prose) are
read directly — no staging. For an external or file document, run
every guard below before any tier logic; a failure here is cheap, a
failure mid-window is not.

- A repository URL `https://github.com/owner/repo` (exactly 4
  slashes) means the README: fetch the raw file at
  `raw.githubusercontent.com/owner/repo/main/README.md`, then
  `/master/README.md`; the repository HTML page is not the document.
- Remote URL: download to `notes/research/<slug>-raw.txt` with the
  shell capability (`curl -sL -o notes/research/<slug>-raw.txt
  <url>`). url-fetch is fine for small pages (an abstract, an
  index), never for the document body — its return value enters
  context directly, which the on-disk discipline exists to prevent.
- Local file or PDF: copy, or extract text with `pdftotext` via the
  shell capability, into `notes/research/<slug>-raw.txt`.
- Under 50 bytes after fetching, or over 1 KB with fewer than 100
  readable text characters: stop and report — a bad fetch, or
  binary, unextracted content; do not proceed to tier selection.
- `notes/research/<slug>-summary.md` already exists: ask with the
  user-question capability whether to overwrite or pick a new slug;
  do not proceed until answered.

Measure decoded text characters, not bytes — UTF-8 multi-byte
characters would overcount. Log:
`[eli5] source=<source> slug=<slug> chars=<count>`.

## Choose a tier

Windowing keeps context pressure proportional to the window size,
not the document size; the table decides which strategy applies.

| Decoded chars | Strategy |
| --- | --- |
| below tier-threshold | Direct read — read in full and explain |
| at or above tier-threshold | Windowed, checkpointed read (below) |

Log: `[eli5] tier=<direct|windowed> chars=<count>`.

## Windowed reading (checkpointed)

The document stays on disk. Extract windows by character offset via
the shell capability:

```python
# file-read tools address lines, not characters; char-boundary
# windowing needs the shell. Overlapping starts keep a claim
# that spans a boundary intact in at least one window.
with open("notes/research/<slug>-raw.txt", encoding="utf-8") as f:
    f.seek(n * (window_size - overlap))
    window = f.read(window_size)
```

For each window, in order:

1. Extract the key claims, definitions, theorem statements, and
   proof moves, each with enough context to stand alone. Mark a
   claim cut off at a window boundary `BOUNDARY PARTIAL`; drop the
   marker when a later window carries the complete version.
2. Append the extract to `notes/research/<slug>-summary.md` as an
   entry opening with a `## Window <N>` heading, **before** reading
   the next window. This is the checkpoint: an interrupted session
   loses at most one window.
3. Log: `[eli5] window <N>/<total> done`.

On restart, count the `## Window <N>` headings already in
`notes/research/<slug>-summary.md` and resume from the next
window — never re-read from the top. When every window is done,
synthesize the accumulated notes into a closing summary section of
the same file — a claim appearing in overlapping windows is one
claim; keep the most complete formulation — then write the
explanation from the notes, not from memory of the raw text.

## The explanation

Six sections, always in this order: **One-Sentence Summary**,
**Big Idea**, **How It Works**, **Why It Matters**, **What To Be
Skeptical Of**, **If You Remember 3 Things**.

Guidelines, all binding:

- Short sentences, concrete words. Define jargon the moment it
  appears or remove it.
- One strong analogy beats several weak ones. Say where the analogy
  stops working.
- Separate what the source actually shows from interpretation and
  speculation, and label which is which.
- Epistemic labels are strict. VERIFIED applies only to claims
  machine-checked in this repository — name the module or the
  `Gloss.*` certificate. A claim taken from a paper is CONJECTURED,
  written `CONJECTURED, SOURCE-CHECKED against <ref>` when the
  cited document was opened and states it. Your own reading between
  the lines is labeled as interpretation.
- **What To Be Skeptical Of** covers, at minimum: hypotheses the
  result quietly leans on, steps the source does not mechanize or
  prove, and any gap between the paper's formulation and this
  repository's (wild categories, `--erased-cubical`, no hom-set
  conditions).
- Novelty language is "we are not aware of prior work" plus the
  searches performed — never "new" or "first".

## Verify

Before delivery, run one adversarial pass over the draft:
load-bearing claims without an epistemic label, labels stronger
than their evidence, an analogy implying properties the source
never establishes, jargon left undefined, and sections surviving
from earlier drafts that the final evidence no longer supports.
Grade findings FATAL / MAJOR / MINOR; fix FATAL findings and run
one more pass after the fixes; carry MAJOR findings into a closing
"Open questions" line of the explanation; accept MINOR.

## Deliver

The explanation goes to chat — it is the deliverable, not a file. A
direct-read run of a repo-internal target writes nothing; a
direct-read run of an external or local document leaves only
`notes/research/<slug>-raw.txt` behind. A windowed run also leaves
`notes/research/<slug>-summary.md` as working notes, closing with:
the source and its vetting status (`resources/` entry,
SOURCE-CHECKED, or `[unvetted]`), the resolved configuration, the
verification status (PASS / PASS WITH NOTES / BLOCKED) and the run
date, and any blocked capability with the manual command a human
could run instead. Verify on disk that the file exists before
stopping a windowed run.

This skill writes only `notes/research/<slug>-raw.txt` and
`notes/research/<slug>-summary.md` — nothing else, anywhere. A
paper worth permanent vetting, a gloss entry worth pursuing, or a
mechanization spike the explanation suggests is a proposal, stated
in chat or in the working notes — never executed as a side effect.

## Honesty rules (binding)

- No reference supports a claim unless the cited document was
  opened and says what it is cited for. A reference surfaced by
  automated search is `[unvetted]` and supports no load-bearing
  claim until a human or a `resources/` entry confirms it.
- A capability with no visible tool is reported BLOCKED with the
  manual command a human could run; never simulate a capability or
  claim its result. Windowed runs record BLOCKED entries in
  `notes/research/<slug>-summary.md`; direct-read runs report them
  in chat.
- Plain English never earns extra confidence: an explanation
  simplifies the language, never the epistemic status.
