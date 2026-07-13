# resources/ — vetted source references

Each entry is one source (paper, book chapter, thesis, slide deck,
web reference) in its own directory: `resources/<slug>/`.

The directory serves two roles. It is the on-hand reference shelf
for the research materials this repository draws on — human and
agentic users alike open an entry to discover more about a source a
research artifact cites. And it is the citation store: an entry
carries **all the information needed to generate an academic
citation in the future** — full bibliographic record, the exact
document identity (hash + vintage), and where it came from.

**Information flows one way: from resources out, never from the
repository into resources.** An entry is self-contained — it
describes its source in the source's own terms and references at
most other entries in this tree, never modules, ledgers, notes, or
any research artifact elsewhere in the repository. Tracking what
*uses* a source is the job of the repository's own corpus (proof
artifacts, docs, the theorem ledger), which cites *into* this tree.
The repository is the moving target; this doctrine is what keeps an
entry durable against staleness as everything around it changes. A
repository reference appearing inside an entry is a defect.

An entry is built to serve a construction *at speed*: when a proof
turns on a source, the reader opens the vendored copy and jumps to
the cited line, so the map below is line-anchored, not vague.

## Canonical source format

House the source's own markup when it exists. The format hierarchy:

1. **Source markup** — LaTeX `.tex` (an arXiv e-print), or other
   markup. Math and structure stay intact and greppable; this is
   the canonical form, preferred over everything below.
2. **PDF** — when no source markup is available.
3. **Transcribed text** (`.pdftext`) — a `pdftotext` extraction, the
   lowest form: a greppability fallback beside a PDF when the source
   markup is absent.

Each entry records its canonical format (LaTeX-source / PDF / scan).
All vendored and derived forms are gitignored — the source tarball,
the extracted markup, the `.pdftext` — so only tracked, regenerable
metadata leaves the machine. A new unfolded-source file extension not
yet ignored is added to `.gitignore` as encountered.

## Entry format — `resources/<slug>/README.md`

- **Citation** — full bibliographic record: authors, title, venue,
  year, DOI or arXiv id, URL.
- **Vetting** — who opened the document and when, and what it was
  checked to say. A directed agent ingestion produces a PROVISIONAL
  entry (say so here); it becomes vetted only after Lane confirms.
  No load-bearing citation rests on a PROVISIONAL entry.
- **Files** — an inventory of the vendored artifacts (the source
  tarball, the extracted markup or `.pdftext`), naming the canonical
  format and which file the reader greps. A `.pdftext` extraction
  records its **provenance**: the exact `pdftotext` command and the
  poppler version that produced it (run inside `nix develop`, whose
  flake pins poppler — line anchors into an extraction are only as
  stable as the extractor), so the extraction is regenerable
  byte-identically.
- **Source URL and re-fetch** — where the document was actually
  obtained: the fetch URL kept for record whenever a known URL
  sourced the artifact (binding for PDFs — an arXiv id is already a
  stable identifier, a bare PDF is not), plus the explicit re-fetch
  command when a stable URL exists (`curl -L -o <file> <url>`), or an
  honest note that no stable re-fetch exists (a user-supplied file, a
  moved page). Backups of irreplaceable artifacts are handled outside
  the repository; the entry's job is to record identity (hash) and
  origin (URL) so any copy can be authenticated.
- **Document hash** — sha256 of the **canonical artifact** (the
  e-print tarball for a LaTeX source; the PDF for a PDF-only source)
  plus its filename (`shasum -a 256 <file>`). The canonical-format
  record disambiguates which artifact the hash is of. The hash and
  publication data are tracked; any copy re-verifies against them.
  `just resources-verify` re-checks every entry's recorded hashes
  against the vendored files mechanically.
- **Section map** — a location→content map anchored to lines in the
  vendored readable copy (`l.NNN` into the `.tex`/`.pdftext`), with a
  jump note (`sed -n 'A,Bp' <file>`). Map **depth tracks the
  source's load**: a full line-anchored map for a load-bearing or
  mechanization-target source, a short outline for a background
  reference. A load-bearing citation resolves at `<file>:LINE`, not
  "Definition 1, §2".
- **Content digests** — the layer between the map and the source:
  statement-level digests of the load-bearing items, in the source's
  own terms and notation, each carrying its map anchor — so a reader
  can *use* a definition or theorem (its hypotheses, its shape)
  without opening the vendored copy. **Digest depth tracks the
  source's load**, like the map's: statement-level for the parts a
  development leans on, a few sentences per section for background
  parts, absent for a shelf reference. Digests state what the source
  states — never what any development has done with it.
- **What the source establishes** — the source's actual deliverables
  and their status in the field, compactly. Entries record what the
  source states, not what anyone has proven from it: every
  mathematical claim here is CONJECTURED until machine-checked.

The depth standard: a full line-anchored map with content digests
for an implemented or load-bearing source, a one-line outline for a
background reference. The exemplar entry is `resources/rijke-hott/`.

## Acquiring documents

When a load-bearing claim rests on a source not yet vendored, the
default action is to ingest it (ingest-on-firsthand-need), producing
a PROVISIONAL entry — not merely to propose a candidate. Fetch by
stable identifier: for an arXiv source, `curl
https://arxiv.org/e-print/<id>` for the canonical LaTeX-source
tarball and `https://arxiv.org/abs/<id>` for metadata (the
paper-search capability maps this; feynman alpha is not relied on);
otherwise the source's stable URL or a user-supplied file. **Record
the fetch URL in the entry** whenever a known URL sourced the
artifact — binding for PDFs, whose only stable identity otherwise is
the hash. Compute the sha256 of the canonical artifact and record
it; for an existing entry, check it against the recorded hash before
citing from the local copy (`just resources-verify` runs this check
over the whole tree). A hash mismatch is a FATAL finding: stop and
resolve which document the entry describes before citing anything.

An agent may ask to vendor a source at any time, especially when a
construction under development draws on it. Workflows also propose
candidate entries in their provenance sidecars; a PROVISIONAL entry
becomes vetted at the human confirmation step.
