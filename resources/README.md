# resources/ — vetted source references

Each entry is one source (paper, book chapter, thesis, slide deck,
web reference) in its own directory: `resources/<slug>/`.

An entry directory is self-contained: its README.md carries
everything needed to cite and audit the source, and entries
reference at most other entries in this tree — never files elsewhere
in the repository — so an entry stays a reliable citation target as
the repository changes around it.

## Entry format — `resources/<slug>/README.md`

- **Citation** — full bibliographic record: authors, title, venue,
  year, DOI or arXiv id, URL.
- **Vetting** — who opened the document and when, and what it was
  checked to say. An entry exists only after a human has opened the
  document.
- **Document hash** — sha256 of the vendored file plus its filename
  (`shasum -a 256 <file>`). Document files are vendored locally next
  to the README and are gitignored; the hash and publication data
  are tracked, so any copy can be re-verified against the record.
- **Summaries** — content summaries, section maps, key definitions
  and theorem statements with their locations in the document.
  Entries record what the source states, not what the repository has
  proven: every mathematical claim recorded here is CONJECTURED
  until machine-checked.

## Acquiring documents

Fetch by stable identifier (arXiv id, DOI) with the paper-search or
url-fetch capability (`.agents/skills/kitcat/HARNESS.md` maps
these), or accept a user-supplied file. In both cases compute the
sha256 and check it against the entry's recorded hash before citing
from the local copy. A hash mismatch is a FATAL finding: stop and
resolve which document the entry describes before citing anything.

Workflows propose candidate entries in their provenance sidecars;
entries are created deliberately by a human-approved vetting step,
never as a side effect of a run.
