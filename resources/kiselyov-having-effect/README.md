---
artifact: having-effect.html
sha256: 232d484bc9dee356cf184715b737c87471839f0e14da68fd619ba6637820828e
format: html
fetch-url: https://okmij.org/ftp/Computation/having-effect.html
version: September 2017
fetched: 2026-07-28
---

# Kiselyov — Having an Effect

A reconstructed talk on the nature of computational effects. The
thesis: an effect is an interaction of an expression with its
context. The talk demonstrates that denotations become unstable
when a language grows, reconstructs Cartwright and Felleisen's
Extensible Denotational Language Specifications as the repair, and
extends it: expressions send requests to handlers, handlers are
localized parts of the program rather than a central authority, and
variable dereference and closure formation are themselves effects
(`ReqVar`, `ReqClosure`). The stated slogan for the handler
discipline: what one cannot handle gets sent to a superior.

Load declaration: background reference, held at outline depth. The
source of the effects-as-interactions vocabulary and the
variables-as-requests reading.

## Citation

Oleg Kiselyov. *Having an Effect*. Web essay reconstructing a talk,
okmij.org. First presented at the Indiana University SoIC Computer
Science Colloquium, 25 August 2016, and at the HOPE workshop, ICFP
2017. Page version: September 2017.
URL: https://okmij.org/ftp/Computation/having-effect.html

The reconstructed source is: Robert Cartwright and Matthias
Felleisen, "Extensible Denotational Language Specifications",
Theoretical Aspects of Computer Software, 1994 (cited at l.514 of
the page). That paper is not vendored here; it is its own candidate
entry.

## Vetting

PROVISIONAL. Directed agent ingestion, 2026-07-28, from a single
fetch of the live page. No statement audit is recorded, so the
entry supports no load-bearing citation.

## Files

- `having-effect.html` — the canonical artifact and the file the
  reader greps. HTML markup as served by the author's site. The
  page is living: it carries its own version stamp (September 2017,
  l.127), and identity is the hash plus that stamp.

## Source provenance

Fetched by agent on 2026-07-28 from the author's maintained
personal site (okmij.org) over HTTPS. No paywall. The page is a
living document, so a re-fetch can drift from the recorded hash;
the version stamp at l.127 is the drift indicator to check first.

## Section map

Outline depth. Anchors are lines in `having-effect.html`
(`sed -n 'A,Bp' having-effect.html`).

- l.84 — Introduction. Talk provenance at l.122-127.
- l.147 — Part 1, Unstable Denotations: denotational semantics
  l.151, definitional interpreters l.177, extensible interpreters
  l.265, state l.355, first-class functions l.422. The instability
  statement at l.449.
- l.454 — Part 2, Effects and Interactions: the thesis, an effect
  as the interaction of an expression with its context
  (l.454-456).
- l.529 — Part 3, Stable Denotations: towards stable denotations
  l.533, state l.653, the handler-bureaucracy slogan and the
  stated departure from Cartwright-Felleisen (no central
  authority) l.718-722, Extensible Effects l.897.
- l.916 — Part 4, Higher-order Programming is an Effect:
  `ReqVar` l.775-794, lexical scope l.801, `ReqClosure` l.840-845.
- l.1006 — Conclusions.

## Content digests

- Thesis (l.454-456): unstable denotations reflect the
  interactions of an expression with its context. An effect is
  such an interaction.
- Variables as requests (l.775-778): `var v` denotes the request
  `Req (ReqHO (ReqVar v)) Done`, sent to a handler that holds the
  environment. Dereferencing a variable is an effect.
- Closures as requests (l.840-845): `lam v body` denotes
  `Req (ReqHO (ReqClosure v body)) Done`, so closure formation is
  an effect uniformly with variable dereference.
- Handler discipline (l.718-722): handlers are localized parts of
  the program, a bureaucracy, and unhandled requests propagate
  upward. Stated as a departure from Cartwright-Felleisen, where
  the authority is stationed outside the program.

## What the source establishes

A reconstruction argument, not theorems: that naive denotational
semantics loses stable denotations under language extension, that
the Cartwright-Felleisen request discipline restores them, and
that variables and closures fit the same request form. As claims
about semantics these are CONJECTURED here until something is
machine-checked against them.
