# Kitcat

An experiment with univalent programming and open source mathematics in cubical Agda.

> **WIP** — API is unstable. Expect breaking changes.

## Contents

Kitcat is a research library at the intersection of higher category
theory, homotopy type theory, and programming language foundations,
written in Cubical Agda. It is a testbed for new ideas in these
areas, a reference for formalized mathematics and type theory with
machine-checked proof as its standard of evidence.

## Research provenance

This repository is developed with substantial AI assistance under the direction
and review of its human owner, and aims to be an exemplar of transparent
AI-assisted mathematics research. As such, it is a living entry into the
conversation about ethical practice in this domain. Machine-checking is the
trust boundary for mathematical claims, and references are human-vetted before
anything rests on them, and AI contributions are disclosed
[`docs/provenance.md`](docs/provenance.md) is the binding standard. I will
take every opportunity to credit authorship and theoretical provenance. The
research that the library actively cites and draws upon is cataloged in the
resources directory.

This is a best-effort attempt on my part. I welcome feedback and discussion on
how to improve any aspect of the library, as well as human contributions.

## Building

Requires Agda with cubical support (no external libraries — Agda
builtins only). With [just](https://github.com/casey/just) and
direnv:

```sh
direnv allow      # puts bin/ on PATH
just check-all    # typecheck the whole library
just --list       # everything else
```

## Foundations

The category theory framework is built on a confluence of ideas from:

- [Capriotti-Kraus](https://arxiv.org/abs/1707.03693)
- [Chen](https://arxiv.org/abs/2503.05790)
- [Petrakis](https://arxiv.org/abs/2205.06651) and
- Sterling's [virtual bicategory theory](https://www.jonmsterling.com/005B) &
  ([reflexive graph lenses](https://arxiv.org/abs/2303.10986))
- among other references (see: resources directory)

## Acknowledgments

While many lemmas are original (I've rewritten the Core library several times
in the course of development), Kitcat has adapted or otherwise drawn upon code
from the following projects, which are exemplars of open source mathematics and
deserve ample credit for their contributions to the corpus of Homotopy Type
Theory and Univalent Foundations. They are excellent, go look at them.

- [**1lab**](https://1lab.dev/) (Amélia Liao et al., AGPL-3.0) — Definitions and
  proofs across `Core.Function.Embedding`, `Core.HLevel`, `Core.Trait.Trunc`,
  `Core.Data.Fin`, `Core.Path`, and `Core.Transport.Properties` are derived from
  or influenced by 1lab's formalizations
- [**TypeTopology**](https://github.com/martinescardo/TypeTopology) (Martín
  Escardó et al., GPL-3.0) — `Core.Function.Partial` adapts the lifting monad
  from `Lifting.Construction`/`Lifting.Monad`; `Core.Retract` follows
  `UF.Retracts`; `Core.Discrete` follows `UF.DiscreteAndSeparated`; and
  `Core.Function.Embedding` adapts `UF.LeftCancellable`

The primary HoTT reference used throughout is Rijke's _Introduction to Homotopy Type Theory_, which we take as our standard reference for identifiers and structural
organization of the theory whenever possible.

## Related work not otherwise mentioned

- [agda-unimath](https://unimath.github.io/agda-unimath/) —
  Univalent foundations at scale, a lovely reference
- [agda-categories](https://github.com/agda/agda-categories) —
  Category theory library for Agda
