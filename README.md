# Kitcat

An experiment with univalent programming and open source mathematics in cubical Agda.

> **WIP** — API is unstable. Expect breaking changes.

## Contents

Kitcat is a research library at the intersection of higher category
theory, homotopy type theory, and programming language foundations,
written in Cubical Agda. It is a testbed for new ideas in these
areas, a reference for formalized mathematics, and an ergonomic
environment for functional programming, with machine-checked proof
as its standard of evidence.

## Research provenance

This repository is developed with substantial AI assistance under
the direction and review of its human owner, and aims to be an
exemplar of transparent, ethical AI-assisted mathematics research:
machine-checking is the trust boundary for mathematical claims,
references are human-vetted before anything rests on them, and AI
contributions are disclosed. [`docs/provenance.md`](docs/provenance.md)
is the binding standard.

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
- among other references

## Acknowledgments

Kitcat incorporates and adapts code from the following projects:

- [**1lab**](https://1lab.dev/) (Amélia Liao et al., AGPL-3.0) — Definitions and
  proofs across `Core.Function.Embedding`, `Core.HLevel`, `Core.Trait.Trunc`,
  `Core.Data.Fin`, `Core.Path`, and `Core.Transport.Properties` are derived from
  or influenced by 1lab's formalizations
- [**TypeTopology**](https://github.com/martinescardo/TypeTopology) (Martín
  Escardó et al., GPL-3.0) — `Core.Function.Partial` adapts the lifting monad
  from `Lifting.Construction`/`Lifting.Monad`; `Core.Retract` follows
  `UF.Retracts`; `Core.Discrete` follows `UF.DiscreteAndSeparated`; and
  `Core.Function.Embedding` adapts `UF.LeftCancellable`
- [**agda-prelude**](https://github.com/UlfNorell/agda-prelude) (Ulf Norell,
  MIT) — `Core.Function.Base` and `Core.Trait.Ord` are adapted from
  `Prelude.Function` and the prelude's ordering conventions
- [**TOTBWF's Segal conditions gist**](https://gist.github.com/TOTBWF/018347c1ef1da6cd9e7a43f2e4295513) —
  simplicial-set and Segal-condition definitions were adapted for an
  earlier development, currently parked in `Stash/`

The primary HoTT reference used throughout is Rijke's _Introduction to Homotopy Type Theory_.

## Related work

- [1lab](https://1lab.dev/) — Formalised mathematics as explorable reference,
  to whom this library is much indebted
- [agda-unimath](https://unimath.github.io/agda-unimath/) —
  Univalent foundations at scale
- [agda-categories](https://github.com/agda/agda-categories) —
  Category theory library for Agda
