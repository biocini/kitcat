# Kitcat

An experiment with univalent programming and open source mathematics in cubical Agda.

> **WIP** — API is unstable. Expect breaking changes.

## Contents

Kitcat will be host to investigations at the intersection of higher catgegory
theory, homotopy type theory, rewriting theory, combinatorics, and proof
theory. The library is intended to be a testbed for new ideas in these areas,
as well as a reference for formalized mathematics and an ergonomic environment
for functional programming.

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
  from `Lifting.Construction`/`Lifting.Monad`; `Core.Set.Omega` follows
  `UF.SubtypeClassifier`; `Core.Retract` follows `UF.Retracts`;
  `Core.Discrete` follows `UF.DiscreteAndSeparated`; and
  `Core.Function.Embedding` adapts `UF.LeftCancellable`
- [**agda-prelude**](https://github.com/UlfNorell/agda-prelude) (Ulf Norell,
  MIT) — `Core.Function.Base` and `Core.Trait.Ord` are adapted from
  `Prelude.Function` and the prelude's ordering conventions
- [**TOTBWF's Segal conditions gist**](https://gist.github.com/TOTBWF/018347c1ef1da6cd9e7a43f2e4295513) —
  `Lib.SSet.Base`, `Lib.SSet.Segal`, and `Lib.CSet.Base` adapt the simplicial
  set and Segal condition definitions

The primary HoTT reference used throughout is Rijke's _Introduction to Homotopy Type Theory_.

## Related work

- [1lab](https://1lab.dev/) — Formalised mathematics as explorable reference,
  to whom this library is much indebted
- [agda-unimath](https://unimath.github.io/agda-unimath/) —
  Univalent foundations at scale
- [agda-categories](https://github.com/agda/agda-categories) —
  Category theory library for Agda
