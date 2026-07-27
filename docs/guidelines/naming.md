# Naming

- **Kebab-case, capitalization by role**: predicates and proofs are
  lowercase (`is-contr`, `left-cancellable`), including predicate
  records (`is-equiv`). Bundled structures, classifiers, and traits
  are capitalized (`Monoid`, `Lift`, `nType`). No camelCase.
- **Conversion lemmas are `source→target`** with the arrow in the
  name: `is-contr→is-prop`, `iso→equiv`, `path→square`.
- **Law vocabulary compresses to one token**, with trailing `l`/`r`
  for sidedness and no hyphen: `unitl unitr invl invr assoc comm
  idem cancell cancelr zeror`. Composite descriptors hyphenate:
  `ap-comp`, `fiber-comp`, `transport-∙`.
- **Lemma families live in namespace modules. Case marks the
  kind**: lowercase modules are operation families
  (`module add` → `Nat.add.unitr`, `module pcom`, `module transp`).
  Capitalized modules are type/subject interfaces
  (`module Equiv (e : A ≃ B)`, `module Emb`, `module Path`).
  Members are short names built for qualified access: `set : is-set
  Nat` consumed as `Nat.set`, never re-prefixed (`set`, not
  `nat-set`). The `∂`-namespace for interval combinators
  (`src/Core/Base.lagda.md:73-120`) is the same instinct at the
  symbol level.
- **Instances are `Class-Type`**: `Underlying-Σ`, `Discrete-Nat`.
  Superclass fields likewise (`Semigroup-Monoid`).
- **Variables**: `x y z w` for elements, `p q r s` for paths,
  `α β` for higher cells, `i j k l` for interval variables (hcom
  binders take the next free letter), `φ` for face formulas,
  `A B C` for types. Levels (ruled 2026-07-13): `u v w` for
  `Level`. `ℓ` remains reserved for interval-indexed levels
  `ℓ : I → Level` (`src/Core/Base.lagda.md:33-34`). Core's
  `ℓ ℓ'`-for-`Level` minority sites are baseline, not precedent.
  In `Cat.*`, the domain names `o` (object level) and `h` (hom
  level) are the rule for category-shaped records (ruled
  2026-07-13). Auxiliary levels there follow the general rule.
