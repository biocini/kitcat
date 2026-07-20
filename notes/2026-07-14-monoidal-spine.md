# Session log — 2026-07-14 — monoidal spine

Objective: review and re-architect `Cat.Type`; then carry the representable-embedding
construction through the standard category-theoretic library (limits, functors,
monoidal structure), and investigate the product of wild categories.

## What was done

### Review and refactor of `Cat.Type`

- Full API review of the wild-category presentation (reflexive graph + representable
  embedding `emb` into two-sided *composites*, with `interchange♭`, `spine-contr`,
  `unit` as axioms). Verdict: construction sound; `Cat.Groupoid` confirms the
  "no hidden truncation" claim (path groupoid of an arbitrary type inhabits the axioms).
- `Rx` renamed to `reflexive-graph`; the operator layer was factored into a
  pre-record `representable` module parameterized by `(S , emb)` alone, so instances
  no longer duplicate `pre/post/sub/cosub/·/·ᵒᵖ/·'/·''`.
- **Interchange experiment** (run both ways, then reverted): made the ternary
  `interchange` the record field and derived `interchange♭` by two J's
  (`interchange♭-from`). Migration cost: three repairs in `Cat.Coherence` (an
  `interchange♭-op` lemma and two `J-refl` steps) because the library's `J` computes
  on `refl` only propositionally (`J-refl = transport-refl`). Conclusion, agreed with
  Lane: **flat `interchange♭` as the field** has strictly better computation
  (fields are neutrals; closures hit the J lottery), with `interchange♭-from` kept
  in `representable` as instance sugar.
- Naming: `⟨_,_⟩` (uniqueness of representatives) replaced by the `repr-*` family:
  `repr-unique` (sole `-unique` lemma), `repr-lc`, `repr-refl`, `repr-cast`,
  `repr-ap`, `repr-∙`, `⊳-repr`, plus `repr-op`, `repr-sym` in `Cat.Coherence`.
  Brackets freed for the product API.

### Module distribution and library build-out

- Split: `Cat.Type` (interface), `Cat.Op` (duality, `op-invol` definitional),
  `Cat.Theory` → later renamed **`Cat.Base`** (derived theory: embedding equivalence,
  `_⨾_`, `assoc`/`unitl`/`unitr`, `repr-*`, witness API `_⨾_=>_`/`cast-path`).
  2-cell seeds (`●-coh`, `ι-mult-*`, `interchange-natural`) evicted to `Cat.Coherence`.
- New modules, all checking: `Cat.Morphism` (whiskering, sections/retractions,
  mono/epi, neutrality), `Cat.Morphism.Iso` (isomorphisms, biinv, inverse
  uniqueness), `Cat.Limits.{Terminal,Product,Coproduct,Equalizer,Pullback}`
  (universal properties as contractible cones, β/η/ind, uniqueness up to iso),
  `Cat.Functor`, `Cat.Functor.{NatTrans,Adjoint}`. The stale `Cat.Base` content was
  fully absorbed; `All.lagda.md` and old `Cat.Base` rehabilitation deferred per Lane.
- Duality as theorems: `is-terminal C T ≡ is-initial (op C) T` (definitional);
  `is-coproduct C ι₁ ι₂ ≃ is-product (op C) ι₁ ι₂` (via fiberwise cone equivalence,
  `interchange` mediating the two composite orders).

### Monoidal categories — the central construction

- Lane's direction: ternary tensor primitive in the *uncurried* new style, not
  delooping, not the older curried record, and not my multihom/promonoidal proposal
  (which had a cartesian trap: `Nat(よx × よy, よz)` presents `x × y`, not `x ⊗ y`).
- `src/Cat/Monoidal.lagda.md` delivers the full two-level record:
  `tensor-virtual` (`⊗composite = C.ob × C.ob → C.ob`, `⊗ev`),
  `tensor-representable` (operators + `⊗interchange♭-from`),
  `record monoidal (C : category o h)` with fields `I`, `⊗emb`,
  `⊗interchange♭` (flat), `⊗spine-contr` (full packed spine with 2-cell), `⊗unit`
  (evaluation at the identity context — **no is-equiv pair**: absorption and the
  two unit equivalences are theorems, per Lane's correction),
  plus the morphism layer `⊗hemb` (uncurried hom-context pairs), `⊗hunit`,
  `⊗hinterchange`, `⊗hbifunctor`, `⊗hspine-contr` (packed `⊗hspine` whose 2-cell
  is a PathP over the object spine's θ-square).
- Derived in `theory`: `_⊗_` as spine center, `⊗emb-comp(-op)`, absorb chain,
  `⊗is-representable-prop`, `⊗repr-unique`, `⊗assoc`, `⊗unitl/r`,
  `⊗unit-is-prop` (Kraus chain, its equivalence hypothesis demoted from field to lemma).
- Design note recorded: `⊗hbifunctor` is a field (it is the only field mentioning
  `C.⨾`; compatibility of a primitive action with vertical composition is structure,
  like `preserves-comp`); the derived `⊗ₕ-preserves-⨾` is the theorem.

### Product of wild categories — investigation and verdict

- `src/Cat/Product.lagda.md` (ternary pointwise product) built to the wall:
  `embₚ`, both interchanges, `unitₚ`, full spine center — then `spine-contr` fails.
  **Obstruction, precisely identified**: the fiber contraction needs a 2-cell
  comparing a joint path-family to its identity-context specialization; off-diagonal
  variation `Π (γD : ctxD) , R γC ≄ R γC` is unconstrained by the component axioms.
  Same wall for binary and ternary pointwise products. Module deleted on Lane's call.
- Verdict: wild categories in this presentation are not freely closed under
  pointwise products. The ternary `tensor-emb` route is the answer the library
  already ships (jointness as primitive, never split).
- **Representability spike** (`src/Test/ProductSpike.lagda.md`, checks): product as
  representing object of the joint functor-family. `is-product` record (projections +
  `pairing-equiv`, level-polymorphic); `terminal-fam-contr` (functors into `𝟙`
  contractible); unit law `is-product A terminal-category A` via `∘F-unitl`.
  The presentation characterizes the product; existence is per-instance.

## Strongest findings / decisions

1. Fields-as-neutrals beats derived-closures for computation (the interchange swap
   experiment, measured in `Cat.Coherence` repairs).
2. The erased-index trick ports the entire `Cat.Type` machinery to monoidal:
   `hom _ _ := ob`, `idn := I`, `ctx := ob × ob`, spine machinery transfers verbatim,
   including the hom level as a spine over the object spine's θ-square.
3. The unit is a field `⊗unit : ⊗emb x (I , I) ≡ x`; both is-equivs from the old
   record are derived mid-chain (absorb → funext + `aut`).
4. Product obstruction is structural (`Π` over pointed-but-wild contexts), not a
   missing lemma; the terminal unit (`𝟙`, `src/Cat/Terminal.lagda.md`, checks)
   absorbs exactly where context types are contractible.

## Failed strategies (with reasons)

- Multihom/promonoidal for monoidal — works, but strictly heavier than the
  ternary-tensor construction Lane had already proven in `backup/Monoidal`.
- Naive `bihom (x y) z = Nat(よx × よy, よz)` — builds the *cartesian* tensor
  (shared contravariant variable = diagonal).
- Ternary field for interchange (reverted; computation).
- `Σ i , is-equiv × is-equiv` unit for monoidal (old curried style; new style
  derives the equivalences).
- Pointwise and ternary-pointwise product categories (off-diagonal variation).

## Verification state

All of the following pass `just check <module>` (Agda 2.9.0, `--safe --erased-cubical`):

- **verified**: `Cat.Type`, `Cat.Op`, `Cat.Base`, `Cat.Morphism`, `Cat.Morphism.Iso`,
  `Cat.Limits.Terminal`, `Cat.Limits.Product`, `Cat.Limits.Coproduct`,
  `Cat.Limits.Equalizer`, `Cat.Limits.Pullback`, `Cat.Functor`,
  `Cat.Functor.NatTrans`, `Cat.Functor.Adjoint`, `Cat.Coherence`, `Cat.Groupoid`,
  `Cat.Terminal`, `Cat.Monoidal`, `Test.ProductSpike`.
- **blocked (partial)**: `src/Cat/Monoidal/Bifunctor.lagda.md` — compiles up to
  `extend-θ`: the `hfil` square for the spine extension fails its face check with
  `⊗interchange♭ _ _ i (l , r)` vs `⊗emb x (⊗sub y (l , r))` (metas in the display).
  `hfiber-contr`, `⊗ₕ-preserves-⨾` sit downstream of it.
- **unverified artifact**: `src/Test/Probe.lagda.md` — debugging probe reproducing
  the same face mismatch (`probe-face` fails); not library code.

Open obligations: the `extend-θ`/`extend-q`/`hfiber-contr` chain (the bridge from
p-only fiber to packed `⊗hspine`); then `⊗ₕ-preserves-⨾`; then monoidal coherence
(pentagon/triangle), `htensor` unit/naturality, braided story, and the deferred
`All.lagda.md` + old-`Cat.Base` plan.

## Open questions / risks

- The `extend-θ` face mismatch: the record's derived `⊗interchange` should
  endpoint-reduce at `i0` (probe confirms it does in isolation), but inside the
  `hfil` boundary check the interchange♭ application appears with metas and does not
  reduce. Likely needs a different 2-cell construction (square from the object θ₀'s
  filler, or reformulating `extend-q` so the cap is definitionally the q-side).
- Whether `is-product` existence is provable for any library instance beyond `𝟙`.
- How much of `backup/Monoidal/{Coherence,Hexagon,Braid,Twist}` ports — the
  `absorb-coh` layer is known-irreducible there and presumably here too.

## Next steps

1. Fix `extend-θ` (try: build the square as the object θ₀'s hom-lift rather than a
   hand-rolled `hfil`, or state `extend-q` independently and fill the square by
   `PathP`-composition), then `hfiber-contr`, then `⊗ₕ-preserves-⨾`.
2. `Cat.Monoidal.Coherence` (pentagon from the E₄ fiber + `⊗is-representable-prop`).
3. Bifunctor as a natural map of joint functor-families (bridges the
   representability reading and the tri-level tensor).
4. The `All.lagda.md` / old-`Cat.Base` planning conversation (still deferred).

## Artifacts

- Library: `src/Cat/{Type,Op,Base,Morphism,Coherence,Groupoid,Terminal,Monoidal}.lagda.md`,
  `src/Cat/Morphism/Iso.lagda.md`, `src/Cat/Limits/{Terminal,Product,Coproduct,Equalizer,Pullback}.lagda.md`,
  `src/Cat/{Functor,Functor/NatTrans,Functor/Adjoint}.lagda.md`,
  `src/Cat/Monoidal/Bifunctor.lagda.md` (blocked, WIP).
- Spikes/probes: `src/Test/ProductSpike.lagda.md` (checks), `src/Test/Probe.lagda.md`
  (debugging artifact, fails as designed).
- Deleted: `src/Cat/Product.lagda.md` (pointwise product WIP).
- Reference: `src/Cat/backup/Monoidal.lagda.md.bak` and `src/Cat/backup/Monoidal/*`
  (the earlier curried monoidal development used as port source).

No external sources were consulted this session.
