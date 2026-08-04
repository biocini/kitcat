# Core.Rx — remaining work

Formalisation of Sterling, *Reflexive Graph Lenses*. This tracks what is not yet
done. Difficulty tags: `[easy]` mechanical, `[mod]` a real but bounded proof,
`[hard]` open-ended cubical work.

## Current state

- **Type** — `reflexive-graph`, `reflexive-graphᴰ`.
- **Base** — `module rx (G)`, the one interface keyed on a base graph, spanning
  both forms: `vfam`/`efam`/`disp`/`diag`, `tensor` (`:= ∐`), `cotensor`
  (`:= ∏`), fans, `op`, `is-univalent`/`-op`, `to-edge`, `hom`, and the nested
  `(D)` block — `total`/`total-op`, `component`, `is-cov/ctrv-fibration`,
  `cov/ctrv-fibration` push/pull — plus `binary-product`, `comprehension`,
  `constant`. Free-standing (keyed on a type or family, not a base): `product`,
  `coproduct`, `discrete`, `codiscrete`, `image`, `is-univalent-family`,
  `is-path-objects`, `is-displayed-univalent`.
- **Properties** — `module po (G)`, the univalence calculus of a fixed graph
  (`edge-idsys`, `edge≃path`, `is-univalent→to-edge-equiv`/`←`,
  `is-univalent→op`/`is-univalent-op→`, `cofan-idsys`, `op-path-object`,
  `is-univalent-is-prop`); it does not re-export `rx`. Free-standing: the
  univalent-family characterisations and the full closure set — `total-`,
  `disc-`, `codisc-`, `const-disp-`, `bin-prod-`, `prod-`, `coprod-`, `tensor-`,
  `cotensor-`, `compr-path-object`, `is-displayed-univalent-is-prop`.
- **Lens** — `oplax-cov-lens`, `lax-ctrv-lens`, `unbiased-lens` with displays;
  `cov-disp-path-object`, `ctrv-disp-path-object`, `unb-disp-path-object`; `tot-op-lens`, `tot-op-lens⁻`,
  `display-of-tot-op`; `cov-`/`ctrv-lens-to-unbiased`; `component-path-object`;
  `cov-`/`ctrv-`/`unb-lens-structure-is-prop`; `cov-`/`ctrv-flatten` with their
  path-object certificates.
- **Fibration** — `cov-`/`ctrv-fibration-path-object`, `fibration-duality`(`⁻`);
  `module cov-straightening` (`straighten-equiv`, `straighten`, `unstraighten`,
  `underlying-lens`, `edge-ids`/`vert-ids`); `cov-`/`ctrv-lens-to-fibration`, the
  universal-transport ↔ componentwise-univalence pairs, and
  `component-of-display`/`underlying-lens-of-display`.
- **Univalent** — `display-of-underlying-lens`, `characterisation-of-fibs` and
  its contravariant form. The `--cubical` module: a proof belongs here exactly
  when it appeals to `ua` or consumes something that does.
- **Classify** — over a univalent family `(U , E)`: `gph-on`/`gph-lens`/`Gph`,
  `rx-on`/`rx-lens`/`RxGph`; over a fixed base `gA`: `realize`/`CovLensStr`/
  `lens-of-lenses`/`cov-lens-over`, and `DGphOn`/`DGph-lens`/`DGph`,
  `DRxOn`/`DRx-lens`/`DRxGphOver` — each construction with its path-object
  certificate.
- **Poly** — `cov-poly`/`ctrv-poly` (covariant/contravariant partial products)
  with their path-object certificates, over a transport unital up to a path; and
  `pmc⁺`/`pmc⁻`, the partial map classifier of a dominance (a `Poly` application
  over the codiscrete family on `T`, base `image T`).
- **Classify** (case studies) — `binop±`/`binop-lens`/`BinOp`/`Magma`: the
  reflexive graph of `U`-small magmas, the example that motivates the unbiased
  lens (its homomorphism edge is mixed-variance, from neither biased lens); and
  `𝔹Σ₂`/`E₂`/`hUP⁺`/`hUP⁻`, homotopy unordered pairs (a `Poly` application over a
  comprehension of the universe by a truncation). Each with its path-object
  certificate.
- **Simplex** — `AugSpx`, the reflexive graph of augmented simplices (naturals
  as vertices, monotone equivalences of finite ordinals as edges), with its
  univalence from gauntness; and `List⁺`/`List⁻`, lists valued in a path object
  as the partial products of `AugSpx` with the finite-ordinal family `𝔉`, with
  their path-object certificates.

## 1. Univalence-preservation closures → `Properties` — DONE

`const-disp`, `bin-prod`, `prod`, `coprod`, `tensor`, `cotensor`, `compr` — all
`-path-object` closures are formalised. `comprehension` requires each `P x` to be
a proposition (the construction itself is defined for arbitrary `P`).

## 2. Lens structure uniqueness → `Lens` — DONE

All three structures are propositions over a path object: `cov-`, `ctrv-` and
`unb-lens-structure-is-prop`. Each distributes the structure over the base
vertices, curries the transport onto the fan of `x`, and evaluates at the
contractible fan's centre (`Π-contr-dom`, `Σ-equiv-fst`); what is left is the
cofan — for the lax contravariant lens, the fan — of the identity in
`B.vtx x ⋔ B x`. In the unbiased case both injections collapse, the lax unitor
pairs the right one into the fan of the identity, and contracting that fan leaves
the mid unitor as the cofan; its hypothesis names the diagonal components only,
which `component-path-object` shows to be the condition on all of them.

## 3. Fibrations → `Fibration`, `Univalent` — DONE

`characterisation-of-fibs`: lenses of path objects over `G` are equivalent to
covariant fibrations over `G`, with no univalence assumed of `G`. Beneath it,
fibrations are path objects, the total opposite exchanges the two variances,
universal transport and componentwise univalence agree, and straightening is an
equivalence (`based-singl-contr→Ids` presents both edge families as based
identity systems over the pushforward, so each is the path type out of it).

Both roundtrips come out as identifications, so Sterling's route through
univalence of `DRxGphOver` and `CovLensOver` is unnecessary and §4 gates nothing.
Only `display-of-underlying-lens` needs `ua`: its two edge types differ in an
argument of `G.edge x y` against `G.rx y`, which no `ap` reaches. The reverse
roundtrip moves within one family — the cofan identity system supplies
`u ≡ push (rx x) u` and `ap` carries the edges along it — so
`component-of-display` and `underlying-lens-of-display` stay erased.

`straighten` is built from `Ids-based→equiv⁻`, whose forward map is `to-path`,
precisely so that it reduces to `subst (D.edge (G.rx y) (push p u)) …`; the
unitor coherence is stated against that normal form.

Both variances are proved; `ctrv-characterisation-of-fibs` reads each side
against the opposite base, where opposition is involutive on reflexive graphs,
displayed ones and both lens flavours, so only the componentwise univalence
proofs need adjusting and those are propositions.

## 4. Classifying path objects, SIP, case studies → new modules

Sterling's own case study, wanted for the classifying path objects and their
applications rather than for §3. `image`, `is-univalent-family`, `Gph`, `RxGph`,
`realize`, `CovLensStr`, `lens-of-lenses` and `cov-lens-over` are formalised in
`Classify`.

Endpoint convention: a constructed graph's `edge` computes, normalising its
endpoints into projection position where unification cannot recover them (the
dual of the edge transparency that carries the definitional unit laws). Whether
an endpoint survives is a property of the base. `discrete`, `image`, `product`
(hence `cotensor`), `op` and `AugSpx` retain theirs; `coproduct` (hence
`tensor`) buries the source fibre vertex under a transport, `comprehension`
discards the predicate components, `codiscrete` retains nothing, and `total`
inherits the failure from either factor — so every classifier, every polynomial
and `𝔹Σ₂` are bases at which an implicit endpoint does not solve. Over `Gph` the
target is the lost one, `gph-lens` reindexing it through `has-pull`, so it
appears applied to `p .fst x` rather than to a bound variable.

The whole edge-indexed API therefore names endpoints **explicitly**:
`reflexive-graphᴰ.edge`, `rx.hom.emap`, `rx.efam`, `rx.is-cov`/`ctrv-fibration`
with their push/lift and pull/colift operations, `rx.univalence.to-id`/`concat`/
`inv`, the `push`/`pull` synonyms behind `oplax-cov-lens.has-push` and
`lax-ctrv-lens.has-pull`, `universal-push`/`universal-pull`, `cov-straightening`'s
`edge-ids`/`straighten-equiv`/`straighten`/`unstraighten`, `component-path-object`,
and `unbiased-lens`' `linj`/`rinj`/`munitor`/`runitor`. A field additionally
cannot do otherwise: a type-synonym field auto-introduces its implicits and
cannot be re-bound by name.

Endpoints stay implicit exactly where another argument pins them rigidly —
`reflexive-graphᴰ.rx` and both lens unitors, pinned by `vtx x`; `rx.to-edge`,
whose argument is a path and so rigid in the vertices at every base.

Total opposition exchanges the endpoints: `tot-op-lens L .has-pull x y p` is
`has-push L y x p`, and `fibration-duality` transposes the same way.

`lens-of-lenses`' unit laws are `refl`: `f`'s vertex map and fibrewise edge
equivalence reduce to the identity at reflexivity (`RxGph.rx … .fst .fst .fst`
through `𝒰.rx = aut`, `aut .fst = id`), and Σ has η, so both injections compute
to the identity on an opaque argument — Sterling's definitional unit laws,
intact.

`DRxGphOver` is formalised — the two-stage `DGph` then `DRxGphOver`, parallel to
`Gph`/`RxGph` one level up: `DGph` classifies displayed-graph structures over `gA`
(a lax contravariant lens reindexing displayed edges along a fibrewise vertex
equivalence), `DRxGphOver` adds displayed reflexivity data by an unbiased lens.
The definitional unit laws hold as before.

Partial products are formalised in `Poly`: `cov-poly`/`ctrv-poly` and their
path-object certificates, over a transport (`push`/`pull`) unital *up to a path* —
the formalisable proxy for Sterling's definitional lens, since a general lens'
unitor is only an edge and `c` acts on vertices alone. The polynomial is a path
object whenever the base and `C` are, with no condition on `B`.

`Magma`/`BinOp`, homotopy unordered pairs (`hUP⁺`/`hUP⁻`), partial map
classifiers (`pmc⁺`/`pmc⁻`), and augmented simplices with lists (`Simplex`) are
formalised.

Augmented simplices rest on the gaunt fact, which lives in
`Core.Data.Fin.Monotone.Gaunt`: `mono-unique` (a monotone equivalence of finite
ordinals is determined by its underlying map) and `mono-card`
(`Fin m ≃ Fin n` monotone forces `m ≡ n`). Both come from one observation at the
level of the underlying naturals — a monotone equivalence is inflationary,
`lower i ≤ lower (f i)`, on the map and its inverse alike, so `lower (f i) ≡ lower i`
pins the action exactly. The irrelevance-wrapped bound is recovered relevantly
because `<` on the naturals is decidable: `Core.Data.Irr.out-dec` turns
`Irr A` into `A` against a decision, giving `Core.Data.Fin.Properties.bound`
(`(i : Fin n) → lower i < n`) and the order recovery in `Gaunt`. Supporting Nat
lemmas `≤-antisym`, `<-dec`, `≤-dec` are in `Core.Data.Nat.Properties`.

The definitional lens `𝔉` is realised: `push`/`pull` are the underlying map of a
monotone equivalence and its inverse, and the unit law holds on the nose
(`push-rx = refl`) because the reflexive edge is the identity equivalence.

A *definitional lens* — one whose unit law holds on the nose, so the unitor is
the component's own reflexivity — is not formalisable as a type: Sterling states
it judgementally and notes that definitional equality is not expressible in
MLTT. It is a shape lenses are built in, and `gph-lens` and the flattened lenses
are already in it; nothing is owed here.

## Parameter convention

A parameter is implicit exactly when every use site recovers it. Record-headed
arguments recover theirs — `rx.disp G v' e'`, and the three lens records — so the
base is implicit wherever a display or a lens is the principal argument
(`total-path-object`, `cov`/`ctrv`/`unb-disp-path-object`, the flattenings, the
total-opposite family, `Fibration`'s lens block, `is-displayed-univalent`).
A Π-domain recovers its parameter when the argument is a named family, which is
why `image`, `is-univalent-family`, `is-path-objects` and the `Classify`/`Poly`
index types hide it, and why `product`/`prod-path-object` cannot — their family
arrives as a lambda and the result type buries both under projections. Anything
reachable only through a projection is never recovered: `rx.vfam` and `rx.efam`
unfold to functions out of `reflexive-graph.vtx G`, so a family never determines
its base and every family-keyed signature names it.

Declarations with no principal term argument keep their parameters: the lens type
formers, and `cov`/`ctrv`/`unb-lens-structure-is-prop`.

Levels lead and are explicit exactly where un-inferable — `vfam`/`efam`/`disp`,
`dep-rx`, and `Univalent`'s four `*-of-path-objects` types.

## Loose ends

- The `All.lagda.md` aggregator is retired pending module-organisation decisions
  (does `Bb.CatsWithExplicitInterchange` belong in it?). Whole-library check
  is `just check-tree` (a parallel `fd … -x agda` sweep); do not run
  `bin/sync-all` meanwhile.
- [ ] `rst-disp` — restriction of an iterated displayed reflexive graph.
- [ ] Full `path-alg-toolkit` / `pre-ct-is-equiv` — `edge≃path` covers the
      downstream needs so far; complete if a later proof requires it.
- [ ] `prop-image` — the image of a family of propositions, edges the
      biimplications, together with its agreement with `image` on such a family.
      The agreement needs a biimplication-to-equivalence combinator, which Core
      does not have.
