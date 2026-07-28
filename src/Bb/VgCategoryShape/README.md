# Bb.VgCategoryShape

## The construction

An h-category is a graph with a ternary reflection that sends its
edges into judgments. It carries one chosen edge `rx`, which fills both
argument slots. `readback` aligns the reflection with that edge,
and both cuts have representatives.

```agda
record hcategory o h : Type₊ (o ⊔ h) where
  field
    ob      : Type o
    hom     : ob → ob → Type h
    reflect : ∀ {x y} → hom x y → judgment x y             -- structure
    rx      : (x : ob) → hom x x                           -- structure
    readback : ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f -- structure
    cut⁺    : ∀ f g → is-contr (representable (composite⁺ f g))
    cut⁻    : ∀ f g → is-contr (representable (composite⁻ f g))
    unit    : (x : ob) → is-unital x
```

The two cut fields and `unit` are property. `unital e` is not a
proposition. Its second component is a path between untruncated
edges. Over the path groupoid on `S²` the fiber at `refl` is
`Ω²S² = ℤ`. The total space `is-unital x` is a proposition, so it
earns the prefix, and `Unit.unit-contr` shows it contractible. The
record extracts the unit rather than choosing it.

Four modules, and the theory runs in this order. Readback alone
gives left-cancellability, the two evaluations at the axiom, and
one unit law per hand at `rx`. The cuts give the two readings of
one reflection, and their difference gives mixed associativity. The
unit then identifies `rx` with the extracted `idn` and completes
the other two unit laws. Two theorems follow, and they are what
makes the shape. Nothing assumes interchange, the theorem
`f ⨾⁻ g ≡ f ⨾⁺ g`. Stability comes from a contractible fiber of
`cut⁻` over a point of the image, through
`image-fibers-contr→is-embedding`.

`Parity` shows why `rx` stays structure. The two-element heap
carries two h-category structures on one graph and one reflection.
They differ only in the origin. So no condition on `reflect` alone
selects the chosen edge.

## Provenance

Vendored 2026-07-28 at commit `7fae4ef`, frozen green, from an
untracked `Mag` staging directory. The staging record's module
paths read `Mag.*`, and they resolve here as
`Bb.VgCategoryShape.*`. That directory held the record while its
shape settled, and the shape did settle. The record name
`hcategory` holds. The module path does not.

Two constructions stayed unwritten when the tree froze. `Mag.Op`
worked before the record changed, and nobody rebuilt it. The route
is on record. `opᴹ` reverses `hom`, swaps the argument halves in
`reflect`, and keeps `rx` and `readback` unchanged. It exchanges
the two cuts through the argument-swap equivalence. Its one
obstacle is the `unit` clause. That clause needs
`idn ⨾⁻op idn ≡ idn`, and `⨾⁻op` does not reduce to `⨾⁺`, because
the centre of `is-contr-equiv` goes through `Equiv.inv`.
Contractibility supplies it instead, through `ap fst` of the
negative cut's own path at `idn ⨾⁺ idn`, composed with `idem⁺`.
The second construction is the promotion out of `Mag.*`, which
waits on the re-founding below.

The tree arrived with a `TODO.md`, converted into this README on
2026-07-28.

## Relationships

The `Mag` rebuild starts fresh at `src/Mag`, and the re-founding
program below is its program of record.

The claim: `hcategory` is, in substance, the wild depolarization
theorem. Sterling's `Depolarization` in
`~/TypeTopology/source/Duploids` is the set-level shadow, where a
depolarized deductive system is a precategory. `Base` already
proves the wild counterpart pointwise. Interchange, all four unit
laws, and stability are theorems there. So the two hands agree, and the
carrier is unital and associative. The theorem form is what the
tree lacks, and the route is a re-founding rather than a record
edit.

The mechanism is the balanced layer of `Cat.Logic`, investigation
line 5 in `src/Cat/Logic/TODO.md`. With both cancellation orders
each hand is two-sided unital with its own twist as unit. That is
two unital magmoids on one graph, offset by the double twist. At
θ² = id the two magmoids merge, and the merged object is
`hcategory`. The target, then:

- `hcategory` re-derived as the balanced layer at θ² = id, over
  a deductive system.
- `readback` becomes the balanced layer's cancellation data.
- `rx` becomes the merged twist. `reflect` stays carrier
  structure, the cuts become the composability tiers, and `unit`
  follows from the revived unit laws.
- The theorem: framing-trivial balanced deductive systems are
  h-categories, and conversely.

Against `Cat.Logic`, at the weak stratum this archive holds as
`Bb.WeakDeductiveSystem`:

|  | `virtual-graph` + `is-deductive-system` | `hcategory` |
| --- | --- | --- |
| structure | `ob`, `hom`, `reflect`, `twist⁺`, `twist⁻` | `ob`, `hom`, `reflect`, `rx`, `readback` |
| property | `stable`, `composable`, `invertible` | `cut⁺`, `cut⁻`, `unit` |
| third tier | `is-invertible±` | `is-unital` |
| interchange | genuine, and it measures the double twist | a theorem |
| stability | a tier | a theorem |

The third tiers have the same shape and say different things, so
the names differ on purpose. There the fiber of `coact-π` over
`snd` says `twist⁻` has a unique right inverse, which is
invertibility of the framing. Here the one filler makes the same
fiber a statement about a neutral idempotent, which is unitality.
Do not unify them.

Polarity needs no change. This tree labels the hand carrying the
term-slot filler `⁺`. That is the convention the duploid
dictionary selects, and `Cat.Logic` moved to match at `b979bb6`.

`hcategory` is the θ² = id fragment. One `rx` in both argument
slots is exactly that assumption: `var` would carry θ⁻¹ and
`covar` θ, so a single section forces θ ≡ θ⁻¹. `readback` is then
the cup cancellation `rx · f · rx ≡ f`, naturality of that twist
against its inverse. The ribbon setting lives strictly outside, in
`Cat.Logic`, where the failure of interchange measures the double
twist. Do not call this a duploid. A duploid is a unital magmoid
with one two-sided identity per object, which this is. But its two
hands agree, so it carries no duploid content.

Three questions were open when the tree froze.

- `readback` is the one structure field carrying no property. Its
  endomorphism fragment gives stability but not interchange, which
  needs `coact-covar` and `act-var` at general edges. No weakening
  in place is available.
- Extracting it. `Bb.WeakDeductiveSystem.Gist.FramedInterchange`
  shows readback need not be a field when the other slot's filler
  arrives as a fiber centre. `Bb.OneTwist.Base` carries the
  resulting record. It does not apply here. With one filler the
  extracted edge would have to equal `rx`, which is the θ² = id
  collapse again.
- `cut⁻` from `cut⁺`. Stability routes through `cut⁺` alone, so
  `cut⁻` could weaken to bare existence. Rejected, since it breaks
  the definitional `op`, and symmetry is worth more.

The live ledger reads the θ² = id convergence as `inferred`, not
as a theorem. `Cat.Logic` at (D′) is `hcategory` with two twists,
and `hcategory` is its collapsed one-twist instance.
