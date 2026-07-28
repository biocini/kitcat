# Bb.VgCategoryShape — archive

**Archive banner.** Vendored 2026-07-28: the `Mag` staging tree,
frozen green at `Bb.VgCategoryShape`. Module paths in this record
read `Mag.*`; they resolve as `Bb.VgCategoryShape.*`. The
re-founding program below remains the program of record for the
`Mag` rebuild, which starts fresh at `src/Mag`.

# Mag — staging

Staging directory for the **one-twist** record, `hcategory`: a reflexive
graph with a ternary reflection, readback, two represented cuts, and a
unit. Module paths stay `Mag.*` until the shape settles. Nothing here is
committed.

## State: green

All four modules typecheck. `just check-tree src/Mag` passes, and so do
`src/Cat` and `src/Test`. Lint is clean, prose check included.

| module | holds |
| --- | --- |
| `Mag.Type` | the record |
| `Mag.Base` | the derived theory, including `interchange` and `stable` |
| `Mag.Unit` | neutral edges as isomorphisms; the unit package contractible |
| `Mag.Parity` | the two-origin heap, which keeps `rx` honest as structure |

`Test.MagInterchange` and `Test.MagOp` are deleted; the first is
superseded by `Mag.Base`, the second is task 1 below.

## The record

```agda
record hcategory o h : Type₊ (o ⊔ h) where
  field
    ob      : Type o
    hom     : ob → ob → Type h
    reflect : ∀ {x y} → hom x y → judgment x y      -- structure
    rx      : (x : ob) → hom x x                     -- structure
    readback : ∀ {x y} (f : hom x y) → eval (reflect f) ≡ f   -- structure
    cut⁺    : ∀ f g → is-contr (representable (composite⁺ f g))  -- property
    cut⁻    : ∀ f g → is-contr (representable (composite⁻ f g))  -- property
    unit    : (x : ob) → is-unital x                             -- property

  is-neutral e = (∀ {z} → is-equiv (λ h → reflect e ((x , e) , (z , h))))
               × (∀ {w} → is-equiv (λ g → reflect e ((w , g) , (x , e))))
  unital    e  = is-neutral e × (e ⨾⁻ e ≡ e)      -- not a proposition
  is-unital x  = Σ e ∶ hom x x , unital e          -- a proposition, by CK
  idn {x}      = unit x .fst
```

> **structure** — `ob`, `hom`, `reflect`, `rx`, `readback`
> **property** — `cut⁺`, `cut⁻`, `unit`

`rx` is the reflexive-graph edge, posited bare with no condition on it.
`unital` takes no `is-` prefix: its second component is a path between
untruncated edges, and over the path groupoid on `S²` the fibre at
`refl` is `Ω²S² = ℤ`. The total space is the proposition, so `is-unital`
earns the prefix. `Mag.Unit.is-unital-is-prop` proves it; in fact
`unit-contr` shows the type is contractible.

## What is proved, and how

Read `reflect m ((_ , t) , (_ , k))` as the string `t · m · k`. Every
name below is in `Mag.Base` unless marked.

**From readback alone.** `reflect-lc`; `coact-covar`; `act-var`; and one
unit law per hand *at `rx`* — `unitr⁺rx : f ⨾⁺ rx y ≡ f` and
`unitl⁻rx : rx x ⨾⁻ f ≡ f`. Each hand absorbs `rx` on the side its own
action closes. The other two laws are not reachable here.

**From readback and the cuts.** `⨾⁻-is-act : act-π h (w , s) ≡ s ⨾⁻ h`
and `⨾⁺-is-coact : coact-π f (z , k) ≡ f ⨾⁺ k` — each composition is its
own action read at the axiom. Then the two readings of one reflection,
`read⁺` and `read⁻`, and their difference

```agda
  mixed-assoc t m k : t ⨾⁻ (m ⨾⁺ k) ≡ (t ⨾⁻ m) ⨾⁺ k
```

which is Mangel's *valid* mixed word. Also `le-is-coact` and
`re-is-act`: the two self-filled halves of `is-neutral e` are the two
*other* hands' self-composites acting.

**`rx ≡ idn`.** `idn-idem⁻` turns the first half of `idn-neutral` into
`idn-pre`, an equivalence of `coact-π idn`, hence `idn-⨾⁺-equiv`.
Surjectivity of `idn ⨾⁺ _` plus `mixed-assoc idn idn k` gives
`unitl⁻ : idn ⨾⁻ m ≡ m`. So `rx` and `idn` are both left units for the
negative hand, and `post-eqv` — the second half of `idn-neutral`, via
`re-is-act`, with no idempotence spent — cancels them against each
other at `idn ⨾⁺ idn`.

**The other two unit laws.** `unitr⁺` from `unitr⁺rx` along `rx≡idn`;
then `idem⁺`, `idn-post`, `absorb⁺`, `absorb⁻`, and finally `unitl⁺`
and `unitr⁻`.

**Interchange is a theorem.** `mixed-assoc f idn g` collapses on both
sides by `unitl⁺` and `unitr⁻`:

```agda
  interchange f g : f ⨾⁻ g ≡ f ⨾⁺ g
```

Nothing is assumed. `judgment-interchange` lifts it to the cuts.

**Stability is a theorem.** `absorb⁻` gives `composite⁻-idn`, so
`cut⁻ idn f` is a contractible fibre over a point of the image, and
`image-fibers-contr→is-embedding` gives `stable`. `cut⁺ f idn` with
`composite⁺-idn` would do equally.

**In `Mag.Unit`.** A map whose square is an equivalence is one, so with
interchange and associativity each half of `is-neutral e` gives a
composition-action isomorphism: `neutral→pre`, `neutral→post`, no
idempotence spent. Cancelling gives `cancel : is-neutral e → e ⨾⁻ e ≡ e
→ e ≡ idn` and then `cancel-equiv`, which makes the idempotence
component a based path. Hence `unit-contr` and `is-unital-is-prop`.

## What `Mag.Parity` shows

The two-element heap, `reflect m ((_ , t) , (_ , k)) = t ⊕ m ⊕ k`. Every
edge is neutral, and both cuts are represented, at *either* origin. So
`heap false` and `heap true` are two `hcategory` structures on one graph
and one reflection (`same-reflection` is `refl`) with different
compositions (`compositions-differ`). `reflection-is-equivariant` and
`twist-moves-the-origin` exhibit the automorphism that carries one to
the other.

That is why `rx` is structure and not property: no condition on
`reflect` alone selects it.

## The re-founding program

Planned 2026-07-28. The claim: `hcategory` is, in substance, the
wild depolarization theorem. The set-level shadow is Sterling's
`Depolarization` in `~/TypeTopology/source/Duploids`, where a
depolarized deductive system is a precategory (see the Resources
entry in `src/Cat/Logic/TODO.md`). Here `Mag.Base` already proves
the wild counterpart pointwise: interchange, all four unit laws,
and stability are theorems, so the hands agree and `hcategory` is
a unital associative wild carrier. What is missing is the theorem
form, and the route is a re-founding rather than a record edit.

The mechanism is `Cat.Logic`'s balanced layer, investigation line
5 in `src/Cat/Logic/TODO.md`: with both cancellation orders, each
hand is two-sided unital with its own twist as unit, two unital
magmoids on one graph, offset by θ². At θ² = id the two magmoids
merge, and the merged object is `hcategory`. So the target is:

- `hcategory` re-derived as the θ² = id specialization of the
  balanced layer over a deductive system.
- `readback` becomes the balanced layer's cancellation data,
  which is where position (C) already ruled that content lives.
- `rx` becomes the merged twist, `reflect` stays carrier
  structure, the cuts become the composability tiers, and `unit`
  is derived from the revived unit laws.
- The theorem: framing-trivial balanced deductive systems are
  hcategories, and conversely. That is the wild form of
  Sterling's depolarization result, and it makes the comparison
  table below a theorem rather than a table.

The structure-field justifications survive the re-founding as
reasons the specialization presents this way: `ReadbackTwist` for
`readback`, `OpTwist` for `reflect`, `Mag.Parity` for `rx`. The
spike harvest is complete in the `Mag` files (checked
2026-07-28), so no Test lemma blocks this.

Gated on `Cat.Logic` line 5. The two TODOs move together: when
the balanced layer is stated, this program is its first consumer.
Task 2 below, promotion out of `Mag.*`, should wait on the
re-founding decision, since the module's eventual home depends on
whether it is a specialization or a sibling.

## Tasks

1. **`Mag.Op`.** The construction is free and was working before the
   record changed. `opᴹ` reverses `hom`, swaps the argument halves in
   `reflect`, keeps `rx` and `readback` unchanged (`readback` is
   literally the same term, since `covar-op` is `var`), and exchanges
   the two cuts through the argument-swap equivalence, which is a
   definitional involution under Σ-eta. `op-op` is `refl` on every
   structure field and needs `is-contr-is-prop` on the two cuts.

   The one new obstacle is the `unit` clause. It needs
   `idn ⨾⁻op idn ≡ idn`, and `⨾⁻op` does not reduce to `⨾⁺` because
   `is-contr-equiv`'s centre goes through `Equiv.inv`. Get it from
   contractibility instead: `ap fst (cut⁻op idn idn .paths (idn ⨾⁺ idn ,
   w))` where `w` is `λ i γ → reflect-⨾⁺ idn idn i (γ .snd , γ .fst)`,
   then compose with `idem⁺`.

2. **Promotion out of `Mag.*`.** The record name is settled
   (`hcategory`); the module path is not.

## Comparison with `Cat.Logic`

|  | `virtual-graph` + `is-deductive-system` | `hcategory` |
| --- | --- | --- |
| structure | `ob`, `hom`, `reflect`, `twist⁺`, `twist⁻` | `ob`, `hom`, `reflect`, `rx`, `readback` |
| property | `stable`, `composable`, `invertible` | `cut⁺`, `cut⁻`, `unit` |
| third tier | `is-invertible±`, contractible fibre of an action map over `snd` | `is-unital`, contractible by CK |
| interchange | genuine; measures the double twist | a theorem |
| stability | a tier | a theorem |

The third tiers have the same shape and say different things, so the
names differ on purpose. In `Cat.Logic` the fibre of `coact-π` over
`snd` says `twist⁻` has a unique right inverse, which is invertibility
of the framing. Here the one filler makes the same fibre a statement
about a neutral idempotent, which is unitality. Do not unify them.

Polarity needs no change here. `Mag` already labels the hand carrying
the term-slot filler `⁺`, which is the convention the duploid dictionary
selects, and `Cat.Logic` was swapped to match at `b979bb6`.

`hcategory` is the **θ² = id fragment**. One `rx` in both argument slots
is exactly that assumption: `var` would carry θ⁻¹ and `covar` θ, so a
single section forces θ ≡ θ⁻¹. `readback` is then the cup cancellation
`rx · f · rx ≡ f`, which is naturality of that twist against its
inverse. The ribbon setting lives strictly outside, in `Cat.Logic`,
where the failure of interchange measures the double twist. Do not call
this a duploid: a duploid is a unital magmoid with one two-sided
identity per object, which this is, but its two hands agree, so it has
no duploid content.

## Open questions

- **`readback` is the one structure field carrying no property.** Its
  endomorphism fragment suffices for `stable` but not for
  `interchange`, which needs `coact-covar` and `act-var` at general
  edges. It cannot be weakened in place.
- **Extracting it.** `Cat.Logic.Gist.FramedInterchange` shows `readback` need not
  be a field if the *other* argument slot's filler is extracted as a
  fibre centre, and `Bb.OneTwist.Base` carries the resulting record.
  That is position (B) on the `Cat.Logic` side; `src/Cat/Logic/TODO.md`
  states it there and the two must move together. It does not apply
  cleanly here, because with one filler the extracted edge would have to
  equal `rx`, which is the θ² = id collapse again.
- **`cut⁻` from `cut⁺`.** `stable` routes through `cut⁺` alone, so
  `cut⁻` could weaken to bare existence. Rejected: it breaks the
  definitional `op`, and symmetry is worth more.
- **`is-neutral` versus `is-iso` inside `unital`.** Now known
  equivalent, by `neutral→pre`/`neutral→post` and composing
  equivalences back. The self-filled form is in the record because it is
  stateable before `rx`; that is a choice, not an accident.
