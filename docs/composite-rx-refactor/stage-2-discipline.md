# Stage 2 — `Core` disciplined by Rx

`Core.Kan` and `Core.Composite` restated in the backend's vocabulary,
per the tiers of the [standpoint](standpoint.md); the dead surface and
the duplications retired. Everything here is Tier 1–2 material —
conversions and certified identities — plus deletions licensed by the
[evidence](evidence.md) censuses.

The stage is the compatibility discipline run in reverse. The
cubical machinery speaks the virtual-graph language here, before
`Cat.Logic` introduces the theory formally: an implementation
already shaped by the metatheory makes its conformance trivial to
exhibit when the theory arrives, and leaves the development itself
available for study at that point. Nothing in this stage waits on
the frontend.

## 2.1 `Core.Composite.SysP` as a displayed fibration

The highest-leverage item: it makes `Core.Kan` and `Core.Transport`
one development, and it is the Core-level worked instance of the
frontend's push/pull.

A family `P : A → Type v` is displayed over `discrete A`:

```agda
disp-of P .edge x y p a b = PathP (λ i → P (p i)) a b
```

`SysP.SysLift p a` is the displayed fan on the nose, and
`SinglP-contr` witnesses `rx.is-cov-fibration` — both VERIFIED
(`Test.KanIdentities` probe 7). Restore the contractibility the port
dropped (`LiftP-is-contr`) as that witness: `push` is `transport`,
`lift` is `transport-filler`, `lift-unique` the contraction.

**The canonical-construction ruling, written in.** The identification
`SysP.fillerP ~ cov-fibration.lift` is propositional, not
definitional — a com-tower and a transp-filler are two centres of one
contractible space. Per the one-construction principle and the
fiber-projection idiom (never declare the structure; declare a
contractible fiber and project):

- `SysLift`/`syslift-center` are articulated as fibration
  projections; the com-based construction retires from that role.
- **No bridging lemma is stated** between the two constructions.
- `SysOver`/`fillerP` — systems *with walls* over the filler, strictly
  more than the path case — remain plumbing, per the Exo boundary.

## 2.2 Fan vocabulary in `Core.Kan`

- `Total-sys φ s` restated as `rx.fan (discrete A) (sys-composite φ s)`
  — refl (`Test.KanIdentities` probe 3), so consumers
  (`Core.Transport.J.J-sys`) are untouched.
- `Total-sys-contr` as `Singl-contr` at the composite (probe 4; the
  lemma lives in `Core.Base` after 0.1).
- The module's opening prose states the plumbing/statement boundary
  (*the plumbing constructs centres; the Rx layer states what they are
  centres of*) and the Tier-3 reading of `HComposite` — prose only;
  the lens restatement is Stage 5 material, gated on D7.

## 2.3 Dead surface, aliases, relocations

Delete (zero consumers src-wide, ≈ 120 lines + `hcom-unique`'s 47 ms;
full list with liveness notes in [evidence](evidence.md)): `HSys`,
`sys-path`, `SysExt`, `sys-lid`, `hc`, `kext`, `TotalP`,
`extend→is-contr`, `ap-comp-dep`, `path→square`, `square-sym-h`,
`square-sym-v`, `hcom-unique`, `hcom-lid-unique`, `com-unique`,
`com-lid-unique`, `hcom-cong`.

Collapse the aliases: `sys-composite` (= `hcom`, and the plumbing
speaks `hcom` — 2.2's boundary);
`Sys`/`PartialsP` to one name (`Sys φ A` is `PartialsP φ (λ _ → A)` —
VERIFIED); `sys-filler` against `hfil` (argument permutation).
Re-point `Core.Composite` and `Core.Transport.J`.

Relocate `Chain` to `Core.Path`, updating `Core.Univalence`'s import
(the one live consumer of the combinators).

Keep, with their reasons on record: `Total-sys` (load-bearing through
`Total-sys-contr`'s type in `J-sys`), `conn` (four live consumers),
`cone` (Stage 3.4's transcription target), `is-contr→extend`,
`contr-face` (Stage-5 material with `Core.Coherence.Paths`).

## 2.4 The representability theory, generalized into the backend

`Core.Groupoid.emb` and `Core.Groupoid.Virtual.repr.emb` are one
ternary operation under different curryings — refl-equal, VERIFIED
(`Test.KanIdentities` probe 8); `Core.Path.Composition.Repr` is a
third copy; `yon-unbiased = repr` is a consumer-less alias. Three
statements of one theorem at one instance, differing only in
currying.

D2 is ruled (the backend — [decisions](decisions.md)): the library
develops the latent virtual-graph theory of the cubical machinery,
part of `Core.Composite`'s meaning, so the ternary action and its
representability theory are backend material. This item therefore
pursues the general form now rather than keeping a preferred
duplicate:

- Rule D3 first: the general statement's currying is exactly what
  the three copies differ by.
- Mint the virtual-graph representability statement in the backend,
  in the ruled shape. The graph-with-action structure and its
  term/coterm displays sit below `Core.Kan` (`Test.RxVirtual`
  certifies the structure layer); the `hom≃total-representable`
  proof consumes `J`/`Core.Equiv` and sits above — the usual
  structure/theory split. Module name and seat: decision D10.
- Collapse all three path-groupoid developments to the discrete
  instance of the general form (`pcom` as the action), deleting the
  duplicated `iso→equiv` proofs (~110 lines) and the alias.

Anti-duplication invariant: exactly one general statement in the
library. `Cat.Logic`'s `hom≃total-representable` becomes the
frontend's restatement in the sequent vernacular, landing
definitionally on the backend theorem per the compatibility ruling —
no bridge.

Module fates: after 0.1, `Core.Groupoid`, `Core.Groupoid.Virtual`,
and `Core.Path.Composition` all have zero live consumers; with the
theory descended they retire, and what remains of **decision D10**
is the backend module's name and seat.

## 2.5 Displaced composition

Delete `comp-pathp` (zero consumers anywhere). The other nineteen are
held in place, and the hold is a contract with a test, not a
deferral: eighteen of them have no `Core` consumer at all
([evidence](evidence.md)), existing in `Core.Kan` and
`Core.Path.Base` solely to serve `Cat.Depreciated`, so leaving them
unexamined would let a tree this refactor deletes go on shaping the
namespace it is being deleted from.

**The placement question.** Each held name carries one open question:
*does the construction have a theoretical placement in the
disciplined `Core`?* The family displaces the path-composition
calculus — `cat.fill`/`rfill`/`lcoh`/`rcoh`, `Path.assoc`/`unitl`/
`commutes`, `HComposite.path`, `pcom.map`, `ap-comp`/`ap-merge` — to
unary and binary type families. Once 2.1 makes `SysP` a displayed
fibration the question is concrete: does the name arise as that
fibration's action on the base construction it displaces — `fillerP`
and its consequences over a composite — or is it an artifact of the
ad hoc route it was built along?

**Disposition, per name, before Stage 4 closes.** Exactly two
outcomes:

- *Placement found* — the construction is reformulated over the
  disciplined structure, in its principled home, and the displaced
  form retires. The name need not survive; the mathematics does.
- *No placement* — it was the deprecated tree's scaffolding, and it
  is deleted with that tree.

There is no third outcome. A name is not carried into the rebuilt
`Cat` on the grounds that it already exists, and the disciplined
structure is not bent to receive one.

**Timing.** The question becomes answerable when 2.1 lands and
sharpens at Stage 5, when the target shape is fixed; it must be
answered for every held name before Stage 4 deletes the deprecated
tree, that being the last moment a consumer exists to check a
reformulation against. Until then the held names take no new
consumers.

`comp-pathp₂` is the one name with a `Core` consumer
(`Core.Path.Exchange`); it faces the same question, and **decision
D9** settles the module that holds it either way.

## Acceptance

- Whole-library check unchanged throughout the stage.
- `just profile Core.Kan` at or below the measured noise band
  (1,025–1,072 ms); after 2.3 the `hcom-unique` 47 ms comes off the
  named costs.
- No bridging lemmas: `just lint changed` plus review against the
  one-construction principle at 2.1 and 2.4.
