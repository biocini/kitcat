# Design — 2026-07-21 — the free rack HIT

Design session for the `HData.Rack` work item. **The track is
gated behind the braided-theory redevelopment** (Lane,
2026-07-21): the new braided layer over the two-field record
develops first, and the rack type is designed afterwards, applying
what the model teaches. The rulings at the end are settled except
where marked; they are pinned constraints for that later work, not
a green light to start.

## The intention (pinned, Lane)

`Rack` is a **free HIT indexed on a carrier type** — `Rack A` as
`List A`'s framed sibling — with the crossing history carried as
**path data**, never as point-level annotation. The larger telos:
a List-like type for **contexts and cocontexts**, the framed
context calculus that the tensor context calculus (`⊗₀-ctx`,
today a bare pair) eventually reads against, and that the kernel's
framed-braid spine is certified against. Consequences:

- constructors are structural only — the S¹ pattern: generators
  and crossings, with every coherence a theorem;
- the classical free rack (`A × F(A)`, one generator `ℤ` with the
  shift) is the **derived shadow**, computed by encode–decode the
  way `winding-equiv` computes Circle's loop space — for one
  generator, components `Int` through the circle machinery, with
  `conj`/`rot` realizing the shift and `conj loop ≡ rot` by `refl`
  the meridian on the nose;
- the operation is extracted from contractible fibers **proven
  over the HIT** by induction (the CircleTensor `pull-contr`
  pattern), never posited.

## The classical target, as the shadow to derive

Convention (Fenn–Rourke, right action; vendoring is a chore
below): `x ▷ y` is x passing under y. R1: translations `_▷ y`
bijective; R2: `(x ▷ y) ▷ z ≡ (x ▷ z) ▷ (y ▷ z)`. The free rack
on A is `A × F(A)` — generator with crossing history — with
`(a , w) ▷ (b , v) = (a , w · v⁻¹bv)`: the actor contributes its
augmentation. Hand-verified: R1 by cancellation, R2 by expanding
both sides to `(a , w·v⁻¹bv·u⁻¹cu)`, reachability because
conjugates of generators generate `F(A)`. One generator collapses
to `m ▷ n = m + 1`, actor-independent; the quandle axiom fails on
the nose (`a ▷ a = a + 1`) — the ℤ of self-crossing is the
framing, and refusing to quotient it is "never index by the
invariant you derive" one floor down.

## The stub is superseded, not repaired

`Ra`'s failure was never that it is a HIT: it posits its
coherences as constructors (`sec`/`retr`/`coh`/`sdist`), and its
convention is mixed — `sec`/`retr`/`coh` make `x ▷_` invertible
(left-rack) while `sdist` is right-rack, and no rack satisfies
both: in the one-generator free rack the translation `x ▷_` is the
constant shift. `Ra-is-equiv`'s idea (translations as half-adjoint
equivalences) returns as a theorem.

## The ruled form (Lane, 2026-07-21)

The crossing cell is a **single `swap`, with `sym swap` as the
other-handed crossing** — the inverse relation between the
chiralities held definitionally, the framed R2-move for free. The
form to explore first:

    inc  : A → Rack A
    _⊗_  : Rack A → Rack A → Rack A
    swap : (x y : Rack A) → x ⊗ y ≡ y ⊗ x

with no coherence constructors: the tensor is free, and the
crossing is the only cell. Consequences to certify:

- **The framing is the derived self-swap loop** `swap x x :
  x ⊗ x ≡ x ⊗ x` — no kink constructor exists to posit it, `sym`
  inverts it without killing it, and its nontriviality is the
  R1-failure of framed isotopy arriving as a theorem. This is the
  ribbon-arc note's self-braiding candidate `c(p,p)` appearing as
  the HIT's own structure.
- **The detection design**: encode–decode against the circle
  machinery. The receiving structure sends `inc`-points to
  `Circle`-points, `⊗` to `mult`, and `swap x y` to a commuting
  homotopy of `mult` whose diagonal winds — `conj`/`rot` realize
  the shift, so the self-swap loop reads off as winding ±1 under
  the Melliès-positive orientation. The commuting homotopy for
  `mult` with a controlled diagonal is the one new circle cell
  this needs; `winding-equiv`, `self-path-equiv`, and the
  translation equivalences exist.
- **The classical shadow**: the `A × F(A)` realization stays as a
  parallel comparison track — the set-level free rack the HIT's
  components and loop data must recover, one generator first
  (components `Int`, the shift actor-independent).
- **The operation's site**: `▷` is extracted, not posited — the
  crossing composite's contractible fibers over the HIT
  (CircleTensor's `pull-contr` pattern, proven by induction), with
  sdist and its tower falling to the one-propositional-fiber
  pattern (`Legacy.Coherence`, `spine-tail`); level-k coherence =
  contractibility of the fiber over the depth-(k+1) composite,
  uniformity in k the theorem-schema question.

Open details inside the ruled form: whether v1 includes the empty
context (a unit point constructor — the context telos wants one
eventually, the framing exploration does not need it), and where
associativity enters (not a constructor; either a later cell or
derived through the monoidal record instantiated on the HIT).

**The self-distributivity question.** sdist is the Yang–Baxter
relation for the crossing (R3), and in the bare form it is neither
free at the point level nor even statable in the classical shape
(the YBE composites need re-association). What the type theory
does give freely is `swap`'s naturality — the square
`λ i → swap (p i) (q i)` for any paths — and R3 in a braided
category is exactly naturality of the braiding instantiated at
itself; since the free rack's elements live at the path level
(histories are loops, `π₀` collapses `swap`), the sdist statement
lives there too, where the free naturality squares are the
available material. Resolution order: first test empirically
whether free naturality delivers the R3-content — the spike's
first target, the same mechanism that made the exchange cells
definitional — and only if it does not, admit an R3 2-cell as
generating data: a relation of the presented isotopy theory
(legitimate for a free-on-generators-and-relations HIT), not a
posited coherence of an operation. Either way `▷` and its tower
stay derived, the kink stays a theorem, and on the derived shadow
sdist holds automatically after encode — the content is entirely
wild-level.

## Rack theory in Cat, separately

A record for rack *theory* — the `Cat.Monoidal` analogue for
crossing algebras — is worthwhile as its own study, with the free
HIT as its initial instance; that initiality is what feeds the
record-freeze guardrail. The representability shapes for such a
record (bare orbit readout with posited readback, versus
signed-history contexts with declared R2/R3 cells and derived
readback, versus orbit-record with the context calculus as derived
theory) were analyzed this session and survive for that track,
together with one refutation that constrains any shape: the
translation-map embedding (`b ↦ _▷ b`) fails on the free rack
itself — translations there are constant, so racks are not
faithfully represented by their translations, and the orbit
readout is the faithful choice. The Cat-side record is not on
`HData.Rack`'s critical path.

## Rulings (Lane, 2026-07-21)

1. **Unit** — leaning include, form OPEN: either an empty-context
   point constructor, or a pointed carrier (`x₀ : A` in the type
   former, `inc x₀` playing the unit — the tensorial-pole
   analogy). Decide after consulting Melliès
   (`resources/mellies-braided-dialogue`) on how the pole handles
   the unit/context role. **Associativity**: no cell committed —
   let the monoidal-record instance on the HIT force whatever cell
   it actually demands.
2. **Encode target for general A**: the wedge-of-circles loop
   space, ruled. Phasing: one generator first (mint `winding-∙`,
   `add-assoc`/`add-comm`, shared with the interchange-path
   component count); the wedge HIT arrives when general A does.
3. **The Cat-side theory record**: waits for the HIT as its first
   intended instance — instance evidence before fields.
4. **The context-calculus connection**: OPEN in refined form — the
   goal is to develop the new braided theory and then design the
   rack from the model, so the binding question is deferred with
   the whole track.
5. **Convention and glyphs**: Fenn–Rourke right action; `▷`/`◁`
   for the derived operation.
6. **Stub disposition**: `Ra` deleted outright (the half-adjoint
   translation idea survives here as a future theorem; an archive
   copy sits in `.attic/Stash/`).
7. **Chore**: vendor Fenn–Rourke, *Racks and links in codimension
   two*, into `resources/` before rack code cites the convention.
