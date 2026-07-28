# Bb.OneTwist

## The construction

A virtual graph carrying one twist. The negative invertibility
tier mentions `coact-π`, hence `var`, hence `twist⁻` alone. So the
tier is stateable before a second twist exists, and its centre
defines one. Mutual inverseness on that side is then the centre's
own witness, not an axiom. The carrier holds four fields where the
two-twist record holds five.

Three modules. `Base` states the carrier and extracts the positive
twist. `Cancel` adds the `⁺` tier and asks for the term-side
cancellation, `act-π (twist⁻ x) ≡ snd`. `Models` runs the carrier
against the two stock models, the path groupoid and the abelian
group.

The verdict is against the proposal, and `Cancel` carries it. The
model is the Klein four-group `Bool × Bool` under `xor`, with
`reflect m (t , k) = t ⊕ (σ m ⊕ k)` for `σ` a three-cycle of the
non-unit elements. Extraction walks the cycle, so `twist⁺` is
`ψ twist⁻` and the `⁺` centre is `ψ² twist⁻`, a different element.
Every field and both tiers hold there, and `no-cancel⁺` refutes
the cancellation. By contractibility the cancellation says the `⁺`
centre agrees with the posited twist. That same agreement is
op-involutivity at the twist field, so `no-agree` settles both
halves at once. The same model shows that the
readback-record reduction does not transpose to a readback-free
carrier: `⨾⁻twist⁺-cancellable` holds while `no-frame⁻` refutes
the frame law.

`Models` runs the checks that a definition change must pass. The
path groupoid over an arbitrary type, at an arbitrary `t⁻`, pins
the extraction to the inverse (`twist⁺-forced`). No h-level
hypothesis enters. The abelian group at an arbitrary element shows
a group model cannot witness the failure (`group-cancel⁺`). Those
checks pass, and the countermodel measures what they do not. The
proposal breaks the opposite. The op moves up a level, its square
posits the `⁺` centre, and the centre is not the twist.

## Provenance

Archived 2026-07-28 at commit `006d477`, out of three `Test`
spikes: `ExtractedTwist` became `Base`, `ExtractedTwistCancel`
became `Cancel`, and `ExtractedTwistModels` became `Models`. Git
tracked the first alone, so the commit records one rename and two
additions. The same commit re-points the citations in
`docs/deductive-systems/`.

The spikes ran on 2026-07-27 to settle a proposal against the
five-field carrier, and the session log is
`notes/2026-07-27-one-twist-verdict.md`. The tree sits here
because the proposal lost. The rejected carrier keeps its own
namespace so that the evidence stays checked, and the live
definitions keep theirs.

## Relationships

`Bb.WeakDeductiveSystem` is the carrier the proposal targeted, and
both spikes here run against its `Gist` modules.
`Bb.OneTwist.Cancel` extends the readback record of
`Gist.FramedInterchange`, and `Bb.OneTwist.Models` runs the two
models of `Gist.FramedCut` and `Gist.FramedGroup`.

The verdict left the live record with five fields, and the
extraction trick with a home one level up. In the balanced layer
both cancellations hold anyway. The remaining datum over a
one-twist carrier is then exactly the centre-agreement path
family. `Cat.Logic` has since taken the balanced field, so the
trick did not return.

`Bb.VgCategoryShape` is the other one-filler record, and it is not
this one. There the single chosen edge fills both argument slots
and collapses the double twist to the identity. Here the record
posits one twist and extracts the other, and asks for no collapse.
