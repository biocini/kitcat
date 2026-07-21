# Program — 2026-07-20 — the LB certification program

Ruled (Lane, 2026-07-20): formalizing the LB/∂LB apparatus —
the braided, polarized, linear/dependent type theory implemented
at `~/src/ocaml/lb` — is the chief motivation of kitcat's
development at this time. This note is the program map: the
audit that grounds it, the phases, and the certificate targets.
It absorbs and extends `notes/2026-07-20-ribbon-arc.md` (whose
stages become Phases 2–5 here, with their ∂LB consumers named).

## The correspondence

∂LB's kernel and kitcat's categories are two renderings of one
architecture. ∂LB carries proof-equality as data (the ribbon
group `Gₙ = Bₙ ⋉ ℤⁿ` on every neutral spine), refuses UIP, and
decides conversion by normalization into a strict carrier with
canonical forms (BKL). kitcat's spine is the same design stated
categorically: `⊗₀-emb` is reflection into a strict
context-function domain, `⊗₀-ev`/`⊗₀-unit` are readback at the
identity frame and its round-trip law, propositional
representability fibers are uniqueness-of-readback, the
contractible spine is closure of normal forms under the formers,
and coherence rides the spine as carried path-data. A set-level
formalization could not state ∂LB's central commitment at all —
UIP at the hom level forces the symmetric collapse (HL 2024
Prop 5.8; kitcat's regress-theorem lineage is the same fact from
the other side) — so the wild cubical setting is not a style
choice but the only regime in which ∂LB's semantics can be
spoken.

## The audit (2026-07-20, against the ∂LB theory corpus and
`lib/kernel/{domain,conv}.mli`)

Five pressure points, two blank zones:

1. **Congruence functoriality is proved for the disjoint-strand
   half only** (`conv.mli`'s juxtapose argument); the cut/cabling
   half is oracle-checked at braid-word level and bottoms out in
   freeness (∂LB ledger claim 15, `[~]`). kitcat's
   free/hypothesis/field taxonomy is the classification the
   kernel should inherit and document.
2. **Silent exchange on central strands** (conversion modulo
   central-reorder slack) is a quotient by the centre, currently
   uncertified. Sound iff by Müger transparency — the
   centrality-layer theorem (Phase 1).
3. **The J layer risks a second construction**: the based-path
   skeleton in `Typing.Induction` must stay a projection of the
   conversion groupoid (the one-construction principle), and the
   non-synthesizing based-path producer smells like a J-shaped
   primitive where a filler-shaped one (the `path-iso` package)
   would synthesize.
4. **The braided-NbE gap (∂LB metatheory §11.5) partially
   deflates in the kitcat idiom**: the coherence tower needs no
   Day-convolution presheaf base — a bare context-function
   domain with representability fibers and carried path-data
   suffices, which is the shape the kernel already has. The spec
   for the domain is the record's field list. What genuinely
   remains: the non-commutative case-on-neutral monad (additives)
   and normalization completeness (gluing).
5. **Completeness of `Gn.equal` rests on freeness** — that group
   equality coincides with the intended categorical equality is
   the free-balanced-`∗`-autonomous package, the ledger's
   headline `[~]` and this program's keystone (Phase 5).

Blank zones on both sides: the additive layer (kitcat has no
`⊕`/`&`), and the gluing-style normalization-completeness proof.
Recorded as the joint frontier (Phase 7), not anyone's oversight.

## The currency

Every phase ships a named certificate: a kitcat theorem or
instance that lands in ∂LB's claim ledger as a citable upgrade
(`[~] → [✓-Agda]`, commit-pinned, Gloss-style freeze) or
discharges an audit finding. No phase exists without a consumer.
Standing disciplines: records minted against instances,
comparisons in Properties modules, the spine J-free, frontier
fenced.

## The phases

**Phase 0 — anchor.** The certificate convention (how ∂LB's
ledger cites a kitcat theorem); the first certificate through
the pipe: `End(I)` is commutative in any monoidal category
(Eckmann–Hilton over `monoidal C`, via `⊗₁-emb-⨾`), upgrading
the core lemma of `universe_unit_degeneracy_check.py`; the
ruling batch (ribbon-arc forks, the `Twist` rename, the
`--cubical` trigger: move if the HIT instances demand it —
S¹ support confirmed).

**Phase 1 — the centre.** Transparency (σ²-triviality) as a
predicate over `braided`, the Müger centre, closure properties,
and the silent-exchange soundness lemma (audit point 2
discharged). Vocabulary for everything later: centrality is
∂LB's purity gate, duplicability criterion, and dependency
license at once. Claim 21's θ-side completes in Phase 2.

**Phase 2 — balanced + the no-UIP model.** `balanced` at both
grades, minted against the S¹ group-tensor instance (twist = the
generator loop) and the Ω² Eckmann–Hilton instance (flank swap =
the EH move). Headline certificate: a model where
`Id(a,a) ≅ ℤ` via the twist and UIP fails — ∂LB metatheory §7's
expectation become a model-existence theorem, on π₁(S¹) = ℤ
only. Companions: the balancing law as the categorical spec for
the kernel's θ-bookkeeping; claim 21 closed. Parallel
kernel-facing study: the filler-first eliminator prototype
against `path-iso` (audit point 3).

**Phase 3 — dialogue.** Its own design session first: pole and
negations as representability of a refutation composite. Then
`dialogue`, the double-negation monads, the `∗`-autonomous
specialization (pole dualizing — LB's involutive boundary),
`balanced-dialogue` (Melliès Def. 12), and dialogical twist =
ribbon twist (Prop. 14) as the layer's first theorem.
**Chir re-gated (Lane, 2026-07-20): folds into this phase** as
the two-sided presentation — the dialogue-chiralities
equivalence (Melliès, Theorem 3) is a Properties-grade
presentation comparison; the surviving attic design
(`.attic/handoff.md`; the pruned chirality-record memory) is
re-derived here, where "kitcat's op is Melliès' dagger" gets its
home.

**Phase 4 — duploids and the keystone theorem.** The shifts
(`F ⊣ U` from the dialogue adjunctions), duploid structure,
thunkability and linearity, then braided Hasegawa–Thielecke:
central = thunkable in a braided dialogue duploid with
involutive negation — finite equational proof whose only
symmetry-use σ² = e neutralizes. Upgrades ⟨open-1⟩, the wall
under ∂LB's Move 1, to machine-checked.

**Phase 5 — the free instance and kernel soundness (keystone
gate; absorbs the old "framed syntax instance" project).**
Staged: (a) `Gₙ` in Agda with juxtaposition/functoriality, plus
the three-way pin (Agda-computed decidable instances — starting
with the 22-code finite universe model — diffed against the
Python oracles and the OCaml kernel); (b) the LB MA-core deep
embedding as a `balanced-∗-autonomous` instance; (c)
faithfulness on fragments; (d) the universal property — claim 15
formalized, making the kernel's soundness statement exact:
`Gn.equal` decides hom-equality of the free balanced
`∗`-autonomous category on the polarized atoms, the trusted leaf
shrunk to BKL arithmetic. (a) can start any time after Phase 0;
(d) is the only genuinely uncertain-scale item.

**Phase 6 — modalities and additives (consumer-gated).** The
additive layer (`⊕`/`&`) enters the spine here, forced by LB's
full calculus and the kernel's case-on-neutral monad; the
comonoid layer (braided cofree tensor coalgebra = the winding
comonad, no-`Sₙ`-quotient theorem, braided Seely) certifies
claims 16–18.

**Phase 7 — the fenced frontier (non-gating).** Normalization
completeness via gluing; the universe ω-limit (domain theory in
`Coh`); the infinitary server; mechanized Shum (whose role the
free-instance route deliberately reduces).

## Certificate → ledger map (initial)

| kitcat certificate | ∂LB target |
|---|---|
| `End(I)` commutative (Ph 0) | `universe_unit_degeneracy` core lemma |
| transparency/silent-exchange (Ph 1) | conversion's central-reorder slack; claim 21 (with Ph 2) |
| S¹ balanced model, `Id(a,a) ≅ ℤ` (Ph 2) | metatheory §7 no-UIP model existence |
| balancing law (Ph 2) | the kernel's θ-bookkeeping spec |
| dialogical = ribbon twist (Ph 3) | braided-dialogue Prop. 14 |
| braided Hasegawa–Thielecke (Ph 4) | ⟨open-1⟩ machine-checked |
| free MA-core universal property (Ph 5) | claim 15; kernel completeness |
| braided cofree comonoid, Seely (Ph 6) | claims 16–18 |

## Open rulings

The six ribbon-arc forks carry over (twist primitive; the
`Twist` name; negation genus; instance packaging; evidence tier;
sequencing), plus: the certificate convention's mechanics (where
certificates live in kitcat, how the ∂LB ledger pins them), and
whether Phase 5(a) opens in parallel immediately.
