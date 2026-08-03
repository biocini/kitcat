# Reviewer checklist

Read by `reviewer.md` before evaluating a formalization or research
artifact. Covers four areas; work through all four before writing the
structured review.

## Statement fidelity (highest priority)

Look for:

- **Vacuous statements** — hypotheses that cannot be instantiated, unused
  hypotheses that make the theorem trivially applicable, conclusions weaker
  than the informal claim, or existential statements whose witness type is
  empty or trivial.
- **Definition gaming** — a definition crafted so the "theorem" becomes
  definitional or trivial (e.g. defining the target property as the proved
  fact, baking the conclusion into a hypothesis, or encoding the object so
  lossily that the theorem is about something else).
- **Smuggled assumptions** — extra hypotheses not present in the informal
  statement; decidability, finiteness, or well-foundedness side conditions
  silently added or silently dropped.
- **Quantifier and binder drift** — ∀/∃ order swapped, implicit arguments
  changing the reading, scoping that narrows the claim.
- **Encoding risk** — representation choices (intrinsic vs. extrinsic,
  bundled vs. unbundled, setoid vs. strict equality) that change what the
  theorem says compared to the informal source.
- **Missing side conditions** the informal proof uses implicitly.

## Proof quality

- open obligations (sorries, holes, admits) in any delivered file
- unsafe markers: axioms, postulates, disabled termination/positivity checks,
  escape hatches — each must be justified and disclosed
- brittleness: proofs that check only by fragile reduction behavior, unnamed
  auto-generated lemmas the artifact depends on
- duplicated functionality: proved helpers that already exist in the library
  (located via search, with `file:line` for the existing version)

## Library fit

- naming and module placement consistent with host library conventions
- visibility/export discipline; no leakage of internal scaffolding
- encoding style consistent with the library's established idioms
- reusable lemmas exposed at the right generality rather than inlined one-offs

## Artifact integrity

- claims that outrun the checker evidence ("verified" without a recorded run)
- sections, tables, or diagrams that survive from earlier drafts without support
- obligation counts or coverage claims that disagree with grep-able reality
- informal prose that quietly strengthens the formal result (e.g. "the theorem
  holds for all structures" when the formal statement fixes one)
- notation drift between the write-up and the code
