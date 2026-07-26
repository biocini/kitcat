# Morphism Equivalences in Wild Magmoid Theory

Three notions of "f : hom x y is an equivalence" in a magmoid, ordered from
most extensional to most algebraic.

## ≐  Neutral identity (Cat.Magmoid.Base, Cat.Magmoid.Neutral)

    is-neutral f = is-left-divisible f × is-right-divisible f

    x ≐ y = Σ f ∶ hom x y , is-neutral f

Composition with f is an equivalence on all hom-types: (_⨾ f) and (f ⨾_) are
both type-level equivalences. Statable with just the magmoid signature — no
units or associativity required.

This is the extensional (Yoneda-style) characterization: f is an equivalence
iff it *behaves* as one in every compositional context. Names no witnesses.

Always propositional: is-neutral-is-prop.

## ≃  Biinvertible equivalence (Cat.Magmoid.Eqv)

    is-biinv f = (Σ s , f ⨾ s ≡ id) × (Σ r , r ⨾ f ≡ id)

    x ≃ y = Σ f ∶ hom x y , is-biinv f

f has a section and a retraction (which need not coincide). Requires units
to state. Propositional with associativity (is-biinv-is-prop).

## ≅  Wild isomorphism

    x ≅ y = Σ f ∶ hom x y , Σ g ∶ hom y x , (f ⨾ g ≡ id) × (g ⨾ f ≡ id)

f has a single two-sided inverse. Requires units to state. NOT propositional
in general — the inverse is unique (with assoc) but the coherence pair
(f⨾g≡id , g⨾f≡id) can carry higher structure.

## Relationships

With associativity + units:

    is-neutral f ≃ is-biinv f        (is-neutral≃is-biinv, Cat.Magmoid.Eqv)

The biinv→neutral direction uses associativity to build hom-type equivalences
from section/retraction witnesses via iso→equiv. The neutral→biinv direction
extracts witnesses as centers of contractible fibers — no associativity needed.

Without associativity, is-neutral is strictly stronger than is-biinv.

## Unit decomposition

is-unital e decomposes into two independent halves, each pairing one-sided
divisibility with the matching coherence:

    is-unital e ≃ is-left-unital e × is-right-unital e

where:

    is-left-unital e  = is-right-divisible e × lcoh    → derives unitl : e ⨾ f ≡ f
    is-right-unital e = is-left-divisible e  × rcoh    → derives unitr : f ⨾ e ≡ f

The coherences (lcoh/rcoh) witness that an idempotent equivalence is the
identity. Classically trivial; in HoTT they carry genuine content — they are
the homotopical residue of what is automatic at h-level 0.

Each half corresponds to a Jonsson unit concept:

    is-left-unital   ↔  local left unit (universal)   ↔  left skew-poloid / constellation
    is-right-unital  ↔  local right unit (universal)  ↔  right skew-poloid
    both halves      ↔  effective / two-sided unit     ↔  poloid (wild category)

And to the duploid decomposition of associativity:

    thunkable morphisms  ↔  interact with is-left-unital structure
    linear morphisms     ↔  interact with is-right-unital structure

## Derived units from neutral morphisms

For f : hom x y with is-neutral f:

    loop f   : hom y y    unique e with f ⨾ e ≡ f    (target-side / canonical right unit)
    coloop f : hom x x    unique e with e ⨾ f ≡ f    (source-side / canonical left unit)

These are Jonsson's canonical local units (λ_x = xx⁻¹, ρ_x = x⁻¹x), extracted
as centers of contractible fibers rather than computed from an explicit inverse.

With a designated unit i at the object:

    loop-absorb / coloop-absorb    all derived units equal i
    loop-is-unital / coloop-is-unital    derived units carry full is-unital
    loop-thunkable / loop-linear    derived units are thunkable and linear

Uniqueness of local units — the hypothesis Jonsson needs for his restricted
multiplication theorem (ESN) — is automatic from contractibility of fibers.

## References

- Cat.Magmoid.Base — is-neutral, is-unital, loop/coloop, absorb lemmas
- Cat.Magmoid.Eqv — is-biinv, is-neutral≃is-biinv, eqv-cat, eqv-inv
- Cat.Magmoid.Neutral — ≐ without units, neu-sym (with assoc)
- Jonsson, "On Group-Like Magmoids" (.refs/gist/on-group-like-monoids.gist.tex)
