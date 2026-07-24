---
name: hott
description: >-
  Use when users want to understand, learn, or reason about dependent
  type theory, homotopy type theory (HoTT), or univalent foundations —
  especially "why", "how", or "what's the deal with" questions.
  Trigger for: foundational questions about equality (judgmental vs
  propositional), identity types, type-theoretic proofs and reasoning;
  HoTT exercises (especially from Rijke's book); proving equivalences or
  characterizing identity types; path induction, transport,
  contractibility, truncation levels (propositions/sets), function
  extensionality, univalence, higher inductive types; comparative
  questions ("coming from set theory, why does type theory..."). Use
  even for generic "type theory" questions when they involve identity
  types, equality, or understanding foundational concepts.
---

# Homotopy Type Theory

You are working with a user on homotopy type theory (HoTT) in the style of
Egbert Rijke's *Introduction to Homotopy Type Theory* (arXiv:2212.11082) —
informal but fully rigorous univalent mathematics, written as prose with
precise types, not proof-assistant code. This file grounds you in the
discipline of HoTT reasoning; the `references/` directory holds digested
chapter notes that you read selectively, per the topic map below.

## The homotopy interpretation

The single most important habit: read type-theoretic statements
homotopically. Every type is a space, and its identity types are path
spaces — they can carry non-trivial structure of their own.

| Type theory | Homotopy theory |
|---|---|
| Type `A` | Space |
| Element `a : A` | Point |
| Identity type `x = y` | Space of paths from x to y |
| Type family `B : A → 𝒰` | Fibration over A |
| `Σ (x:A). B(x)` | Total space |
| `Π (x:A). B(x)` | Space of sections |
| Equivalence `A ≃ B` | Homotopy equivalence |
| `is-trunc k` | "Has no homotopical content above level k" |

Consequences to internalize:

- An identification `p : x = y` is a *witness*, not just a truth value.
  Two elements can be identified in more than one way, and `p = q` between
  identifications is again a meaningful type. Types are ∞-groupoids.
- A type is only understood when you know (i) how to construct its
  elements and (ii) what its identity types are. Much of HoTT work is
  *characterizing identity types* — see the fundamental theorem below.

## Two equalities — never confuse them

- **Judgmental equality** `a ≡ b` (definitional): holds by the computation
  rules of the theory. It is not a type; it cannot be hypothesized,
  negated, or proved by induction. Writing `a := b` introduces a
  definition. Example: `add n 0 ≡ n` holds by definition of `add`, since
  `add` is defined by induction on its first argument.
- **Propositional equality** `a = b` (the identity type): a type whose
  elements are identifications. It must be *proved* — typically by
  induction (on ℕ, etc.) or by path induction. Example: `add 0 n = n`
  needs induction on `n`; it is not judgmental.

When a user says "equal", figure out which one is meant, and be explicit
in your answer about which one you are establishing. A classic tell:
associativity of `add` is propositional (proved by induction), while the
defining equations of `add` are judgmental. Sloppiness here is the most
common beginner error — flag it when you see it.

## Notation

- `Π (x:A). B(x)` dependent function type; `λx. b` abstraction. Non-dependent: `A → B`.
- `Σ (x:A). B(x)` dependent pair type, elements `(a , b)`, projections `pr₁`, `pr₂`. Non-dependent: `A × B`.
- `x = y` (or `x =_A y`) identity type; `refl a : a = a`.
- `p ∙ q` path concatenation; `p⁻¹` path inverse.
- `ap f p : f x = f y` for `p : x = y`; `apd f p` dependent version.
- `tr B p : B x → B y` transport along `p : x = y`.
- `f ~ g` homotopy: `Π (x:A). f x = g x`.
- `A ≃ B` equivalences; `is-equiv f`; `is-contr A`; `fib f b : Σ (x:A). f x = b`.
- `is-prop A`, `is-set A`, `is-trunc k A`; `Prop-𝒰`, `Set-𝒰`; `‖A‖` propositional truncation.
- `𝟘` empty type, `𝟏` unit type with `⋆`, `bool`, `ℕ`, `ℤ`, `Fin k`, `A + B` coproduct with `inl`, `inr`.
- `𝒰`, `𝒱` universes. `S¹` the circle with `base : S¹` and `loop : base = base`; `Ω A : (a = a)` loop space.
- `W (x:A). B(x)` W-types with constructor `sup`.

## The reasoning toolkit

These are the moves. Each names when to reach for it and which reference
file develops it.

### 1. Inductive type discipline — the grammar of definitions

Every inductive type is specified by formation, introduction
(constructors), elimination (induction principle), and computation rules
(judgmental). To **define** a function out of an inductive type, give its
values on the constructors (recursion = non-dependent elimination). To
**prove** a property of all its elements, use the induction principle
(dependent elimination). Computation rules hold judgmentally, so
constructor-headed goals compute — simplify before doing anything clever.
→ `references/inductive-types.md`, `references/dependent-type-theory.md`

### 2. Path induction — proving things about all paths

**Based path induction**: to construct something for all `x : A` and
`p : a = x` (with `a` *fixed*), it suffices to handle `refl a`. Use the
unbased form when both endpoints may vary (reduce to `refl x : x = x`).
Reach for path induction to define path operations (concatenation,
inverses, transport, ap) and to prove properties quantified over *all*
identifications. Do **not** use it to reason about one specific path, and
remember it only applies when an endpoint is free — this is why
`p ∙ refl = p` for `p : x = y` needs the right endpoint free, and why
"axiom K" (`p = refl` for `p : x = x`) is *not* provable.
→ `references/identity-types.md`

### 3. Path algebra and transport

Paths form a groupoid *up to higher paths*: associativity, unit, and
inverse laws for `∙` are themselves identifications, satisfying further
coherences. Equational chains with `∙` and `⁻¹` are the basic arithmetic
of HoTT proofs. `ap f` preserves this structure (ap of a concat is a
concat of aps). `tr B p` moves along a fibration; a "path over `p`" from
`y : B x` to `z : B x'` is an identification `tr B p y = z` — the
dependent notion needed for higher inductive types and Σ-type identity
characterizations.
→ `references/identity-types.md`

### 4. The fundamental theorem of identity types — characterizing `x = y`

To show `(a = x) ≃ B x` for a family `B` with `b : B a`, it suffices that
`Σ (x:A). B x` be **contractible** (then the canonical map induced by
path induction from `refl` is a family of equivalences). This is the
principal tool for "what is the identity type of X?" Deploy it by
inventing the right family: observational equality `Eq-ℕ` for the
naturals, "Eq-coprod" families for disjointness of constructors, pairs of
paths for Σ-types, homotopies for Π-types (via funext), equivalences for
universes (via univalence). Also yields: a map is an embedding iff its
action on paths is an equivalence; identity systems and the structure
identity principle.
→ `references/fundamental-theorem.md`

### 5. The equivalence toolkit — proving `is-equiv f`

`is-equiv f` means `f` has a separate left and right inverse
(bi-invertibility); crucially it is a *proposition*, so "being an
equivalence" is a property, not extra structure. Ways to prove it:
(i) exhibit a quasi-inverse `(g, η, ε)`; (ii) show every fiber
`fib f b` is contractible (`is-contr-map f`); (iii) 3-for-2: if two of
`f`, `g`, `g ∘ f` are equivalences, so is the third; (iv) exhibit `f` as
part of a retract triangle whose other sides are equivalences. Any map
homotopic to an equivalence is an equivalence. Contractibility is itself
the base case: `A` is contractible iff `A → 𝟏`-style terminality holds,
and singletons `Σ (x:A). a = x` are the canonical contractible types.
→ `references/equivalences.md`

### 6. Truncation-level discipline — know where your goal lives

Before proving, ask: is the goal a proposition, a set, or a general type?

- `is-prop A := Π (x y : A). x = y` — proof-irrelevant types; logic lives here.
- `is-set A`: identity types are propositions (equality is a mere property).
- `is-trunc (k+1) A`: identity types are k-truncated.

Why it matters operationally: to prove a proposition-valued goal any
inhabitant works; propositions and k-types are closed under `Π` (needs
funext), under `Σ` when the base and fibers are at the right level, and
under equivalence; **Hedberg's theorem** — decidable equality implies
set — dispatches most concrete set-ness goals (`ℕ`, `Fin k`, `bool`). A
subtype (family of propositions) is an embedding on `pr₁`, so elements of
subtypes are equal as soon as their first components are.
→ `references/truncation-levels.md`

### 7. Function extensionality — `(f = g) ≃ (f ~ g)`

An axiom (not provable in bare Martin-Löf type theory). In informal
proofs this licenses: "to show `f = g`, it suffices to show `f x = g x`
for arbitrary `x`." Equivalent to weak function extensionality (a
product of contractible types is contractible); implies k-types are
closed under `Π`. Flag its use explicitly — users tracking axiom
dependencies care.
→ `references/funext.md`

### 8. Univalence — `(A = B) ≃ (A ≃ B)`

Voevodsky's axiom, characterizing the identity type of a universe. Two
directions, two uses: to *construct* an identification of types, build an
equivalence; to *use* an identification of types, transport along it.
Consequences: **propositional extensionality** (logically equivalent
propositions are equal); isomorphic structures (groups, posets, …) are
identified — the **structure identity principle**; funext follows; and
identity types of structured types become computable. It is inconsistent
with "all types are sets", so it marks the departure from set-theoretic
foundations.
→ `references/univalence.md`

### 9. Logic, univalent style — propositions as types

True is `𝟏`, False is `𝟘`, conjunction is `×`, implication is `→`,
universal quantification is `Π`, negation is `P → 𝟘`. But **existence and
disjunction must be truncated**: `∃ (x:A). P x := ‖Σ (x:A). P x‖` and
`P ∨ Q := ‖P + Q‖` — otherwise you claim more than mere truth. To use a
hypothesis `‖A‖` when proving a *proposition* `B`, it suffices to map
`A → B` (universal property of truncation). Surjective means "fibers
merely inhabited"; the image of `f : A → B` is `Σ (b:B). ‖fib f b‖`. The
trap to avoid: using raw `Σ` where mere existence is meant — that asserts
a chosen witness, not a truth.
→ `references/logic-truncation.md`

### 10. Higher inductive types and the circle

HITs add *path constructors* alongside point constructors, and the
induction principle must match: to map out of `S¹`, give a point `a : A`
and a loop `p : a = a`; to prove `Π (x:S¹). P x`, give `b : P base` and a
dependent path from `b` to `b` over `loop`. The flagship technique is
**encode–decode via the universal cover**: define a family over `S¹`
sending `base` to `ℤ` and `loop` to the path `succ : ℤ ≃ ℤ` (this is
where univalence enters), then show its total space is contractible and
conclude `Ω S¹ ≃ ℤ`, hence `π₁(S¹) = ℤ` as groups. The same pattern —
characterize the loop space of a HIT by a cleverly chosen family —
generalizes.
→ `references/circle.md`

## Topic map — load only what the question needs

Read the reference file(s) matching the user's topic before answering in
depth. For a conceptual question, one file usually suffices; for a proof,
read the file for the *technique* plus the file for the *domain*. Files
are listed roughly in dependency order.

| User asks about… | Read |
|---|---|
| Judgments, contexts, structural rules, substitution, λ-calculus, Π-types | `references/dependent-type-theory.md` |
| ℕ and induction, unit/empty/bool, coproducts, Σ, ×, pattern of inductive definitions | `references/inductive-types.md` |
| Identity types, path induction, transport, ap, groupoid laws, paths-over | `references/identity-types.md` |
| Universes, universe levels, type families defined by induction | `references/universes.md` |
| Equivalences, quasi-inverses, homotopies, contractibility, fibers, 3-for-2 | `references/equivalences.md` |
| Characterizing identity types, fundamental theorem, identity systems, Eq-ℕ, disjointness of constructors | `references/fundamental-theorem.md` |
| Propositions, sets, k-types, subtypes, embeddings, Hedberg, proof irrelevance | `references/truncation-levels.md` |
| Function extensionality, homotopies vs identifications of functions | `references/funext.md` |
| Propositional truncation, ∃/∨, logic, images, surjections, Cantor-style arguments | `references/logic-truncation.md` |
| Univalence axiom, propositional extensionality, transporting structures, smallness | `references/univalence.md` |
| Set quotients, equivalence relations, effectiveness, replacement axiom | `references/quotients.md` |
| Finite types, Fin k, counting arguments, finite choice, π of finite sets | `references/finite-types.md` |
| Semigroups, groups, homomorphisms, isomorphisms as identifications, quotient groups | `references/groups.md` |
| W-types, well-founded trees, initial algebras, extensional W-types | `references/w-types.md` |
| Circle, higher inductive types, universal cover, loop spaces, π₁(S¹) = ℤ, synthetic homotopy | `references/circle.md` |
| Curry–Howard in practice, decidability, modular arithmetic, gcd, primes, strong induction | `references/number-theory.md` |

If the user's question spans several rows, read the relevant files only —
do not bulk-load the whole directory. If nothing matches well, answer
from the principles in this file.

## How to write answers

- Match the user's register, but keep the Rijke discipline: state claims
  as types ("We construct an element of type …"), name what you
  construct, and give its type before its definition.
- Prose proofs, not code — unless the user asks for a proof assistant
  encoding, in which case say that this skill's grounding is the informal
  theory and adapt carefully.
- Use `≡`/`:=` for judgmental matters and `=` for the identity type,
  consistently. Use equational chains with `∙`, `⁻¹`, `ap`, `tr` for path
  algebra, justifying each step.
- Explicitly flag every use of an axiom: funext, univalence, propositional
  truncation, replacement. A proof that avoids them is strictly more
  informative; say when one does.
- For proof requests, first locate the goal on the truncation hierarchy
  and pick the technique accordingly (toolkit items 4–6 handle most
  "identity type" and "equivalence" goals).
- Warn about the classics: assuming axiom K/UIP, confusing `Σ` with `∃`,
  proving `is-equiv` by the wrong structure, or claiming judgmental
  equality where only propositional equality holds.

The reference digests were prepared from Egbert Rijke, *Introduction to
Homotopy Type Theory*, arXiv:2212.11082 (2022; revised version published
by Cambridge University Press, 2025).
