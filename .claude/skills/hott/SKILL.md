---
name: hott
description: "Domain knowledge for dependent type theory, homotopy type theory (HoTT), and univalent foundations: a reasoning toolkit plus topic-indexed digests of Egbert Rijke's Introduction to Homotopy Type Theory, covering identity types, path induction, transport and paths-over, the fundamental theorem of identity types, equivalences, contractibility and fibers, truncation levels (propositions, sets, k-types), function extensionality, univalence, propositional truncation and the logic of mere existence, higher inductive types, the circle and loop spaces, W-types, set quotients, universes, finite types, and groups. This skill should be loaded whenever the work turns on these concepts and the exact statement or the correct technique matters, and not only when the user asks about them: before characterizing an identity type, choosing an induction principle, claiming a type is a proposition or a set, asserting what is or is not provable (UIP, axiom K), invoking function extensionality or univalence, distinguishing judgmental from propositional equality, or reasoning about a higher inductive type. It applies to informal prose mathematics and to the univalent-foundations content behind a proof-assistant development alike, since the concepts are the same either way. It should also be used when the user asks directly about any of these topics, including conceptual and comparative questions about foundations."
---

# Homotopy Type Theory

This file states the discipline of homotopy type theory (HoTT) in the
style of Egbert Rijke's *Introduction to Homotopy Type Theory*
(arXiv:2212.11082), rigorous univalent mathematics written with precise
types. The material applies to informal prose mathematics and to
proof-assistant developments alike. The reasoning toolkit below names
the moves and says when to reach for each. The digested chapter notes in
`${CLAUDE_SKILL_DIR}/references/` carry the detail. Read them
selectively, per the topic map.

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

When a source says "equal", determine which one is meant, and state
which one is being established. A classic tell: associativity of `add`
is propositional (proved by induction), while the defining equations of
`add` are judgmental. Sloppiness here is the most common error. Flag it
wherever it appears.

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
→ `${CLAUDE_SKILL_DIR}/references/inductive-types.md`, `${CLAUDE_SKILL_DIR}/references/dependent-type-theory.md`

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
→ `${CLAUDE_SKILL_DIR}/references/identity-types.md`

### 3. Path algebra and transport

Paths form a groupoid *up to higher paths*: associativity, unit, and
inverse laws for `∙` are themselves identifications, satisfying further
coherences. Equational chains with `∙` and `⁻¹` are the basic arithmetic
of HoTT proofs. `ap f` preserves this structure (ap of a concat is a
concat of aps). `tr B p` moves along a fibration; a "path over `p`" from
`y : B x` to `z : B x'` is an identification `tr B p y = z` — the
dependent notion needed for higher inductive types and Σ-type identity
characterizations.
→ `${CLAUDE_SKILL_DIR}/references/identity-types.md`

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
→ `${CLAUDE_SKILL_DIR}/references/fundamental-theorem.md`

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
→ `${CLAUDE_SKILL_DIR}/references/equivalences.md`

### 6. Truncation-level discipline — know where the goal lives

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
→ `${CLAUDE_SKILL_DIR}/references/truncation-levels.md`

### 7. Function extensionality — `(f = g) ≃ (f ~ g)`

An axiom (not provable in bare Martin-Löf type theory). In informal
proofs this licenses: "to show `f = g`, it suffices to show `f x = g x`
for arbitrary `x`." Equivalent to weak function extensionality (a
product of contractible types is contractible); implies k-types are
closed under `Π`. Flag every use explicitly, so that the axiom
dependencies of a development stay visible.
→ `${CLAUDE_SKILL_DIR}/references/funext.md`

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
→ `${CLAUDE_SKILL_DIR}/references/univalence.md`

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
→ `${CLAUDE_SKILL_DIR}/references/logic-truncation.md`

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
→ `${CLAUDE_SKILL_DIR}/references/circle.md`

## Topic map — load only what the task needs

Read the reference file(s) matching the topic before working in depth.
For a conceptual point, one file usually suffices. For a proof, read the
file for the *technique* plus the file for the *domain*. Files are
listed roughly in dependency order.

| Topic | Read |
|---|---|
| Judgments, contexts, structural rules, substitution, λ-calculus, Π-types | `${CLAUDE_SKILL_DIR}/references/dependent-type-theory.md` |
| ℕ and induction, unit/empty/bool, coproducts, Σ, ×, pattern of inductive definitions | `${CLAUDE_SKILL_DIR}/references/inductive-types.md` |
| Identity types, path induction, transport, ap, groupoid laws, paths-over | `${CLAUDE_SKILL_DIR}/references/identity-types.md` |
| Universes, universe levels, type families defined by induction | `${CLAUDE_SKILL_DIR}/references/universes.md` |
| Equivalences, quasi-inverses, homotopies, contractibility, fibers, 3-for-2 | `${CLAUDE_SKILL_DIR}/references/equivalences.md` |
| Characterizing identity types, fundamental theorem, identity systems, Eq-ℕ, disjointness of constructors | `${CLAUDE_SKILL_DIR}/references/fundamental-theorem.md` |
| Propositions, sets, k-types, subtypes, embeddings, Hedberg, proof irrelevance | `${CLAUDE_SKILL_DIR}/references/truncation-levels.md` |
| Function extensionality, homotopies vs identifications of functions | `${CLAUDE_SKILL_DIR}/references/funext.md` |
| Propositional truncation, ∃/∨, logic, images, surjections, Cantor-style arguments | `${CLAUDE_SKILL_DIR}/references/logic-truncation.md` |
| Univalence axiom, propositional extensionality, transporting structures, smallness | `${CLAUDE_SKILL_DIR}/references/univalence.md` |
| Set quotients, equivalence relations, effectiveness, replacement axiom | `${CLAUDE_SKILL_DIR}/references/quotients.md` |
| Finite types, Fin k, counting arguments, finite choice, π of finite sets | `${CLAUDE_SKILL_DIR}/references/finite-types.md` |
| Semigroups, groups, homomorphisms, isomorphisms as identifications, quotient groups | `${CLAUDE_SKILL_DIR}/references/groups.md` |
| W-types, well-founded trees, initial algebras, extensional W-types | `${CLAUDE_SKILL_DIR}/references/w-types.md` |
| Circle, higher inductive types, universal cover, loop spaces, π₁(S¹) = ℤ, synthetic homotopy | `${CLAUDE_SKILL_DIR}/references/circle.md` |
| Curry–Howard in practice, decidability, modular arithmetic, gcd, primes, strong induction | `${CLAUDE_SKILL_DIR}/references/number-theory.md` |

When a task spans several rows, read those files only. Do not bulk-load
the whole directory. When nothing matches well, work from the principles
in this file.

## Applying the theory

- Keep the Rijke discipline: state claims as types ("We construct an
  element of type …"), name what is constructed, and give its type
  before its definition.
- Use `≡`/`:=` for judgmental matters and `=` for the identity type,
  consistently. Use equational chains with `∙`, `⁻¹`, `ap`, `tr` for path
  algebra, justifying each step.
- Flag every use of an axiom: funext, univalence, propositional
  truncation, replacement. A derivation that avoids them is strictly
  more informative, so say when one does.
- Locate the goal on the truncation hierarchy first, then pick the
  technique. Toolkit items 4–6 handle most "identity type" and
  "equivalence" goals.
- Watch for the classics: assuming axiom K/UIP, confusing `Σ` with `∃`,
  proving `is-equiv` by the wrong structure, or claiming judgmental
  equality where only propositional equality holds.

The reference digests come from Egbert Rijke, *Introduction to Homotopy
Type Theory*, arXiv:2212.11082 (2022). Cambridge University Press
published the revised version in 2025.
