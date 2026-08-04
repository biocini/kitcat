# Elaboration: implicit and explicit arguments

When a parameter `A` precedes an argument whose type mentions `A`, is
`A` implicit? The gain from hiding it: use sites stop restating what
the later argument already says. The cost: the elaborator must
recover it. Where recovery fails, the failure is a metavariable
report at the call site, not a type error at the mistake.

The answer is not a matter of taste. **A parameter is implicit
exactly when every use site recovers it.** How the later argument's
type reduces decides recoverability. That is a fact about the code,
testable in a scratch module in under a minute. Inconsistency is
worse than either choice uniformly applied: a caller cannot hold
"sometimes inferable" in their head.

## The three tiers

**Tier 1, record-headed.** The parameter sits in a parameter position
of a record or data type that *heads* a later explicit argument's
type. Unification solves it from that argument's type, before any
other checking, in inferring and checking position alike.
**Implicit.**

```agda
module _ {o h} {C : category o h} (D : categoryᴰ C o' h') where
module _ {o h} {C : category o h} {M : monoidal C} (B : braided M) where
```

The chain rule follows: in a telescope of dependent structures, the
deepest one the declaration is *about* is explicit. Every ancestor
recoverable from it is implicit.

**Tier 2, Π-domain.** The parameter is the domain of a later explicit
argument's function type: `B : A → Type ℓ'`, or a synonym that
unfolds to one. Rigid, so it solves when the argument arrives as a
term with a declared type: a named definition, a variable, a
projection. It does **not** solve when the argument is a bare
lambda. The checker must know the domain to check the lambda, and
the result type cannot rescue it if that type unfolds and buries the
parameter under projections.

So the tier splits on how call sites actually supply the argument. A
family that always arrives named may hide its index. One that
arrives as a lambda may not.

**Tier 3, projection-reached.** The parameter is reachable only
through a field projection. No unifier solves `record.field ?G ≐ X`,
because projections are not injective. **Explicit, always.**

This is the tier that catches structure-indexed families. A type
synonym like `vfam G w z = reflexive-graph.vtx G → …` looks as
though it mentions `G`, but it unfolds to a function type whose
domain is a stuck projection. A family therefore never determines
its base.

**No principal argument.** A declaration whose hypotheses are all
unfolding predicates (`is-univalent G → is-path-objects B → is-prop
(structure G B)`) has nothing to recover from. It keeps its
parameters explicit, even when its neighbors hide theirs.

A record-typed parameter behind such hypotheses can appear to
solve anyway. The unifier rebuilds it by eta, field by field, from
the projections that the predicates' unfolded types mention. That
recovery is complete exactly while every field of the record
occurs there. This is an inventory fact about the record, not a
property of the signature. A new structure field that no predicate
mentions breaks every such signature at once, at the use sites.
Treat an eta-recovered parameter as unrecovered.

## Levels

Levels follow the same rule (ruled 2026-07-13 for `Level`, and
general since): a `Level` is implicit exactly when a later explicit
argument's type determines it by unification (`ob : Type o`
determines `o`). A level that occurs only in field types, or only in
the record's own sort, is explicit.

A definition body that happens to solve the meta is not inference.
The signature must stand alone.

Levels lead the signature. Quantifying over `Level` lands in `Setω`.
Nothing pairs a `Setω` inhabitant or passes it to a
level-polymorphic combinator. A level-leading telescope keeps every
partial application small.

The symptom is visible in the source: a use site that writes
`f {w = w} {z = z} x` reports that `w` and `z` were never inferable.

## Endpoints

Edge-indexed signatures are the same question one level down:
`{x y}` before `(p : edge x y)`. In a wild-category or
reflexive-graph setting this is the common case, and the answer is
less obvious than it looks.

**Whether an implicit endpoint solves is a property of the base, not
of the signature.** A structure's `edge` field reduces whenever the
structure is concrete (the same transparency that carries
definitional unit laws). Unification therefore meets the *reduced*
edge type. The endpoint survives only if that type mentions it in a
solvable position.

Base constructions divide accordingly. Those that keep their
endpoints in rigid or Miller-pattern position support implicit
endpoints. Those that discard an endpoint, bury it under a
transport, or reindex it through a substitution do not. Totals and
comprehensions inherit the failure. The constructions a library
builds *on top of* its base are therefore usually the ones where
inference breaks. The primitive bases, where the convention gets
designed and tested, are usually the ones where it works.

Two consequences worth stating, because neither is guessable from a
signature:

- The failure is **asymmetric**. A base that reindexes only its
  target leaves the source recoverable. Of two dual operations over
  the same structure, one elaborates and the other does not. Nothing
  in the types discloses which.
- An opaque `edge` would fix it at the root, but that move is not
  available where definitional unit laws rest on the transparency.
  Explicit endpoints are the only lever.

So: **the edge-indexed API names endpoints explicitly.** Endpoints
stay implicit only where another argument pins them rigidly: a
displayed reflexivity datum pinned by `vtx x`, or an operation whose
argument is a *path*, rigid in its endpoints at every base.

A field additionally cannot do otherwise. A type-synonym field
auto-introduces its implicits, and nothing re-binds them by name.
Implicit endpoints are therefore unusable in a copattern definition,
regardless of inference.

Explicitness here also surfaces content that implicitness absorbs.
An opposite-category or total-opposite operation that reads as an
identity with implicit endpoints reveals its transposition once the
endpoints appear: `f x y p` defined as `g y x p`. That is
information, not noise.

## Deciding a case

Do not reason about the unifier. Ask it. Both tests are a scratch
module in `Test/` and cost a minute.

**Parameter:** restate the signature with the parameter implicit,
delegating to the current form, and apply it at a real use site.

```agda
consumer' : ∀ {v e w z} {G : base v e} {B : fam G w z}
          → (L : structure G B) → hypothesis B → conclusion L
consumer' {G = G} {B} = consumer G B

_ = consumer' some-named-structure some-hypothesis   -- solves, or does not
```

**Endpoint:** instantiate at a *constructed* base (a total, a
comprehension, a quotient), not at the primitive one.

```agda
src-of : ∀ {v e} (G : base v e) → ∀ {x y} → edge G x y → vtx G
src-of G {x = x} _ = x

_ = src-of SomeTotal an-edge      -- unsolved metavariable ⇒ explicit
```

An `UnsolvedMetaVariables` or `UnsolvedConstraints` result is the
answer. Read the constraint before concluding: `?y.snd (f x) = g (f
x)` blocked on `?y.snd` says the endpoint appears applied to
non-variable arguments. That is not a Miller pattern and never will
be.

## Why uniformity is the point

A signature usable at some instantiations and not others is worse
than one uniformly verbose. The failure lands on whoever
instantiates it, as a metavariable rather than a mistake. Library
code checked under an abstract parameter elaborates fine and proves
nothing about the API. The green typecheck and the caller's
experience are different facts. Where they can diverge, prefer the
form that makes them agree.

## Worked example

`notes/2026-07-24-refl-inference-policy.md` applies both axes to
`Core.Rx` in full: the per-base endpoint-retention table, the
tier assignment for every construction in the suite, and the probe
behind each. That document is the worked application. This one is
the rule.
