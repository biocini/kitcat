# Groups in univalent foundations

Groups are the payoff example of univalent foundations. A group is an
element of a *type of all groups* `Group-𝒰`, built in two stages:
semigroups first, then groups as semigroups possessing a unit and
inverses. Because the carrier is required to be a **set**, every axiom
is a mere proposition, "having a unit" and "having inverses" are
*properties* of semigroups (not extra structure), and the structure
identity principle (SIP) plus univalence yields the headline theorem

    (G = H)  ≃  (G ≅ H)

— isomorphic groups are *equal* in the universe, making precise the
classical informal practice of writing e.g. `(G/N)/(K/N) = G/K`. The
chapter then defines homotopy groups `πₙ(A) := ‖Ωⁿ A‖₀` of pointed
types, proves Eckmann–Hilton (`πₙ` abelian for `n ≥ 2`), and sketches
concrete/abstract duality: groups ⇔ pointed connected 1-types via
`G ↦ BG` (delooping/classifying type) and `B ↦ Ω B`.

Dependencies: `truncation-levels.md` (sets/propositions),
`univalence.md` (SIP), `fundamental-theorem.md`, `funext.md`,
`logic-truncation.md` (0-truncation), `equivalences.md` (embeddings,
3-for-2), `identity-types.md` (groupoid laws), `finite-types.md`
(`Fin n`, `BSₙ`). **Axiom flag:** the headline theorem uses univalence
(via SIP) and funext; delooping contractibility relies heavily on
univalence; `πₙ` uses set truncation; the rest is axiom-free.

## Key definitions

- **Semigroup.** A triple `(G , μ , α)` with `G : Set-𝒰` a set,
  `μ : G → (G → G)`, and
  `α : Π (x y z : G). μ (μ x y) z = μ x (μ y z)` an associativity
  homotopy. The type of all semigroups in `𝒰`:

      Semigroup-𝒰  :=  Σ (G : Set-𝒰). Σ (μ : G → G → G).
                         Π (x y z : G). μ (μ x y) z = μ x (μ y z)

  The carrier is a *set* so that associativity (an identity type of a
  set) is a proposition — this is what makes SIP apply.
- **Unital semigroup / monoid.** `is-unital G` is the type of triples
  `(e , left-unit , right-unit)` with `e : G`,
  `left-unit : Π (y:G). μ e y = y`, `right-unit : Π (x:G). μ x e = x`;
  `Monoid-𝒰 := Σ (G : Semigroup-𝒰). is-unital G`.
- **Inverses; groups.** For unital `(G , e)`: `is-group' (G , e)` is
  the type of triples `((-)⁻¹ , left-inv , right-inv)` with
  `left-inv : Π (x:G). μ x⁻¹ x = e`,
  `right-inv : Π (x:G). μ x x⁻¹ = e`. Then

      is-group G  :=  Σ (e : is-unital G). is-group' (G , e)
      Group-𝒰     :=  Σ (G : Semigroup-𝒰). is-group G

  `Group-𝒰` is a *subtype* of `Semigroup-𝒰` (see results).
- **Homomorphism.** For (semi)groups `G H`: a pair `(f , μ_f)` with
  `f : G → H` and `μ_f : Π (x y : G). f (μ_G x y) = μ_H (f x) (f y)`.
  The type `hom G H`. Same definition for semigroups and groups —
  preservation of units and inverses is then *provable*, not assumed.
- **Isomorphism.** `is-iso h` is the type of triples `(h⁻¹ , p , q)`
  with `h⁻¹ : hom H G` a *homomorphic* inverse and
  `p : h⁻¹ ∘ h = id`, `q : h ∘ h⁻¹ = id`:

      G ≅ H  :=  Σ (h : hom G H). Σ (k : hom H G).
                   (k ∘ h = id) × (h ∘ k = id)

- **`iso-eq`.** For `G : Semigroup-𝒰` (resp. `Group-𝒰`) in a univalent
  universe: the family `iso-eq : (G = H) → (G ≅ H)` by path induction,
  `iso-eq refl := id_G`.
- **Concrete examples.** `ℤ` under addition; the **automorphism
  group** `Aut X := (X ≃ X)` of a set `X` (operation = composition,
  unit = `id`); the **symmetric group** `Sₙ := Aut (Fin n)`.
- **Pointed types, maps, loop spaces.** `𝒰* := Σ (X : 𝒰). X`;
  `A →* B := Σ (f : A → B). f a = b`. Loop space: `Ω : 𝒰* → 𝒰*`,
  `Ω (A , a) := (a = a , refl a)`; iterated: `Ω⁰ A := A`,
  `Ωⁿ⁺¹ A := Ω (Ωⁿ A)`.
- **Homotopy groups.** For pointed `A`, `n ≥ 1`: `πₙ(A) := ‖Ωⁿ A‖₀`,
  unit `η (refl a)`, the unique operation with
  `η r · η s = η (r ∙ s)` (well-defined since `‖-‖₀` is a set; `∙`
  descends through both arguments). `π₁` is the **fundamental group**.
  Convention: `π₀(A) := ‖A‖₀` — only a set, no group structure.
- **Functorial action.** For pointed `f` with `p : f a = b`:
  `Ω f r := p⁻¹ ∙ ap f r ∙ p` (pointed since `ap f refl ≡ refl` and
  `p⁻¹ ∙ p = refl`). Iterate for `Ωⁿ f`; with the functorial action of
  0-truncation get `πₙ f : πₙ(A) → πₙ(B)` — a homomorphism, since
  `ap` preserves `∙`.
- **Binary action on paths; horizontal concatenation.** For
  `f : A → (B → C)`: `ap-binary_f : (x = x') → ((y = y') → (f x y =
  f x' y'))`, defined by `ap-binary_f (refl , refl) := refl`. Applied
  to `∙` itself: `r ∙ₕ s := ap-binary_∙ (r , s) : (p ∙ q = p' ∙ q')`
  for `r : p = p'`, `s : q = q'` (**horizontal** concatenation;
  ordinary `∙` of 2-identifications is **vertical**).
- **Delooping / classifying type.** For a group `G`, the unique
  pointed connected 1-type `BG` with `G ≅ Ω BG`. **Abstract groups**:
  elements of `Group-𝒰`; **concrete groups**: pointed connected
  1-types.
- **G-sets.** Abstract: `G-Set-𝒰 := Σ (X : Set-𝒰). hom G (Aut X)`.
  Concrete: families `X : BG → Set-𝒰`; the acted-upon set is `X ⋆`,
  the action given by **transport** along loops.
- **Orbits, fixed points.** For concrete `X`: `X/G := Σ (u : BG). X u`
  (orbits), `X_G := Π (u : BG). X u` (fixed points). `X` is
  **transitive** if `X/G` is connected; **free** if `X/G` is a set; a
  **G-torsor** if both, equivalently if `X/G` is contractible.
- **Subgroups** (exercise): `P : G → Prop-𝒰` containing the unit,
  closed under `μ` and inverses. **Normal**: closed under conjugation
  `x y x⁻¹`.

## Key results

- **`is-unital G` is a proposition.** The unit laws live in a set, so
  are propositions; two units agree by `e = μ e e' = e'`. Being unital
  is a *property*, not structure.
- **`is-group G` is a proposition.** Reduce to `is-group' (G , e)`;
  two inverse operations agree by

      x⁻¹ = μ e x⁻¹ = μ (μ x⁻¹' x) x⁻¹ = μ x⁻¹' (μ x x⁻¹)
          = μ x⁻¹' e = x⁻¹'

  Hence the forgetful map `Group-𝒰 → Semigroup-𝒰` is an embedding.
- **`hom G H` is a set.** Preserving `μ` is a proposition, so equality
  of homomorphisms ≃ homotopies of underlying functions; hence the
  category laws (identity, composition, associativity) hold up to `=`.
- **`is-iso h` is a proposition; `G ≅ H` is a set.** Two homomorphic
  inverses agree: `k y = k (h (k' y)) = k' y`.
- **Isomorphisms are equivalences** (lemma `grp_iso`). `h : hom G H`
  is an isomorphism iff its underlying map is an equivalence; the
  inverse of an equivalence is automatically homomorphic:

      f⁻¹ (μ_H x y) = f⁻¹ (μ_H (f (f⁻¹ x)) (f (f⁻¹ y)))
                    = f⁻¹ (f (μ_G (f⁻¹ x) (f⁻¹ y))) = μ_G (f⁻¹ x) (f⁻¹ y)

  Hence `(G ≅ H) ≃ Σ (e : G ≃ H). Π (x y : G). e (μ_G x y) =
  μ_H (e x) (e y)`.
- **HEADLINE: `iso-eq` is an equivalence for semigroups.** For
  `G : Semigroup-𝒰`, the family `iso-eq : (G = H) → (G ≅ H)` over
  `H : Semigroup-𝒰` is a family of equivalences. Proof: by the
  fundamental theorem it suffices that `Σ (H : Semigroup-𝒰). G ≅ H` is
  contractible; rewrite via `grp_iso` separating carrier and
  structure. Since `H ↦ (G ≃ H)` is an identity system on `Set-𝒰` at
  `G` (this *is* univalence), SIP condition (v) reduces the goal to
  contractibility of
  `Σ (μ' : has-assoc-mul G). Π (x y : G). μ_G x y = μ' x y` — by
  funext, associativity being a proposition over a set.
- **HEADLINE: `iso-eq` is an equivalence for groups.** Commuting
  triangle: `(G = H) --ap pr₁--> (UG = UH) --iso-eq--> (G ≅ H)` vs the
  direct `iso-eq`, `U` = underlying semigroup. Top map: equivalence
  since `pr₁ : Group-𝒰 → Semigroup-𝒰` is an embedding (being a group
  is a property). Right map: equivalence by the semigroup theorem.
  Conclude by 3-for-2. **Isomorphic groups are equal.**
- **`Semigroup-𝒰` and `Group-𝒰` are 1-types**: identity types are
  equivalent to the *sets* `G ≅ H`. Not sets — automorphisms exist.
- **Loop spaces of pointed 1-types are groups.** `Ω A` is a set and a
  group under `∙` with unit `refl`; the group laws are special cases
  of the groupoid laws of identity types.
- **`πₙ₊₁(A) ≅ πₙ(Ω A)`**: by induction `Ω (Ωⁿ A) ≃* Ωⁿ (Ω A)` as
  pointed types preserving `∙`; truncate.
- **Pointed equivalences induce isomorphisms**: `e : A ≃* B` gives
  `πₙ e : πₙ(A) ≅ πₙ(B)` for all `n ≥ 1` (apply `grp_iso`).
- **Laws of `ap-binary`; unit laws for `∙ₕ`; interchange.**
  `ap-binary_f (refl , q) = ap (f x) q`,
  `ap-binary_f (p , refl) = ap (f - y) p`, and both ways around the
  naturality square agree with `ap-binary_f (p , q)`. Hence
  `refl² ∙ₕ s = s`, `r ∙ₕ refl² = r`, and the interchange law
  `(r ∙ r') ∙ₕ (s ∙ s') = (r ∙ₕ s) ∙ (r' ∙ₕ s')` — by path induction
  on `r` and `s`, reducing to `r' ∙ₕ s'`.
- **Eckmann–Hilton.** For `r s : Ω² A`: `r ∙ s = s ∙ r`. Proof:
  `r ∙ s = (r ∙ₕ refl²) ∙ (refl² ∙ₕ s) = (r ∙ refl²) ∙ₕ (refl² ∙ s)
  = r ∙ₕ s`, and symmetrically `r ∙ₕ s = s ∙ r`. Note: path induction
  is *not* applicable — both endpoints `refl a` are fixed.
- **`πₙ(A)` abelian for `n ≥ 2`.** Reduce to `π₂` via
  `πₙ(A) ≅ π₂(Ωⁿ⁻² A)`. The goal `Π (r s : π₂ A). r s = s r` is an
  identification in a set, so the dependent universal property of
  0-truncation applies twice; then
  `η r · η s = η (r ∙ s) = η (s ∙ r) = η s · η r`.
- **Delooping is contractible** (sketch; univalence-heavy). For every
  `G : Group-𝒰` the type
  `Σ (B : Pointed-Connected-1-Type-𝒰). G ≅ Ω B` is contractible; its
  center is `BG`. Hence `Ω : Pointed-Connected-1-Type-𝒰 → Group-𝒰` is
  an equivalence. Example: `Sₙ ≅ Ω BSₙ`, `BSₙ` the type of finite
  types of cardinality `n`.
- **Delooping of homomorphisms.** For `f : hom G H`, the type of
  pointed `b : BG →* BH` with `Ω b` matching `f` along the given
  isomorphisms is contractible — a unique delooping `Bf : BG →* BH`.
- **Generalized fundamental theorem (truncated maps).** For connected
  `A`, `a : A`, `B` over `A`, TFAE: (i) every family
  `f : Π (x:A). (a = x) → B x` is a family of `k`-truncated maps;
  (ii) `Σ (x:A). B x` is `(k+1)`-truncated. Proof: (ii) ⇔ every
  base-point inclusion `𝟏 → Σ B` is `k`-truncated; by connectedness
  only `(a , y)` matters; that inclusion is homotopic to `tot f` for
  `f(a , refl) := y`; conclude via fibers of `tot` and Yoneda.
  Application: `X/G` a set ⇒ `g ↦ g x` is an embedding — freeness.
- **Torsors.** Concrete `X` is a torsor iff `X/G` is contractible,
  iff (fundamental theorem) `Π (v : BG). (u = v) → X v` is a family of
  equivalences, iff `X` is in the image of the embedding
  `_ = - : BG → (BG → Set-𝒰)`. Hence concrete G-torsors ≃ `BG`; one
  construction of `BG` is as the type of abstract G-torsors.
- **From the exercises.** Homomorphisms preserve units and inverses;
  `μ_G : G → (G ≃ G)` is an injective homomorphism (Cayley);
  `equiv-eq : (X = X) → (X ≃ X)` is a group isomorphism;
  `hom ℤ G ≃ G` by evaluation at `1` (ℤ = free group on one
  generator); semigroup isomorphisms between unital semigroups
  preserve units ⇒ isomorphic monoids are equal; normal subgroups of
  `G` ≃ `Σ (H : Group-𝒰). Σ (f : hom G H). is-surj f`; connected
  components of the type of groups of order `n ≤ 8`: `1 1 1 2 1 2 1 5`.

**Not covered here.** Quotient groups `G/N` are not constructed (the
`(G/N)/(K/N) = G/K` example is only informal motivation). Normal
subgroups appear only in exercises. Abelian groups get no type
`Ab-𝒰`; commutativity appears via Eckmann–Hilton and the dihedral
exercise `D_A := A + A` for abelian `A` (with `Dₖ := D_{ℤ/k}`).

## Reasoning idioms

- **To identify two groups**: exhibit an isomorphism `G ≅ H` and apply
  the inverse of `iso-eq` — one equivalence of carriers preserving `μ`
  suffices. This is SIP + univalence; *flag both axioms*.
- **To show a structure is a property**: prove its type is a
  proposition (`is-unital`, `is-group`, `is-iso`, preserves-`μ`). Then
  the Σ-extension is a subtype, the forgetful map is an embedding, and
  `ap pr₁` is an equivalence on identity types.
- **Equality of group elements is ordinary equality in the carrier
  set** — a proposition. Equational calculations (units, inverses,
  conjugation) are chains of identifications in a set; no coherence
  bookkeeping is needed.
- **Equality of homomorphisms is a homotopy of underlying functions**:
  to show `f = g : hom G H`, give `f ~ g`; preservation data is
  irrelevant. Same for isomorphisms.
- **To show a homomorphism is an isomorphism**: show its underlying
  map is an equivalence (`grp_iso`); the inverse is automatically
  homomorphic. Never construct the homomorphic inverse by hand.
- **SIP-style contractible-total-space pattern**: to characterize
  `G = H`, prove `Σ (H : T). G ≅ H` contractible with center
  `(G , id_G)`; peel layers (carrier via univalence, operation via
  funext + propositionality of laws). To port the result from a
  supertype to a subtype (semigroups → groups), set up the commuting
  triangle with `ap pr₁` (an equivalence, by the embedding) and
  conclude by 3-for-2.
- **To reason about `πₙ`**: descent through truncation. Goals that are
  identifications in a set reduce via the dependent universal property
  of `‖-‖₀` to goals about loops, where `η r · η s ≡ η (r ∙ s)`
  computes.
- **When path induction is blocked** (loops with both endpoints fixed,
  as in Eckmann–Hilton): switch to the 2-dimensional calculus —
  horizontal concatenation, unit laws, interchange — and shuffle
  `refl` units.
- **To compare pointed types**: compute homotopy groups. Distinct
  `πₙ` ⇒ not equivalent; pointed equivalence ⇒ all `πₙ` isomorphic.
  Every abstract group arises as `Ω BG`.
- **Concrete group theory**: replace `G` by `BG`. G-set = family over
  `BG`; action = transport; orbits = Σ; fixed points = Π; transitive =
  connected orbits; free = orbits a set; torsor = contractible orbits.
  Subgroups ~ transitive G-sets; normal subgroups ~ fixed points of
  the conjugation action.
- **Uniqueness of structure = contractibility**: "unique `BG`",
  "unique `Bf`" are contractibility claims; prove via fundamental
  theorem / SIP, not ad hoc uniqueness arguments.

## Pitfalls

- **The carrier must be a set.** Drop `is-set G` and the laws acquire
  higher coherence content; `is-unital`/`is-group` cease to be
  propositions and the SIP proof collapses — `iso-eq` is no longer an
  equivalence. For higher groups the right notion is a pointed
  connected type (delooping), not a group with a 1-type carrier.
  (Categories are the analogous 1-level structures; not covered.)
- **`Group-𝒰` is a 1-type, not a set.** `G = H` is the *set* of
  isomorphisms; nontrivial automorphisms give nontrivial loop spaces
  in `Group-𝒰`. Do not UIP over groups.
- **Two different `iso-eq` maps.** Semigroup vs group versions have
  different domains (`G = H` in `Semigroup-𝒰` vs in `Group-𝒰`); the
  group one factors through `ap pr₁`. Track where identifications
  live.
- **Don't strengthen `hom`.** Only preservation of `μ` is recorded;
  unit/inverse preservation are theorems, not fields.
- **`is-iso h` uses a homomorphic inverse**; the equivalence with
  `is-equiv` of the underlying map is a lemma (`grp_iso`), not the
  definition. Either way it is a proposition, so `G ≅ H` is a set.
- **`π₀` is not a group.** `π₀(A) := ‖A‖₀` has no canonical group
  structure; groups start at `n = 1`. And Eckmann–Hilton needs
  `n ≥ 2`: `π₁` can be any group (`Ω BG ≅ G`), hence generally
  nonabelian; the interchange shuffle requires 2-loops.
- **The conjugation in `Ω f` matters.** `Ω f r := p⁻¹ ∙ ap f r ∙ p`;
  dropping `p⁻¹ ∙ … ∙ p` breaks pointedness of `Ω f` and hence `πₙ f`.
- **Multiplication on `πₙ` requires descent** through the universal
  property of 0-truncation in both variables; you cannot pattern-match
  on truncated elements outside set-valued goals. Likewise direct
  `ind-=` is impossible on `r s : refl a = refl a` — both endpoints
  are fixed.
- **Delooping results are univalence-heavy** — contractibility of
  `Σ (B : …). G ≅ Ω B`, hence `BG`, `Bf`, abstract/concrete duality.
  Do not cite in axiom-free developments.
- **Quotient groups are not in this chapter** — normal subgroups are
  characterized via surjective homomorphisms (exercise); for `G/N`
  reach for set quotients (`quotients.md`) or connected maps
  `BG →* BH`.
- **`Group-𝒰` is universe-relative**, living in the next universe;
  same size discipline as `Set-𝒰` (`universes.md`).

## See also

- `univalence.md` — univalence and the SIP: the engine behind `iso-eq`
  and deloopings.
- `fundamental-theorem.md` — contractible total spaces ⇒ identity
  characterizations; skeleton of the headline proof.
- `truncation-levels.md` — sets, propositions, 1-types; `k`-truncated
  maps; why `Group-𝒰` is a 1-type.
- `equivalences.md` — `is-equiv`, embeddings, 3-for-2; `Aut X`.
- `identity-types.md` — groupoid laws (`∙`, `⁻¹`): loop spaces are
  groups; `ap`, `tr`, `apd`.
- `funext.md` — the SIP step: pointwise-equal operations are equal.
- `logic-truncation.md` — `‖-‖₀` and its universal property: `πₙ`.
- `universes.md` — `Set-𝒰`, `Prop-𝒰`, size discipline for `Group-𝒰`.
- `dependent-type-theory.md` — Σ/Π packaging; properties-as-propositions.
- `inductive-types.md` — `𝟏`, `⋆`, coproducts (dihedral `D_A := A + A`).
- `finite-types.md` — `Fin n`, `Sₙ := Aut (Fin n)`, `BSₙ`.
- `quotients.md` — set quotients: the missing ingredient for `G/N`;
  compare `X/G := Σ (u : BG). X u`.
- `circle.md` — `π₁(S¹) ≅ ℤ`: the flagship homotopy-group computation.
- `w-types.md` — orthogonal inductive machinery, not used here.
- `number-theory.md` — `ℤ` as a set with group laws; `ℤ/k`; the
  prime-detection example via `ℤ/2`-sets of factorizations.
