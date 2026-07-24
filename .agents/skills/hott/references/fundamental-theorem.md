# The fundamental theorem of identity types

The fundamental theorem of identity types is the principal tool for
answering "what is the identity type of A?" It says: to characterize
`a = x` for a fixed `a : A` and all `x : A`, exhibit a family `B` over
`A` with `b : B a` whose **total space** `Σ (x:A). B x` is contractible
— then `(a = x) ≃ B x` for every `x`. Characterizing an identity type
thereby becomes routine: invent the right family, prove one
contractibility.

The chapter builds in layers: (1) a fiberwise map
`f : Π (x:A). B x → C x` is a family of equivalences iff `tot f` on
total spaces is an equivalence; (2) the fundamental theorem — fiberwise
equivalence ⇔ contractible total space ⇔ identity system;
(3) applications: `Eq-ℕ` computes `m = n`, equivalences are embeddings,
coproduct identity types compute (disjointness of `inl`/`inr`), and the
structure identity principle (SIP) computes identity types of
`Σ`-structures.

Dependencies: contractible maps, fibers, 3-for-2 (`equivalences.md`);
path induction, singleton contractibility (`Σ (x:A). a = x`, center
`(a , refl a)`), groupoid laws, the `Σ`-identity characterization
(`identity-types.md`); `ℕ`, coproducts, `𝟘`, `𝟏` (`inductive-types.md`).

## Key definitions

- **Homotopy fiber** (recalled from `equivalences.md`): for `f : A → B`
  and `b : B`, `fib f b := Σ (x:A). f x = b`. A map is an equivalence
  iff all its fibers are contractible ("contractible map").
- **The map `tot f` on total spaces.** For a fiberwise map
  `f : Π (x:A). B x → C x`:
  `tot f : Σ (x:A). B x → Σ (x:A). C x`, `tot f (x , y) := (x , f x y)`.
  Functorial up to homotopy: `tot (λx. g x ∘ f x) ~ tot g ∘ tot f`,
  `tot (λx. id) ~ id`, and fiberwise `f ~ g` gives `tot f ~ tot g`.
- **Family of equivalences**: `f : Π (x:A). B x → C x` with each
  `f x : B x → C x` an equivalence.
- **Family of maps over `f`; `tot[f] g`.** For `f : A → B`, `C` over
  `A`, `D` over `B`, `g : Π (x:A). C x → D (f x)`:
  `tot[f] g : Σ (x:A). C x → Σ (y:B). D y`, `(x , z) ↦ (f x , g x z)`.
  Special case `g := λx. id`: the **base-change map**
  `σ_f(D) := λ(x , z). (f x , z) : Σ (x:A). D (f x) → Σ (y:B). D y`.
- **Identity system.** For `A` with `a : A`: a family `B` over `A` with
  `b : B a` such that for every family of types `P x y` (`x : A`,
  `y : B x`), the evaluation map
  `ev(a,b) : (Π (x:A). Π (y:B x). P x y) → P a b`, `h ↦ h a b`,
  **has a section**. Unpacked: for each `p : P a b` there is
  `f : Π (x:A). Π (y:B x). P x y` with an identification `f a b = p` —
  identification elimination with a *propositional* computation rule.
  Archetype: `B x := (a = x)`, `b := refl a`.
- **Dependent identity system.** Given an identity system `C` on `A` at
  `a` with `c : C a`, a family `B` over `A`, and `b : B a`: a family
  `D : Π (x:A). B x → (C x → 𝒰)` with `d : D a b c` such that
  `y ↦ D a y c` is an identity system on `B a` at `b`.
- **Observational equality on ℕ**, `Eq-ℕ : ℕ → ℕ → 𝒰`, by double
  induction: `Eq-ℕ 0 0 := 𝟏`, `Eq-ℕ 0 (n+1) := 𝟘`,
  `Eq-ℕ (m+1) 0 := 𝟘`, `Eq-ℕ (m+1) (n+1) := Eq-ℕ m n`. Reflexivity
  `refl-Eq-ℕ m : Eq-ℕ m m` by induction: `refl-Eq-ℕ 0 := ⋆`,
  `refl-Eq-ℕ (m+1) := refl-Eq-ℕ m`.
- **Observational equality of coproducts**,
  `Eq-coprod : (A + B) → (A + B) → 𝒰`, by double coproduct induction:
  `Eq-coprod (inl x) (inl x') := (x = x')`,
  `Eq-coprod (inr y) (inr y') := (y = y')`, and
  `Eq-coprod (inl x) (inr y') := Eq-coprod (inr y) (inl x') := 𝟘`.
  Reflexivity `ρ` by coproduct induction: `ρ (inl x) := refl x`,
  `ρ (inr y) := refl y`.
- **Embedding**: a map `f : A → B` such that
  `ap f : (x = y) → (f x = f y)` is an equivalence for every `x y : A`.
  Witnesses: `is-emb f`; embeddings: `A ↪ B := Σ (f : A → B). is-emb f`.
  The homotopical analogue of injectivity.

## Key results

- **Fibers of `tot f`** (lemma). For `f : Π (x:A). B x → C x` and
  `t : Σ (x:A). C x`: `fib (tot f) t ≃ fib (f (pr₁ t)) (pr₂ t)`.
  Proof by pattern matching: forward map
  `φ ((x , f x y) , ((x , y) , refl)) := (y , refl)`, inverse `ψ`, both
  homotopies `refl` — legitimate since the endpoint `t` is free, so
  unbased path induction reduces to the `refl` case.
- **Fiberwise equivalences are total equivalences** (theorem). For
  `f : Π (x:A). B x → C x`, TFAE: (i) `f` is a family of equivalences;
  (ii) `tot f` is an equivalence. Proof: each side is an equivalence
  iff its fibers are contractible; by the fiber lemma those fibers are
  equivalent, and equivalent types are simultaneously contractible.
- **Base change along an equivalence** (lemma). If `f : A → B` is an
  equivalence and `C` a family over `B`, then
  `σ_f(C) : Σ (x:A). C (f x) → Σ (y:B). C y` is an equivalence — since
  `fib (σ_f(C)) t ≃ fib f (pr₁ t)`. The **converse fails**: with
  `C := λ_. 𝟘` both total spaces are empty for arbitrary `f`.
- **`tot[f] g`** (theorem). If `f : A → B` is an equivalence and `g` a
  family of maps over `f`, TFAE: (i) `g` is a family of equivalences;
  (ii) `tot[f] g` is an equivalence. Proof: the triangle
  `tot[f] g = σ_f(D) ∘ tot g` commutes judgmentally, `σ_f(D)` is an
  equivalence, 3-for-2 reduces to the previous theorem.
- **THE FUNDAMENTAL THEOREM OF IDENTITY TYPES.** Let `A` be a type with
  `a : A`, `B` a family over `A` with `b : B a`, and
  `f : Π (x:A). (a = x) → B x` equipped with an identification
  `f a (refl a) = b`. TFAE:
  (i) `f` is a family of equivalences;
  (ii) `Σ (x:A). B x` is contractible;
  (iii) `(B , b)` is an identity system on `A` at `a`.
  In particular the canonical map `ind-= a b : Π (x:A). (a = x) → B x`
  (with `ind-= a b a (refl a) ≡ b` judgmentally) is a family of
  equivalences iff `Σ (x:A). B x` is contractible.

  Proof idea:
  - (i)⇔(ii): `f` is a fiberwise equivalence iff
    `tot f : Σ (x:A). a = x → Σ (x:A). B x` is an equivalence. The
    domain is the contractible singleton `(a , refl a)`; a map to/from
    a contractible type is an equivalence iff the other side is.
  - (ii)⇔(iii): for any `P` over `Σ B`, dependent currying
    `ev-pair : (Π (t : Σ B). P t) → Π (x:A). Π (y:B x). P x y` (always
    has a section) forms a triangle with `ev(a,b)` and evaluation at
    `(a , b)`; by 3-for-2 for sections, one has a section for all `P`
    iff the other does. Left = singleton induction of `Σ (x:A). B x` at
    `(a , b)`, i.e. contractibility; right = identity system.
- **Uniqueness.** (1) The map `f` above is unique up to homotopy: two
  candidates agreeing at `refl a` agree everywhere by based path
  induction. (2) Hence identity systems at `a` are unique up to
  canonical equivalence: `(B , b)` and `(C , c)` give
  `B x ≃ (a = x) ≃ C x` sending `b` to `c`. (Univalence upgrades this
  to an identification of families — `univalence.md`.)
- **Equality on the naturals** (theorem). For each `m n : ℕ`, the
  canonical map `(m = n) → Eq-ℕ m n` (path induction from `refl-Eq-ℕ m`)
  is an equivalence — by the fundamental theorem; miniature below.
- **Equivalences are embeddings** (theorem). For `e : A ≃ B` and
  `x : A`, `ap e : (x = y) → (e x = e y)` is an equivalence. Proof: by
  the fundamental theorem (family `y ↦ (e x = e y)`, `refl (e x)` at
  `y := x`) it suffices that `Σ (y:A). e x = e y` is contractible;
  compute `Σ (y:A). e x = e y ≃ Σ (y:A). e y = e x ≡ fib e (e x)` —
  `tot` of the fiberwise equivalence `inv`, then contractibility of the
  fiber of an equivalence.
- **Disjointness and computation of coproduct identity types**
  (theorem). For any `x x' : A` and `y y' : B`:
  `(inl x = inl x') ≃ (x = x')`, `(inl x = inr y') ≃ 𝟘`,
  `(inr y = inl x') ≃ 𝟘`, `(inr y = inr y') ≃ (y = y')`.
  Proof: the canonical map `(s = t) → Eq-coprod s t` exists by
  reflexivity; by the fundamental theorem it suffices that
  `Σ (t : A + B). Eq-coprod s t` is contractible for each `s`. By
  induction on `s` (cases similar), for `s := inl x`:

      Σ (t : A + B). Eq-coprod (inl x) t
        ≃ (Σ (x':A). Eq-coprod (inl x) (inl x')) + (Σ (y':B). Eq-coprod (inl x) (inr y'))
        ≃ (Σ (x':A). x = x') + (Σ (y':B). 𝟘)
        ≃ Σ (x':A). x = x'

  using distributivity of `Σ` over `+`, `Σ` over an empty family is
  `𝟘`, and `X + 𝟘 ≃ X`; the last type is the contractible singleton.
- **Structure identity principle** (theorem). Let `B` be a family over
  `A`, `a : A`, `b : B a`, `C` an identity system on `A` at `a` with
  `c : C a`, and `D : Π (x:A). B x → (C x → 𝒰)` with `d : D a b c`.
  TFAE:
  (i) every pointed family `(b = y) → D a y c` (`y : B a`) is a family
      of equivalences;
  (ii) `Σ (y : B a). D a y c` is contractible;
  (iii) `D` is a dependent identity system over `C` at `b`;
  (iv) every pointed family `((a , b) = (x , y)) → Σ (z : C x). D x y z`
      (`(x , y) : Σ B`) is a family of equivalences;
  (v) `Σ ((x , y) : Σ B). Σ (z : C x). D x y z` is contractible;
  (vi) `(x , y) ↦ Σ (z : C x). D x y z` is an identity system at
      `(a , b)`.
  Proof: (i)–(iii) and (iv)–(vi) by the fundamental theorem; (ii)⇔(v) by
  reassociation
  `Σ ((x , y) : Σ B). Σ (z : C x). D x y z ≃ Σ ((x , z) : Σ C). Σ (y : B x). D x y z`
  followed by collapse over the contractible base `Σ (x:A). C x` with
  center `(a , c)`. Slogan: identifications of structures are pairs of
  structure-preserving identifications.
- **Example: identity types of fibers.** For `f : A → B`, `b : B`,
  `(x , p) (y , q) : fib f b`:
  `((x , p) = (y , q)) ≃ fib (ap f) (p ∙ q⁻¹) := Σ (α : x = y). ap f α = p ∙ q⁻¹`.
  By the structure identity principle with `C y := (x = y)`,
  `c := refl x`, `D y q α := (ap f α = p ∙ q⁻¹)`: `d` is the
  right-inverse law `refl (f x) = p ∙ p⁻¹`, and the remaining goal
  `Σ (q : f x = b). refl (f x) = p ∙ q⁻¹` is equivalent (groupoid laws)
  to `Σ (q : f x = b). p = q`, a contractible singleton.
- **Retract and section formulations** (chapter exercises; freely
  usable). Let `B` be a family over `A` with base point `a : A`.
  (d) If each `B x` is a retract of `a = x` (fiberwise `s x`, `r x`
      with `r x ∘ s x ~ id`), then `B x ≃ (a = x)` for all `x`:
      functoriality of `tot` up to homotopy makes `Σ B` a retract of
      the contractible `Σ (x:A). a = x`; finish by the fundamental
      theorem applied to `r`.
  (e) Hence: if `f : Π (x:A). (a = x) → B x` has a fiberwise section,
      `f` is a family of equivalences. Corollary: if `ap f` has a
      section for each `x y : A`, then `f` is an embedding.
  (Shulman) `f` is an equivalence iff `f` is **path-split**: `f` has a
      section and `ap f (x , y)` has a section for all `x y`.

## Reasoning idioms

### The deployment recipe — characterizing `a = x`

To prove `(a = x) ≃ B x` for all `x : A` (with `a` fixed):

1. **Invent the family** `B : A → 𝒰` — the "observational" content of
   an identification, defined by induction on the shape of `A`:
   impossible cases compute to `𝟘`; reflexive cases are inhabited.
2. **Exhibit the reflexivity element** `b : B a`. Based path induction
   gives the canonical map `f : Π (x:A). (a = x) → B x` with
   `f a (refl a) ≡ b` judgmentally. (Any `f` with `f a (refl a) = b`
   works — only the propositional identification is needed.)
3. **Prove `Σ (x:A). B x` contractible**: center `(a , b)`; contraction
   `Π (x:A). Π (y : B x). (a , b) = (x , y)` by induction on `x` (case
   analysis on `y`): `𝟘`-elimination in impossible cases, `ap` of a step
   map on total spaces in the inductive step.
4. **Conclude** by the fundamental theorem: `f` is a family of
   equivalences, i.e. `(a = x) ≃ B x` for all `x`.

### Worked miniature: `(m = n) ≃ Eq-ℕ m n`

Fix `m : ℕ`; family `n ↦ Eq-ℕ m n`; reflexivity element `refl-Eq-ℕ m`.
By the fundamental theorem it suffices to show `Σ (n:ℕ). Eq-ℕ m n`
contractible.

- **Center**: `(m , refl-Eq-ℕ m)`.
- **Contraction**: construct
  `γ : Π (m n : ℕ). Π (e : Eq-ℕ m n). (m , refl-Eq-ℕ m) = (n , e)` by
  induction on `m` and `n`:
  - `γ 0 0 ⋆ := refl`.
  - `γ 0 (n+1) e` and `γ (m+1) 0 e`: here `Eq-ℕ m n ≡ 𝟘`, so use
    `ex-falso` (induction principle of `𝟘`).
  - Successor step: given `γ m n e : (m , refl-Eq-ℕ m) = (n , e)`,
    define `F : Σ (n:ℕ). Eq-ℕ m n → Σ (n:ℕ). Eq-ℕ (m+1) n` by
    `F (n , e) := (n+1 , e)`. Since
    `F (m , refl-Eq-ℕ m) ≡ (m+1 , refl-Eq-ℕ (m+1))` judgmentally, set
    `γ (m+1) (n+1) e := ap F (γ m n e)`.
- Specialize `γ` at the fixed `m`; conclude `(m = n) ≃ Eq-ℕ m n` for
  all `n`, then discharge `m`.

Two features make this work: `Eq-ℕ` computes on constructors (so
`𝟘`-cases are discharged judgmentally), and the successor step applies
`ap` with a total-space map that *judgmentally* preserves the center —
no transport needed.

### The contractibility toolkit for `Σ (x:A). B x`

- Atomic case: singletons `Σ (x:A). a = x`, center `(a , refl a)`.
- Reassociate/commute `Σ`-factors freely.
- Distribute over coproducts:
  `Σ (t : A + B). E t ≃ (Σ (x:A). E (inl x)) + (Σ (y:B). E (inr y))`;
  `Σ` over an empty family is `𝟘`; `X + 𝟘 ≃ X`.
- **Contractible-base collapse**: if `T` is contractible with center
  `t₀`, then `Σ (t:T). E t ≃ E t₀` (singleton induction) — the engine of
  SIP's (ii)⇔(v).
- **Retract trick**: exhibit `Σ B` as a retract of a known contractible
  type; recycle contractibilities through `tot` of fiberwise
  equivalences (a map out of a contractible type is an equivalence iff
  the codomain is contractible).

### Choosing the family `B`

| Target identity type | Family `B x` | Reflexivity element | Where the work goes |
|---|---|---|---|
| `m = n` in `ℕ` | `Eq-ℕ m n` | `refl-Eq-ℕ m` | double induction, `𝟘`-cases |
| `s = t` in `A + B` | `Eq-coprod s t` | `ρ s` | `Σ`-laws computation |
| `(a , b) = (x , y)` in `Σ B` | `Σ (z : C x). D x y z` | `(c , d)` | SIP: two contractibilities |
| `f = g` in `Π` | `f ~ g` | `refl-htpy f` | funext (`funext.md`) |
| `A = B` in `𝒰` | `A ≃ B` | `id` | univalence (`univalence.md`) |
| `base = x` in `S¹` | universal cover `ℰ x` | `0 : ℤ` | `circle.md` |

For inductive types the pattern is always: same constructor ↦ identity
types of the arguments (recursively), different constructors ↦ `𝟘` —
the "no confusion" property of constructors.

### The successor-map trick

In the inductive step of a contraction, never transport manually.
Package the step as a map `F` between total spaces (e.g.
`(n , e) ↦ (n+1 , e)`) with `F` of the old center *judgmentally* the
new center; the new contraction is then `ap F` of the old one — and
judgmental center preservation is exactly what makes `ap F` typecheck.

### Shortcuts around full contractibility

- To show `f : Π (x:A). (a = x) → B x` is a fiberwise equivalence, a
  **fiberwise section** suffices (retract formulation) — no direct
  contractibility proof needed.
- Conversely, a known fiberwise equivalence `(a = x) ≃ B x` immediately
  yields contractibility of `Σ (x:A). B x` — harvest contractibility
  from characterizations.

### Embedding tests

- Fix `x : A`, show `Σ (y:A). f x = f y` contractible, apply the
  fundamental theorem to `ap f`. For an equivalence this type is
  `fib e (e x)` up to `inv` and `tot`.
- Or: show `ap f (x , y)` has a section for all `x y`.
- Examples: every equivalence; `𝟘 → A`; `inl`, `inr` into coproducts.
  A composite of two embeddings is an equivalence only if both already
  were.

## Pitfalls

- **Fix the base point.** The theorem characterizes `a = x` for one
  fixed `a` as `x` varies. Contractibility is a single global statement
  about `Σ (x:A). B x` — do not try to prove each `B x` contractible
  (often empty, e.g. `Eq-ℕ 0 1 ≡ 𝟘`), and do not expect a
  characterization at one `x` to transfer to another.
- **Total space, not fibers.** The goal is contractibility of
  `Σ (x:A). B x`, never of `B x`. Sanity check: the putative center must
  be `(a , b)` itself.
- **Propositional base condition suffices — and is required.** `f` need
  not be the canonical `ind-= a b`; any `f` with `f a (refl a) = b`
  works. An unpointed fiberwise map proves nothing.
- **Identity systems compute only propositionally.** The section of
  `ev(a,b)` yields `f a b = p`, not `≡`; only genuine `ind-=` computes.
- **`tot` vs `σ_f`.** The iff is for `tot f` (base fixed). Base change
  is one-way only; the converse fails already for `C := λ_. 𝟘`.
- **`tot` is functorial only up to homotopy.** `tot (g ∘ f)` and
  `tot g ∘ tot f` are homotopic, not judgmentally equal.
- **The contraction is the work.** The canonical map is free; the proof
  burden is the contraction — for `ℕ` a *double* induction on
  `Π (m n : ℕ). Π (e : Eq-ℕ m n). …`, specialized afterward. Mismatched
  cases go by `𝟘`-elimination, possible only because the family was
  defined to compute to `𝟘` there.
- **Equivalence, not judgment.** The output `(m = n) ≃ Eq-ℕ m n` is type
  data, not `≡`; that `m = n` is a proposition needs Hedberg.
- **Embeddings are not equivalences.** `is-emb f` means `ap f` is a
  fiberwise equivalence; `inl` and `𝟘 → A` are embeddings without being
  equivalences. And "every equivalence is an embedding" is proved *by*
  the fundamental theorem — don't assume it circularly.
- **Don't path-induct on a fixed path.** The fundamental theorem reasons
  about `a = x` *as `x` varies*; with `x` fixed at a specific element,
  path induction does not apply and no characterization theorem helps.

## See also

- `identity-types.md` — `ind-=`, singleton contractibility, groupoid laws, the raw `Σ`-identity characterization SIP refines.
- `equivalences.md` — `fib f b`, contractible maps, `is-equiv`, 3-for-2, retracts: the fiber-of-`tot` technique builds on these.
- `inductive-types.md` — `ℕ`, coproducts, `𝟘`/`𝟏`, the `Σ`/coproduct laws used in the disjointness computation.
- `dependent-type-theory.md` — `Σ`- and `Π`-types, pattern matching, evaluation maps.
- `universes.md` — families valued in `𝒰` defined by induction: the setting for `Eq-ℕ` and `Eq-coprod`.
- `truncation-levels.md` — embeddings have propositional fibers; Hedberg (decidable equality ⇒ set) turns `Eq-ℕ` into "`ℕ` is a set".
- `funext.md` — the identity system of `Π`-types: `(f = g) ≃ (f ~ g)`, by the same pattern.
- `univalence.md` — the identity system of the universe: `(A = B) ≃ (A ≃ B)`; uniqueness of identity systems as identifications; the general SIP.
- `logic-truncation.md` — disjointness read logically: `¬ (inl x = inr y)`; `≠` as a mere proposition.
- `quotients.md` — identity types of set quotients, same methodology.
- `finite-types.md` — `Fin k` equality via `Eq-ℕ`; counting identifications.
- `groups.md` — SIP for groups: isomorphisms as identifications.
- `w-types.md` — identity types of W-types: another deployment.
- `circle.md` — the universal cover `ℰ` and `Ω S¹ ≃ ℤ`: the flagship fundamental-theorem proof with a non-set family.
- `number-theory.md` — decidability of equality on `ℕ`, arithmetic reasoning built on `Eq-ℕ`.
