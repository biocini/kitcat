# Dependent type theory and Π-types

Dependent type theory is the formal system beneath everything in this library: a collection of inference rules whose derivations construct types, elements, and judgmental equalities in context. This digest covers the structural core — judgments, contexts, families and sections, substitution, weakening, the variable rule — and the first type former, the dependent function type `Π (x:A). B(x)`, in full formal detail. Everything here is bare Martin-Löf type theory: no identity types, no funext, no univalence. Note that Rijke adopts a *judgmental* η-rule; consequently the category laws for ordinary functions (associativity, unit laws) hold by `≡`, not merely up to `=`.

## Key definitions

### Judgments and inference rules

An **inference rule** has finitely many judgments as premises above a horizontal line and a single judgment as conclusion below. A **derivation** is a finite tree of valid inference-rule instances: hypotheses at the leaves, conclusion at the root. Any derivation with hypotheses `ℋ₁, …, ℋₙ` and conclusion `𝒞` licenses using

```
ℋ₁   ℋ₂   …   ℋₙ
-----------------
        𝒞
```

as a *derived rule* in all later derivations — this convention keeps proof trees short.

There are exactly four kinds of **judgment**, each of the form `Γ ⊢ 𝒥` with `Γ` a context and `𝒥` a judgment thesis:

```
Γ ⊢ A type          A is a well-formed type in context Γ
Γ ⊢ A ≡ B type      A and B are judgmentally equal types in context Γ
Γ ⊢ a : A           a is an element of type A in context Γ
Γ ⊢ a ≡ b : A       a and b are judgmentally equal elements of A in Γ
```

`≡` is not a type: it cannot occur in a context, be hypothesized, or be reasoned about internally. `:=` introduces a definition (see the definition convention below).

### Contexts

A **context** is a finite list of variable declarations

```
x₁:A₁,  x₂:A₂(x₁),  …,  xₙ:Aₙ(x₁,…,xₙ₋₁)
```

such that for each `1 ≤ k ≤ n` the judgment

```
x₁:A₁, …, xₖ₋₁:Aₖ₋₁(x₁,…,xₖ₋₂) ⊢ Aₖ(x₁,…,xₖ₋₁) type
```

is derivable. Well-formedness is checked recursively, left to right: each declared type may depend on all previously declared variables. The empty context (length 0) declares no variables and is vacuously a context; a length-1 list `x₁:A₁` is a context iff `A₁` is a type in the empty context. No variable name may be declared twice. Variables are hypothetical elements; the variable rule (δ below) makes them usable as elements.

### Families, sections, fibers

- A **(type) family** over `A` in context `Γ` is a type in the extended context: `Γ, x:A ⊢ B(x) type`. One also says `B(x)` is a type *indexed* by `x:A`. (The identity type `a = x` in context `Γ, x:A`, for fixed `a : A`, is the motivating example — see identity-types.md.)
- A **section** of the family `B` over `A` is an element in the extended context: `Γ, x:A ⊢ b(x) : B(x)`. Read `b` as an operation or program `x ↦ b(x)`, or as a choice of an element of each `B(x)`.
- For `Γ ⊢ a : A`, the **fiber** of `B` at `a` is `B(a) := B[a/x]`; the **value** of a section `b` at `a` is `b(a) := b[a/x]`.
- The **constant (trivial) family** `B` over `A` is obtained by weakening `Γ ⊢ B type` to `Γ, x:A ⊢ B type`.

Ambient variables in `Γ` are routinely suppressed: "family `B` over `A` in context `Γ`" means `A`, `B`, and sections may all additionally depend on `Γ`'s variables.

### The structural rules

Six groups. `𝒥` denotes a generic judgment thesis (any of the four kinds); `Δ` an arbitrary further context extension.

**1. Well-formedness presuppositions.** Any judgment guarantees the well-formedness of everything occurring in it; these rules may be used freely in derivations:

```
Γ, x:A ⊢ B(x) type      Γ ⊢ a : A        Γ ⊢ A ≡ B type      Γ ⊢ A ≡ B type
------------------      ----------       --------------      --------------
   Γ ⊢ A type           Γ ⊢ A type       Γ ⊢ A type          Γ ⊢ B type

Γ ⊢ a ≡ b : A           Γ ⊢ a ≡ b : A
--------------          --------------
Γ ⊢ a : A               Γ ⊢ b : A
```

**2. Judgmental equality is an equivalence relation** — reflexivity, symmetry, transitivity, for types and for elements:

```
Γ ⊢ A type              Γ ⊢ A ≡ B type            Γ ⊢ A ≡ B type   Γ ⊢ B ≡ C type
-----------             -------------             ------------------------------------
Γ ⊢ A ≡ A type          Γ ⊢ B ≡ A type                  Γ ⊢ A ≡ C type

Γ ⊢ a : A               Γ ⊢ a ≡ b : A             Γ ⊢ a ≡ b : A    Γ ⊢ b ≡ c : A
-----------             -------------             ------------------------------------
Γ ⊢ a ≡ a : A           Γ ⊢ b ≡ a : A                   Γ ⊢ a ≡ c : A
```

**3. Variable conversion.** A declared variable's type may be replaced by a judgmentally equal type:

```
Γ ⊢ A ≡ A' type    Γ, x:A, Δ ⊢ 𝒥
--------------------------------
        Γ, x:A', Δ ⊢ 𝒥
```

**4. Substitution.** Substituting `a : A` for `x` simultaneously everywhere — in types and elements alike:

```
Γ ⊢ a : A    Γ, x:A, Δ ⊢ 𝒥
-------------------------- S
    Γ, Δ[a/x] ⊢ 𝒥[a/x]
```

with congruence rules: judgmentally equal substitutes yield judgmentally equal results —

```
Γ ⊢ a ≡ a' : A    Γ, x:A, Δ ⊢ B type
--------------------------------------
   Γ, Δ[a/x] ⊢ B[a/x] ≡ B[a'/x] type

Γ ⊢ a ≡ a' : A    Γ, x:A, Δ ⊢ b : B
-------------------------------------
 Γ, Δ[a/x] ⊢ b[a/x] ≡ b[a'/x] : B[a/x]
```

**5. Weakening.** Any judgment survives the insertion of a fresh variable of any well-formed type:

```
Γ ⊢ A type    Γ, Δ ⊢ 𝒥
---------------------- W
    Γ, x:A, Δ ⊢ 𝒥
```

Weakening `Γ ⊢ B type` by `A` yields the constant family `Γ, x:A ⊢ B type`.

**6. The variable rule (generic element).** A declared variable is an element of its declared type:

```
Γ ⊢ A type
---------- δ
Γ, x:A ⊢ x : A
```

This ensures hypothetical elements really are elements; it also supplies the identity function (below).

### Π-types: formation, introduction, elimination, computation

Every type former in the book is specified by the same template: a **formation** rule, an **introduction** rule, an **elimination** rule, **computation** rules describing how elimination acts on introduction, plus **congruence** rules stating each construction respects `≡`. For dependent function types:

**Formation.** From a family over `A`, form the type of dependent functions:

```
Γ, x:A ⊢ B(x) type
-------------------- Π
Γ ⊢ Π (x:A). B(x) type
```

```
Γ ⊢ A ≡ A' type    Γ, x:A ⊢ B(x) ≡ B'(x) type
--------------------------------------------- Π-eq
  Γ ⊢ Π (x:A). B(x) ≡ Π (x:A'). B'(x) type
```

**Introduction (λ-abstraction).** From a section, form a dependent function; `λ` binds the variable `x` in `b`:

```
Γ, x:A ⊢ b(x) : B(x)
---------------------- λ
Γ ⊢ λx. b(x) : Π (x:A). B(x)
```

```
Γ, x:A ⊢ b(x) ≡ b'(x) : B(x)
------------------------------- λ-eq
Γ ⊢ λx. b(x) ≡ λx. b'(x) : Π (x:A). B(x)
```

Informally one writes `x ↦ b(x)` for `λx. b(x)` (e.g. `n ↦ n²`).

**Elimination (evaluation).** A dependent function, applied to a generic argument, yields a section:

```
Γ ⊢ f : Π (x:A). B(x)
--------------------- ev
Γ, x:A ⊢ f(x) : B(x)
```

```
Γ ⊢ f ≡ f' : Π (x:A). B(x)
-------------------------- ev-eq
Γ, x:A ⊢ f(x) ≡ f'(x) : B(x)
```

**Computation (β and η).** Evaluation and λ-abstraction are mutual inverses, judgmentally:

```
Γ, x:A ⊢ b(x) : B(x)
----------------------- β
Γ, x:A ⊢ (λy. b(y))(x) ≡ b(x) : B(x)
```

```
Γ ⊢ f : Π (x:A). B(x)
----------------------- η
Γ ⊢ λx. f(x) ≡ f : Π (x:A). B(x)
```

The bound-variable name is irrelevant (`λy. b(y)` versus `λx. b(x)`). The η-rule asserts that *every* element of a Π-type is judgmentally a λ-abstraction — there are no "non-functional" elements of a Π-type.

**Application at a specific argument** is the derived rule (ev followed by substitution):

```
Γ ⊢ f : Π (x:A). B(x)    Γ ⊢ a : A
----------------------------------
        Γ ⊢ f(a) : B(a)
```

Note that the codomain is substituted too: `f(a) : B(a)`, never `B(x)`.

### Ordinary function types

For `A` and `B` types in context `Γ`, weaken `B` by `A`, then Π-form, then define:

```
Γ ⊢ A type   Γ ⊢ B type
----------------------- W
    Γ, x:A ⊢ B type
----------------------- Π
Γ ⊢ Π (x:A). B type
----------------------- definition
Γ ⊢ A → B := Π (x:A). B type
```

`A → B` is the type of **(ordinary) functions** from domain `A` to codomain `B`, also written `B^A`. Via the element conversion rule, the Π-rules specialize to →-rules: formation from the two premises `Γ ⊢ A type` and `Γ ⊢ B type`; λ, ev, β, η with `B` not depending on `x`.

**Definition convention.** Whenever a derivation ends in `Γ ⊢ a : A` from hypotheses `ℋ₁, …, ℋₙ`, one may append a definitional line `Γ ⊢ c := a : A` introducing a new constant `c`; thereafter the rules "from `ℋ₁, …, ℋₙ` conclude `Γ ⊢ c : A`" and "conclude `Γ ⊢ c ≡ a : A`" are valid — `c` unfolds definitionally. (Types may be defined the same way, as with `A → B` above.) Every `X := …` definition in the book carries this force.

**Currying conventions.** Iterated function types represent multi-argument functions: `f : A → (B → C)` takes `x : A`, returning `f(x) : B → C`, which takes `y : B`. Write `f(x, y) := f(x)(y)`. Similarly `Π (x,y:A). C(x,y) := Π (x:A). Π (y:A). C(x,y)`.

**The basic combinators** (each defined via the convention above):

- **Identity function:** `id_A := λx. x : A → A`, from δ then λ.
- **Composition:** `comp := λg. λf. λx. g(f(x)) : (B → C) → ((A → B) → (A → C))`; write `g ∘ f := comp g f`. Construction: from generic `g : B → C` and `f : A → B` (via δ) and generic `x : A`, evaluate twice to get `g(f(x)) : C` (ev + substitution), then λ-abstract `x`, `f`, `g` in turn.
- **Constant map:** in context `Γ, y:B`, `const_y := λx. y : A → B`.
- **Swap:** given `Γ ⊢ A type`, `Γ ⊢ B type`, and `Γ, x:A, y:B ⊢ C(x,y) type`,
  `σ := λf. λy. λx. f(x)(y) : (Π (x:A). Π (y:B). C(x,y)) → (Π (y:B). Π (x:A). C(x,y))`.

## Key results

All of the following are derived in bare type theory — no axioms anywhere in this file.

1. **Element conversion (derivable).** From `Γ ⊢ A ≡ A' type` and `Γ ⊢ a : A` one derives `Γ ⊢ a : A'`; the congruence version (`Γ ⊢ a ≡ b : A` to `Γ ⊢ a ≡ b : A'`) likewise. Sketch: symmetry gives `Γ ⊢ A' ≡ A type`; δ gives `Γ, x:A' ⊢ x : A'`; variable conversion (converting the declaration `x:A'` to `x:A`) gives `Γ, x:A ⊢ x : A'`; substitute `a` for `x`. The congruence version goes through the substitution congruence rule with the constant family `A'`. Element conversion is used silently whenever a defined type (like `A → B`) is unfolded.

2. **Change of variables (derivable).** For `x'` fresh: from `Γ, x:A, Δ ⊢ 𝒥` derive `Γ, x':A, Δ[x'/x] ⊢ 𝒥[x'/x]`. Sketch: δ for `x'`; weaken the premise by `x':A`; substitute the generic `x'` for `x`.

3. **Interchange (derivable).** If `Γ ⊢ B type` — crucially, `B` does not depend on `x` — then from `Γ, x:A, y:B, Δ ⊢ 𝒥` derive `Γ, y:B, x:A, Δ ⊢ 𝒥`. Sketch: rename `y` to a fresh `y'`, weaken to `Γ, y:B, x:A, y':B, Δ[y'/y] ⊢ 𝒥[y'/y]`, substitute the generic `y` for `y'`.

4. **Category laws for functions hold judgmentally.**
   - Associativity: from `Γ ⊢ f : A → B`, `Γ ⊢ g : B → C`, `Γ ⊢ h : C → D` derive
     `Γ ⊢ (h ∘ g) ∘ f ≡ h ∘ (g ∘ f) : A → D`.
     Proof: both `((h ∘ g) ∘ f)(x)` and `(h ∘ (g ∘ f))(x)` β-reduce to `h(g(f(x)))`; finish with λ-eq and η.
   - Unit laws: from `Γ ⊢ f : A → B` derive `Γ ⊢ id_B ∘ f ≡ f : A → B` and `Γ ⊢ f ∘ id_A ≡ f : A → B`.
     Proof: `id_B ∘ f ≡ λx. id_B(f(x)) ≡ λx. f(x) ≡ f` — β twice, then η; the right unit law is the same pattern.

5. **Judgmental extensionality (consequence of η).** From `Γ ⊢ f : Π (x:A). B(x)`, `Γ ⊢ g : Π (x:A). B(x)`, and `Γ, x:A ⊢ f(x) ≡ g(x) : B(x)`, derive `Γ ⊢ f ≡ g : Π (x:A). B(x)`. Proof: `f ≡ λx. f(x) ≡ λx. g(x) ≡ g` by η, λ-eq, η. This is the workhorse behind every `≡` between functions.

6. **Laws for const.** From `Γ ⊢ f : A → B`: `Γ, z:C ⊢ const_z ∘ f ≡ const_z : A → C` (both sides β-reduce to `λx. z`). From `Γ ⊢ g : B → C`: `Γ, y:B ⊢ g ∘ const_y ≡ const_{g(y)} : A → C` (both reduce to `λx. g(y)`).

7. **Swap is an involution, judgmentally.** With σ as above:
   `Γ ⊢ σ ∘ σ ≡ id : (Π (x:A). Π (y:B). C(x,y)) → (Π (x:A). Π (y:B). C(x,y))`.
   Proof: `σ(σ(f)) ≡ λx. λy. f(x)(y) ≡ f` by β twice and η, then λ-eq + η.

## Reasoning idioms

- **To construct an element of `Π (x:A). B(x)`:** move `x:A` into the context and construct a section `b(x) : B(x)`; finish with λ-abstraction. λ is the only introduction rule, and η guarantees every element of a Π-type is judgmentally a λ — so "assume `x : A`; construct …" is the complete, canonical opening move for any Π-goal.
- **To use `f : Π (x:A). B(x)` at a concrete `a : A`:** evaluate, then substitute, giving `f(a) : B(a)`. Restate the goal type as the fiber `B(a)` *before* constructing — the codomain of a dependent function changes with the argument.
- **To prove a *judgmental* equality of functions:** introduce a generic `x : A`, compute both sides with β and definitional unfolding until they coincide syntactically, then close with λ-eq and one η per side: `f ≡ λx. f(x) ≡ λx. g(x) ≡ g`. Associativity, the unit laws, the const-laws, and `σ ∘ σ ≡ id` are all exactly this. Chain `≡`-steps freely: reflexivity/symmetry/transitivity plus the congruence rules make `≡` a calculational relation.
- **To define a named combinator:** derive `Γ ⊢ a : A` — typically by introducing generic function arguments via δ, evaluating them at generic variables, and λ-abstracting in reverse argument order, as in the construction of `comp` — then append the definitional line `Γ ⊢ c := a : A`. Thereafter `c` is a constant that unfolds judgmentally; never re-derive it.
- **To build a family over `A` from a bare type `B`:** weaken. The constant family is what makes `A → B` a special case of Π and what lets non-dependent constructions live inside dependent ones.
- **To ignore an unused hypothesis, or reuse a judgment in a bigger context:** weaken. **To rename a variable:** change of variables. **To reorder two independent hypotheses:** interchange. All three are derived rules — invoke them without unfolding their derivations.
- **To discharge well-formedness obligations:** extract them from judgments already in hand via the presupposition rules (e.g. `Γ ⊢ a : A` yields `Γ ⊢ A type`) rather than rederiving them.
- **To represent a multi-argument (dependent) function:** iterate Π/`→` to the right (currying); application associates to the left, `f(x, y) := f(x)(y)`; define by nesting λs in argument order, `λx. λy. …`.

## Pitfalls

- **η is not funext.** η gives `λx. f(x) ≡ f`, a judgmental equality. It does *not* produce an element of `(f ~ g) → (f = g)`: identifying functions propositionally requires the funext axiom (funext.md). From pointwise *judgmental* equality you do get `f ≡ g` (result 5), hence `refl f : f = g`; from a pointwise *propositional* equality `f ~ g` you get nothing without funext. Keep the two extensionality principles strictly apart.
- **The elimination rule outputs a section, not an application.** `ev` yields `Γ, x:A ⊢ f(x) : B(x)` in the *extended* context. Applying `f` to a specific `a : A` is the derived two-premise rule, and the result has type `B(a)` — the substituted fiber. Writing `f(a) : B(x)` or `f(a) : B` for a dependent `f` is ill-typed.
- **Sections are not functions.** A section `Γ, x:A ⊢ b(x) : B(x)` becomes an element of the Π-type only after λ-abstraction; conversely `f : Π (x:A). B(x)` becomes a section only after evaluation. β and η are exactly the two directions of this correspondence — invoke them deliberately when translating between the "open term in context" and "function" points of view.
- **`≡` cannot be hypothesized.** Contexts contain only declarations `x : A`. You cannot assume `x ≡ y`, cannot suppose two types judgmentally equal, cannot do induction over a judgmental equality. To reason under an equality hypothesis, use identity types (`p : x = y`) and path induction (identity-types.md).
- **Substitution congruence needs `≡`, not `=`.** From `Γ ⊢ a ≡ a' : A`, substitution gives `B(a) ≡ B(a')`. From a mere identification `p : a = a'` you only get transport `tr B p : B(a) → B(a')` — a map between fibers, not a definitional equality. Never rewrite a goal type by `p` as though it were `≡`.
- **Interchange requires independence.** `Γ, x:A, y:B(x)` cannot be swapped: the type of `y` mentions `x`. Only when `B` is a type in `Γ` alone may the order be exchanged — which is also why σ needs `B` independent of `x` (though `C(x, y)` may depend on both).
- **Freshness side conditions.** Weakening and change of variables require the new variable name to be undeclared in the ambient context; a context never declares a name twice. α-rename first rather than shadow.
- **Two notions of "fiber".** Here: the fiber `B(a) := B[a/x]` of a *family*. Later: the homotopy fiber `fib f b := Σ (x:A). f(x) = b` of a *map* (equivalences.md). They are related but distinct notions sharing one word.
- **Premises are debts.** Formation and structural rules carry well-formedness premises (`Π` needs `Γ, x:A ⊢ B(x) type`; `S` needs `Γ ⊢ a : A`; `W` needs `Γ ⊢ A type`). Informal proofs discharge them silently, but when a construction fails to typecheck, a missing premise is the first thing to hunt.
- **Do not expect `≡` where later chapters only have `=`.** Function composition is associative and unital *by definition*, because `∘` is defined by λ-abstraction; path concatenation `∙` is associative and unital only up to higher paths, because it is defined by path induction (identity-types.md). The difference in strength comes from the difference in definition principle.

## See also

- identity-types.md — the family `x ↦ (a = x)` over `A` is the motivating type family; transport `tr B p : B(a) → B(a')` is the `=`-level substitute for substitution into a family.
- inductive-types.md — 𝟘, 𝟏, bool, ℕ, Σ, coproducts: each is specified by the same formation / introduction / elimination / computation / congruence template as Π here.
- universes.md — with a universe in play, a family over `A` is a map `B : A → 𝒰` and fibers are literally `B a`; families can then be defined by induction.
- funext.md — the propositional extensionality principle that bare type theory lacks: `(f = g) ≃ (f ~ g)`, and its relation to the judgmental η-rule.
- equivalences.md — `id`, `comp`, `const`, and σ reappear as the first examples of equivalences; 3-for-2 reasoning about `∘`.
- truncation-levels.md — closure of propositions, sets, and k-types under Π (uses funext).
- logic-truncation.md — reading `Π` as universal quantification and `→` as implication; why `Σ`-style existence must be truncated.
- fundamental-theorem.md — characterizing identity types, including `(f = g) ≃ (f ~ g)` under funext.
