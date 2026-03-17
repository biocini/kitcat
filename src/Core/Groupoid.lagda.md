Lane Biocini
March 2026

Representability equivalence for the path groupoid.

`Core.Groupoid` proves `PathP A x y ≃ (∀ w → w ≡ x → ∀ z → y ≡ z
→ PathP A w z)` where the loose cell `q : PathP A x y` is
represented. Here we prove the dual equivalence at constant type
family: `w ≡ x ≃ (∀ y → x ≡ y → ∀ z → y ≡ z → w ≡ z)` where the
tight cell `a : w ≡ x` is represented.

The contractible fiber `Σ w, ∀ y → x ≡ y → ∀ z → y ≡ z → w ≡ z`
has center `(x, λ y q z r → pcom refl q r)` — the identity point
paired with standard binary composition `_∙_`.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Core.Groupoid where

open import Core.Base
open import Core.Type using (Level; Type; _₊; _∘_)
open import Core.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Core.Kan
open import Core.Equiv.Base
  using (is-equiv; iso→equiv; is-contr-equiv; _≃_; Equiv; eqv-fibers)
open import Core.Equiv.Properties using (Σ-equiv-snd; esym)
open import Core.Transport.Base using (Singl-contr; contr-ind)
open import Core.Transport.J using (subst)

private variable
  u : Level

```

## Reverse singleton contractibility

`Singl-contr x` gives `is-contr (Σ y, x ≡ y)`. We need the reverse:
`is-contr (Σ w, w ≡ x)`. The center is `(x, refl)` and the
contraction uses the connection `a (~ i ∨ j)`.

```agda

Singl-contr-cofan
  : ∀ {u} {A : Type u} (x : A)
  → is-contr (Σ w ∶ A , w ≡ x)
Singl-contr-cofan x .center = x , refl
Singl-contr-cofan x .paths (w , a) i =
  a (~ i) , λ j → a (~ i ∨ j)

module _ {A : Type u} where
  emb : {w x : A} → w ≡ x
      → ∀ y → x ≡ y → ∀ z → y ≡ z → w ≡ z
  emb a y q z r = pcom (sym a) q r

```

### Equivalence

```agda
  emb-parametric : ∀ {w x} → (f : (y : A) → x ≡ y → (z : A) → y ≡ z → w ≡ z) → emb (f x refl x refl) ≡ f
  emb-parametric {w} {x} f i y q z r j = hcom (∂ j ∨ i) λ where
    k (i = i1) → f y q (r (j ∨ k)) (λ m → r ((j ∨ k) ∧ m)) (j ∨ ~ k)
    k (j = i0) → f (q i) (λ m → q (i ∧ m)) (pfil refl q r i k) (λ m → pfil refl q r i (k ∧ m)) (~ k)
    k (j = i1) → r (i ∨ k)
    k (k = i0) → conn (λ m → q (i ∨ m)) (λ m → r (i ∧ m)) i j

  emb-equiv : {w x : A} → is-equiv (emb {w} {x})
  emb-equiv {(w)} {(x)} = iso→equiv emb inv sec emb-parametric .snd
    where
      inv : (∀ y → x ≡ y → ∀ z → y ≡ z → w ≡ z) → w ≡ x
      inv f = f x refl x refl

      sec : (a : w ≡ x) → inv (emb a) ≡ a
      sec a = pcom.unique (sym a) refl refl
        (a , λ i j → a (~ j ∨ i))

      retr
        : (f : ∀ y → x ≡ y → ∀ z → y ≡ z → w ≡ z)
        → emb (f x refl x refl) ≡ f
      retr f = emb-parametric f

```

### Representable type

```agda

  is-representable : A → Type u
  is-representable x =
    Σ w ∶ A , ∀ y → x ≡ y → ∀ z → y ≡ z → w ≡ z

```

### Contractible fiber

Transport `Singl-contr-rev x : is-contr (Σ w, w ≡ x)` across
`emb-equiv` to get `is-contr (is-representable x)`.

```agda

  representable-contr : {x : A} → is-contr (is-representable x)
  representable-contr {x} = is-contr-equiv (esym (Σ-equiv-snd λ _ → emb , emb-equiv)) (Singl-contr-cofan x)

```

## Computation laws

The center of `representable-contr` should be `(x, cat.composite)`:
the identity paired with standard binary composition.

An equivalence of types maps `(x, refl)` to `(x, emb refl)`. And `emb
refl y q z r ≡ pcom refl q r ≡ cat.composite q r`. The center's
notion of composition is cat.composite by definition.

```agda

  private
    center-point : {x : A} → representable-contr {x} .center .fst ≡ x
    center-point = refl

    center-op
      : {x : A} (y : A) (q : x ≡ y) (z : A) (r : y ≡ z)
      → representable-contr {x} .center .snd y q z r
        ≡ cat.composite q r
    center-op y q z r = refl

```

## Binary composition as center extraction

`_∙'_` is defined by extracting the center's operation. It computes
as `pcom refl q r`, agreeing with `_∙_` definitionally.

```agda

    _∙'_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    _∙'_ {x} q r = representable-contr {x} .center .snd _ q _ r

    ∙'-is-∙ : {x y z : A} (q : x ≡ y) (r : y ≡ z)
             → q ∙' r ≡ q ∙ r
    ∙'-is-∙ q r = refl

```

## Fiber uniqueness and the Kraus argument

Every element `(w, F)` of `is-representable x` is connected to the center
`(x, cat.composite)` by a path in `is-representable x`. Projecting with
`ap fst` yields a path `x ≡ w` — the tight cell is recoverable from the action.

```agda

  recover : {x w : A}
    → (F : ∀ y → x ≡ y → ∀ z → y ≡ z → w ≡ z)
    → x ≡ w
  recover {x} F =
    ap fst (representable-contr {x} .paths (_ , F))

  recover-center : {x : A}
    → recover (representable-contr {x} .center .snd) ≡ refl
  recover-center {x} =
    ap (ap fst)
      (is-contr→loop-is-refl representable-contr)
    where
      is-contr→loop-is-refl
        : ∀ {u} {A : Type u} (c : is-contr A)
        → c .paths (c .center) ≡ refl
      is-contr→loop-is-refl c =
        is-contr→is-set c _ _ (c .paths (c .center)) refl

```

## Groupoid laws from the fiber

Every groupoid law can be derived from the contractible fiber
by comparing elements of `is-representable x` via `is-contr→is-prop`.

```agda

  private
    is-representable-is-prop : {x : A} → is-prop (is-representable x)
    is-representable-is-prop = is-contr→is-prop representable-contr

```

## The fiber path as master data

For `p : w ≡ x`, the element `(w, emb p)` is in `is-representable x`.
The fiber path `σ p` connects the center `(x, _∙_)` to `(w, emb p)`:

```agda

    σ :  {x : A} {w : A} (p : w ≡ x) → representable-contr .center ≡ (w , emb p)
    σ {w} p = representable-contr .paths (w , emb p)

```

The first component of `σ p` recovers a path `x ≡ w`:

The second component evaluated at arguments `(y, q, z, r)` gives
a PathP over `σ-fst p` connecting the center's value `q ∙ r` to
`emb p y q z r = pcom (sym p) q r`:

```agda

    σ-snd : {w x : A} (p : w ≡ x)
      → (y : A) (q : x ≡ y) (z : A) (r : y ≡ z)
      → PathP (λ i → ap fst (σ p) i ≡ z)
            (q ∙ r)
            (pcom (sym p) q r)
    σ-snd p y q z r i = σ p i .snd y q z r

```

## Identifying σ-fst with sym p

The retraction `sec p : emb p x refl x refl ≡ p` (i.e.,
`pcom (sym p) refl refl ≡ p`) connects the fiber evaluation at
identity arguments to `p` itself. Combined with the center's
identity evaluation `refl ∙ refl`, this identifies `σ-fst p`
with `sym p`.

Evaluating `σ-snd` at `(x, refl, x, refl)`:

```agda

    σ-at-idn : {w x : A} (p : w ≡ x)
      → PathP (λ i → ap fst (σ p) i ≡ x)
            (refl ∙ refl)
            (pcom (sym p) refl refl)
    σ-at-idn p = σ-snd p _ refl _ refl

```

The right endpoint `pcom (sym p) refl refl` equals `p` by `sec`.
The left endpoint `refl ∙ refl` equals `refl` by `pcom.unit refl`
(or `idem`). So `σ-at-idn` is a PathP from `refl` to `p`
(up to these identifications) over `σ-fst p`.

This means `σ-fst p` is the path that transports `refl` to `p`,
i.e., `σ-fst p ≡ sym p` (modulo the endpoint identifications).

We construct an explicit path from center `(x, emb refl)` to
`(w, emb p)` whose first component is definitionally `sym p`. Since
`is-representable x` is contractible (hence a set), `σ p ≡ explicit`,
and projecting gives `ap fst (σ p) ≡ sym p`.

```agda

    σ-fst-is-sym : {w x : A} (p : w ≡ x) → ap fst (σ p) ≡ sym p
    σ-fst-is-sym {w} p = ap (ap fst)
      (is-contr→is-set representable-contr _ _ (σ p) explicit)
      where
        explicit : representable-contr .center ≡ (w , emb p)
        explicit i = sym p i , λ y q z r → pcom (λ j → p (~ i ∨ ~ j)) q r

```

## Groupoid laws as fiber sections

These laws use HComposite contractibility (`pcom.unique` and
`HComposite.unique`), the heterogeneous generalization of
`representable-contr`. Each law provides a witness
`(target, HCell-fill)` and uses uniqueness to derive
`pcom ... ≡ target`.

```agda

  module _ {A : Type u} where
    unitr : {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
    unitr p = pcom.unit p

    unitl : {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
    unitl p = pcom.ideml p

    invl : {x y : A} (p : x ≡ y) → sym p ∙ p ≡ refl
    invl p = pcom.unique refl (sym p) p
      (refl , λ i j → p (~ i ∨ j))

    invr : {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
    invr p = pcom.unique refl p (sym p)
      (refl , λ i j → p (i ∧ ~ j))

```

## Derived operations

`noy` specializes the left context to identity. `yon` specializes
the right context to identity. Binary specializations of the
ternary `emb`, paralleling Cat.Virtual's `noy` and `yon`.

```agda

  noy : {w x : A} → w ≡ x → ∀ z → x ≡ z → w ≡ z
  noy a z r = emb a _ refl z r

  yon : {w x : A} → w ≡ x → ∀ y → x ≡ y → w ≡ y
  yon a y q = emb a y q _ refl

```

### Embedding property

Since `emb` is a full equivalence, its fibers are contractible.
The pointwise formulation has center `(a, refl)` — the tight cell
itself with the trivial witness.

```agda

  emb-image-contr
    : {w x : A} (a : w ≡ x)
    → is-contr
        (Σ s ∶ w ≡ x
        , ∀ y (q : x ≡ y) z (r : y ≡ z)
          → emb s y q z r ≡ emb a y q z r)
  emb-image-contr a .center = a , λ _ _ _ _ → refl
  emb-image-contr a .paths (s , pw) i =
    path i .fst , λ y q z r j → path i .snd j y q z r
    where
      path = is-contr→is-prop (eqv-fibers emb-equiv (emb a))
        (a , refl)
        (s , funext λ y → funext λ q → funext λ z → funext λ r → pw y q z r)

  emb-inj : {w x : A} {a b : w ≡ x}
    → (∀ y (q : x ≡ y) z (r : y ≡ z)
        → emb a y q z r ≡ emb b y q z r)
    → a ≡ b
  emb-inj {a = a} pw =
    ap fst (emb-image-contr a .paths (_ , λ y q z r → sym (pw y q z r)))

```

```agda

  idem : {x : A} → refl {x = x} ∙ refl ≡ refl
  idem = pcom.lr refl refl ∙ pcom.idemr refl

```

### Noy and yon reduce to binary composition

`noy a z r ≡ a ∙ r` and `yon a y q ≡ a ∙ q`. The binary
specializations of `emb` agree with ordinary path composition.

```agda

  noy-comp : {w x z : A} (a : w ≡ x) (r : x ≡ z)
    → noy a z r ≡ a ∙ r
  noy-comp a r = pcom.lsplit a refl r ∙ ap (_∙ r) (pcom.idemr a)

  yon-comp : {w x y : A} (a : w ≡ x) (q : x ≡ y)
    → yon a y q ≡ a ∙ q
  yon-comp a q = sym (pcom.lr a q)

```

### Functoriality

`noy` and `yon` are functorial: composition distributes through
them. Both reduce to path associativity via `noy-comp`/`yon-comp`.

```agda

  noy-composite : {w x y z : A} (a : w ≡ x) (b : x ≡ y)
    (r : y ≡ z) → noy (a ∙ b) z r ≡ noy a z (noy b z r)
  noy-composite a b r =
    noy-comp (a ∙ b) r
    ∙ sym (Path.assoc a b r)
    ∙ ap (a ∙_) (sym (noy-comp b r))
    ∙ sym (noy-comp a (noy b _ r))

  yon-composite : {w x y z : A} (a : w ≡ x) (b : x ≡ y)
    (q : y ≡ z) → yon (a ∙ b) z q ≡ yon a z (yon b z q)
  yon-composite a b q =
    yon-comp (a ∙ b) q
    ∙ sym (Path.assoc a b q)
    ∙ ap (a ∙_) (sym (yon-comp b q))
    ∙ sym (yon-comp a (yon b _ q))

```

### Interchange

`emb a y q z r ≡ noy (yon a y q) z r`: the ternary `emb`
decomposes as yon-then-noy. Follows from `pcom.lsplit` and
`noy-comp`.

```agda

  interchange : {w x y z : A} (a : w ≡ x) (q : x ≡ y) (r : y ≡ z)
    → emb a y q z r ≡ noy (yon a y q) z r
  interchange a q r =
    pcom.lsplit a q r ∙ sym (noy-comp (yon a _ q) r)

```

### Induction principles

`repr-ind` eliminates over the representable fiber: to prove
`P w F` for any `(w, F) : is-representable x`, it suffices to
prove `P x (_∙_)` — the identity paired with binary composition.
`recover` and the groupoid laws are all instances.

```agda

  repr-ind
    : ∀ {v} {x : A}
    → (P : (w : A) → (∀ y → x ≡ y → ∀ z → y ≡ z → w ≡ z) → Type v)
    → P x (λ y q z r → q ∙ r)
    → ∀ w F → P w F
  repr-ind P base w F =
    contr-ind representable-contr (λ (w , F) → P w F) base (w , F)

```

`emb-ind` eliminates over the composition fiber: given a
composable pair `(a, q)`, any `(s, pw)` where `pw` witnesses
`emb s ≡ emb (a ∙ q)` pointwise satisfies `P` whenever the
canonical composite does. `∙-η` extracts the uniqueness path
`a ∙ q ≡ s`.

```agda

  emb-ind
    : ∀ {v} {w x y : A} (a : w ≡ x) (q : x ≡ y)
    → (P : (s : w ≡ y)
         → (∀ y' (q' : y ≡ y') z (r : y' ≡ z)
             → emb s y' q' z r ≡ emb (a ∙ q) y' q' z r)
         → Type v)
    → P (a ∙ q) (λ _ _ _ _ → refl)
    → ∀ s pw → P s pw
  emb-ind a q P base s pw =
    contr-ind (emb-image-contr (a ∙ q)) (λ (s , pw) → P s pw) base (s , pw)

  ∙-η : ∀ {w x y : A} (a : w ≡ x) (q : x ≡ y) (s : w ≡ y)
    → (∀ y' (q' : y ≡ y') z (r : y' ≡ z)
        → emb s y' q' z r ≡ emb (a ∙ q) y' q' z r)
    → a ∙ q ≡ s
  ∙-η a q = emb-ind a q (λ s _ → a ∙ q ≡ s) refl

```

### Triple composition fiber

The common target for three composed paths: fully expand via
`yon` into three nested applications.

```agda

  E₃ : {w x y z : A} (a : w ≡ x) (q : x ≡ y) (r : y ≡ z)
    → ∀ y' → z ≡ y' → ∀ z' → y' ≡ z' → w ≡ z'
  E₃ a q r y' q' z' r' =
    yon a _ (yon q _ (yon r _ q')) ∙ r'

```

Both bracketings of a triple composite decompose to `E₃`.
The center is `(a ∙ q) ∙ r` with the decomposition chain.

```agda

  private
    funext⁴
      : {v : Level} {z₀ : A}
        {B : ∀ (y' : A) → z₀ ≡ y'
          → ∀ (z' : A) → y' ≡ z' → Type v}
        {f g : ∀ y' q' z' r' → B y' q' z' r'}
      → (∀ y' q' z' r'
          → f y' q' z' r' ≡ g y' q' z' r')
      → f ≡ g
    funext⁴ h = funext λ y' → funext λ q' →
      funext λ z' → funext λ r' → h y' q' z' r'

  E₃-contr
    : {w x y z : A} (a : w ≡ x) (q : x ≡ y)
      (r : y ≡ z)
    → is-contr
        (Σ s ∶ w ≡ z
        , ∀ y' (q' : z ≡ y') z' (r' : y' ≡ z')
          → emb s y' q' z' r'
          ≡ E₃ a q r y' q' z' r')
  E₃-contr a q r .center .fst = (a ∙ q) ∙ r
  E₃-contr a q r .center .snd y' q' z' r' =
    pcom.lsplit ((a ∙ q) ∙ r) q' r'
    ∙ ap (_∙ r') (yon-composite (a ∙ q) r q'
                   ∙ yon-composite a q (yon r _ q'))
  E₃-contr {w} a q r .paths =
    is-contr→is-prop
      (subst (λ (T : ∀ y' → _ ≡ y' → ∀ z' → y' ≡ z'
                  → w ≡ z')
              → is-contr
                  (Σ (λ (s : w ≡ _)
                    → ∀ y' q' z' r'
                      → emb s y' q' z' r'
                      ≡ T y' q' z' r')))
        (funext⁴ λ y' q' z' r' →
          pcom.lsplit ((a ∙ q) ∙ r) q' r'
          ∙ ap (_∙ r') (yon-composite (a ∙ q) r q'
                         ∙ yon-composite a q
                             (yon r _ q')))
        (emb-image-contr ((a ∙ q) ∙ r))) _

```

### Associativity

`assoc-σ` is the path between the two points in the
contractible E₃ fiber. `assoc` is its first-component
projection (flipped).

```agda

  assoc-σ
    : {w x y z : A} (p : w ≡ x) (q : x ≡ y)
      (r : y ≡ z)
    → E₃-contr p q r .center
    ≡ ( p ∙ (q ∙ r)
      , λ y' q' z' r' →
          pcom.lsplit (p ∙ (q ∙ r)) q' r'
          ∙ ap (_∙ r')
              (yon-composite p (q ∙ r) q'
                ∙ ap (yon p _)
                    (yon-composite q r q')))
  assoc-σ p q r =
    is-contr→is-prop (E₃-contr p q r) _ _

  assoc : {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
    → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
  assoc p q r = sym (ap fst (assoc-σ p q r))

```

### Identity uniqueness

Any loop `e : x ≡ x` satisfying yon-idempotency
`yon e x e ≡ e` equals `refl`. The proof left-cancels `e`
from `e ∙ e ≡ e ∙ refl`, derived by chaining `yon-comp`,
the hypothesis, and `pcom.idemr`.

```agda

  private
    lcancel : {x y : A} (e : x ≡ x) {q₁ q₂ : x ≡ y}
      → e ∙ q₁ ≡ e ∙ q₂ → q₁ ≡ q₂
    lcancel e {q₁} {q₂} p =
      sym (unitl q₁)
      ∙ ap (_∙ q₁) (sym (invl e))
      ∙ sym (assoc (sym e) e q₁)
      ∙ ap (sym e ∙_) p
      ∙ assoc (sym e) e q₂
      ∙ ap (_∙ q₂) (invl e)
      ∙ unitl q₂

  unit-is-prop : {x : A} (e : x ≡ x)
    → yon e x e ≡ e → e ≡ refl
  unit-is-prop e idpt =
    lcancel e
      (sym (yon-comp e e) ∙ idpt
       ∙ sym (pcom.idemr e) ∙ yon-comp e refl)

```

### Inverse distribution

`sym` distributes over path composition by reversing order.
The `inv-sides` square connects `p`, `q`, `sym q`, `sym p`,
and `sym-distr` chains through it via `hfil`.

```agda

  private
    inv-sides : {x y z : A} (p : x ≡ y) (q : x ≡ z)
      → Square p q (sym q) (sym p)
    inv-sides {x = x} p q i j =
      hcom (∂ i ∨ ∂ j) λ where
        k (i = i0) → p (k ∧ j)
        k (i = i1) → q (~ j ∧ k)
        k (j = i0) → q (i ∧ k)
        k (j = i1) → p (~ i ∧ k)
        k (k = i0) → x

  sym-distr : {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → sym (p ∙ q) ≡ sym q ∙ sym p
  sym-distr p q i j = fill j i i1
    where
      fill : I → I → I → _
      fill a b k = hfil (∂ a) k λ where
        l (a = i0) → q (l ∨ b)
        l (a = i1) → p (~ l ∧ b)
        l (l = i0) → inv-sides q (sym p) a b

```

### Opposite via sym

`sym` is the opposite functor for the path groupoid. It
preserves identity (definitional), distributes over composition
(`sym-distr`), and is a definitional involution (`sym ∘ sym = id`).

```agda

  op-idn : {x : A} → sym (refl {x = x}) ≡ refl
  op-idn = refl

  op-comp : {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → sym (p ∙ q) ≡ sym q ∙ sym p
  op-comp = sym-distr

  op-invol : {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
  op-invol p = refl

```

Pentagon and triangle coherences live in `Core.Coherence`.
