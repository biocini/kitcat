Spike: the extracted twist does not cancel on the term side.

Over `Bb.OneTwist.Base`'s one-twist carrier, add the `⁺`
invertibility tier and ask for the term-side cancellation,
`act-π (twist⁻ x) ≡ snd`. The tier's centre is a left unit for the
negative cut — the unit-law pair of
`Cat.Logic.Gist.FramedInterchange` survives
with the centre in the posited twist's role — and by contractibility
the cancellation is exactly the agreement of that centre with the
posited twist. The opposite carrier posits the extracted `twist⁺` and
takes the `⁺` tier as its `⁻` tier, so the twice-opposed carrier posits
the centre: the same agreement is involutivity of the opposite at the
twist field.

A finite model refutes the agreement. The Klein four-group carries a
reflection twisted by a three-cycle `σ` of its non-unit elements; every
field of the carrier and both tiers are inhabited, the extraction gives
`twist⁺ = ψ twist⁻`, and the `⁺` centre is `ψ (ψ twist⁻)` — one step
further around the cycle, a different element. So the term-side
cancellation and the involution both fail. The same model separates the
two readback-record ingredients of `cancel⁺-from-cancellable`:
right-cancellability of `_⨾⁻ twist⁺` holds, while
`twist⁻ x ⨾⁻ twist⁺ x ≡ twist⁺ x` fails — the reduction does not
transpose to the readback-free carrier.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.OneTwist.Cancel where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Bool using (Bool; true; false; module Bool)
open import Core.Data.Empty

open Bool using (xor; module xor)
open import Core.Kan using (_∙_)
open import Core.Path.Base
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (prop-inhabited→is-contr)
open import Core.HLevel.Base using (Π-is-hlevel; ×-is-hlevel)
open import Core.Function.Embedding using (injective→is-embedding)

open import Bb.OneTwist.Base
```

## The other tier, and what its centre already does

```agda
module system⁻ {o h} (G : graph⁻ o h)
  (invertible⁺ : ∀ x → is-contr (fiber (graph⁻.act-π G {x} {x}) snd))
  where
  open extracted G public

  centre⁺ : (x : ob) → hom x x
  centre⁺ x = invertible⁺ x .center .fst

  centre-cancel⁺ : (x : ob) → act-π (centre⁺ x) ≡ snd
  centre-cancel⁺ x = invertible⁺ x .center .snd

  absorb⁺ : ∀ {x} (t : term x) → act (centre⁺ x) t ≡ t
  absorb⁺ {x} t i = t .fst , centre-cancel⁺ x i t

  _⨾⁻_ : ∀ {x y z} → hom x y → hom y z → hom x z
  f ⨾⁻ g = cut⁻ f g .fst

  reflect-⨾⁻ : ∀ {x y z} (f : hom x y) (g : hom y z)
             → reflect (f ⨾⁻ g) ≡ composite⁻ f g
  reflect-⨾⁻ f g = cut⁻ f g .snd

  composite-centre⁺ : ∀ {x y} (g : hom x y) → composite⁻ (centre⁺ x) g ≡ reflect g
  composite-centre⁺ g i γ = reflect g (absorb⁺ (γ .fst) i , γ .snd)

  unitl⁻ : ∀ {x y} (g : hom x y) → centre⁺ x ⨾⁻ g ≡ g
  unitl⁻ g = reflect-lc (reflect-⨾⁻ (centre⁺ x) g ∙ composite-centre⁺ g)
    where x = _
```

The cancellation says the posited twist inhabits the `⁺` fiber, and the
fiber is contractible, so it is equivalent to the centre being the
twist. The twice-opposed carrier posits the centre, so the same
equivalence reads: the opposite is involutive at the twist field.

```agda
  cancel⁺ : Type (o ⊔ h)
  cancel⁺ = ∀ x → act-π {x} {x} (twist⁻ x) ≡ snd

  agree : Type (o ⊔ h)
  agree = ∀ x → centre⁺ x ≡ twist⁻ x

  cancel⁺→agree : cancel⁺ → agree
  cancel⁺→agree c x = ap fst (invertible⁺ x .paths (twist⁻ x , c x))

  agree→cancel⁺ : agree → cancel⁺
  agree→cancel⁺ p x = subst (λ e → act-π {x} {x} e ≡ snd) (p x) (centre-cancel⁺ x)
```

## The carrier of the countermodel

The Klein four-group, as pairs of booleans under componentwise `xor`,
and a three-cycle of its non-unit elements.

```agda
K : Type
K = Bool × Bool

_⊕_ : K → K → K
w ⊕ v = xor (w .fst) (v .fst) , xor (w .snd) (v .snd)

0₄ v⁻ v⁺ c⁺ : K
0₄ = false , false
v⁻ = false , true
v⁺ = true  , true
c⁺ = true  , false

σ ψ : K → K
σ (false , false) = false , false
σ (false , true)  = true  , false
σ (true  , false) = true  , true
σ (true  , true)  = false , true

ψ (false , false) = false , false
ψ (true  , false) = false , true
ψ (true  , true)  = true  , false
ψ (false , true)  = true  , true

σψ : ∀ w → σ (ψ w) ≡ w
σψ (false , false) = refl
σψ (false , true)  = refl
σψ (true  , false) = refl
σψ (true  , true)  = refl

ψσ : ∀ w → ψ (σ w) ≡ w
ψσ (false , false) = refl
ψσ (false , true)  = refl
ψσ (true  , false) = refl
ψσ (true  , true)  = refl

σ-inj : {x y : K} → σ x ≡ σ y → x ≡ y
σ-inj {x} {y} p = sym (ψσ x) ∙ ap ψ p ∙ ψσ y

⊕-assoc : ∀ a b c → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
⊕-assoc a b c i =
    xor.assoc (a .fst) (b .fst) (c .fst) (~ i)
  , xor.assoc (a .snd) (b .snd) (c .snd) (~ i)

⊕-invol : ∀ a x → a ⊕ (a ⊕ x) ≡ x
⊕-invol a x i = xor.invol (a .fst) (x .fst) i , xor.invol (a .snd) (x .snd) i

⊕-unitr : ∀ a → a ⊕ 0₄ ≡ a
⊕-unitr a i = xor.unitr (a .fst) i , xor.unitr (a .snd) i

⊕-comm : ∀ a b → a ⊕ b ≡ b ⊕ a
⊕-comm a b i = xor.comm (a .fst) (b .fst) i , xor.comm (a .snd) (b .snd) i

⊕-cancel-l : ∀ a {x y} → a ⊕ x ≡ a ⊕ y → x ≡ y
⊕-cancel-l a {x} {y} p = sym (⊕-invol a x) ∙ ap (a ⊕_) p ∙ ⊕-invol a y

⊕-cancel-r : ∀ a {x y} → x ⊕ a ≡ y ⊕ a → x ≡ y
⊕-cancel-r a {x} {y} p = ⊕-cancel-l a (⊕-comm a x ∙ p ∙ ⊕-comm y a)

K-set : is-set K
K-set = ×-is-hlevel 2 Bool.set Bool.set
```

## The twisted reflection satisfies every field

The reflection reads the string through `σ`. Injectivity of each action
map comes from cancelling the flanks and inverting `σ`; each tier's
centre is the `ψ`-image its side's equation names, and both cuts are
represented by `ψ` of the gathered middle.

```agda
cπ : K → Sigma ⊤ (λ _ → K) → K
cπ m k = v⁻ ⊕ (σ m ⊕ k .snd)

aπ : K → Sigma ⊤ (λ _ → K) → K
aπ m t = t .snd ⊕ (σ m ⊕ v⁺)

rf : K → Sigma ⊤ (λ _ → K) × Sigma ⊤ (λ _ → K) → K
rf m γ = γ .fst .snd ⊕ (σ m ⊕ γ .snd .snd)

cπ-inj : {m n : K} → cπ m ≡ cπ n → m ≡ n
cπ-inj {m} {n} p =
  σ-inj ( sym (⊕-unitr (σ m))
        ∙ ⊕-cancel-l v⁻ (happly p (tt , 0₄))
        ∙ ⊕-unitr (σ n) )

aπ-inj : {m n : K} → aπ m ≡ aπ n → m ≡ n
aπ-inj {m} {n} p = σ-inj (⊕-cancel-r v⁺ (⊕-cancel-l 0₄ (happly p (tt , 0₄))))

rf-inj : {m n : K} → rf m ≡ rf n → m ≡ n
rf-inj {m} {n} p =
  σ-inj ( sym (⊕-unitr (σ m))
        ∙ ⊕-cancel-l 0₄ (happly p ((tt , 0₄) , (tt , 0₄)))
        ∙ ⊕-unitr (σ n) )

tier⁻ : is-contr (fiber cπ snd)
tier⁻ = prop-inhabited→is-contr
  (injective→is-embedding (Π-is-hlevel 2 λ _ → K-set) cπ cπ-inj snd)
  (v⁺ , funext λ k → ⊕-invol v⁻ (k .snd))

tier⁺ : is-contr (fiber aπ snd)
tier⁺ = prop-inhabited→is-contr
  (injective→is-embedding (Π-is-hlevel 2 λ _ → K-set) aπ aπ-inj snd)
  (c⁺ , funext λ t → ⊕-unitr (t .snd))

model : graph⁻ 0ℓ 0ℓ
model .graph⁻.ob      = ⊤
model .graph⁻.hom _ _ = K
model .graph⁻.reflect m γ = γ .fst .snd ⊕ (σ m ⊕ γ .snd .snd)
model .graph⁻.twist⁻ _    = v⁻
model .graph⁻.unital⁻ x   = tier⁻
model .graph⁻.stable α    =
  injective→is-embedding (Π-is-hlevel 2 λ _ → K-set) rf rf-inj α
model .graph⁻.cut⁺ f g = ψ (σ f ⊕ (v⁻ ⊕ σ g)) , funext λ γ →
  ap (γ .fst .snd ⊕_)
    ( ap (_⊕ γ .snd .snd) (σψ (σ f ⊕ (v⁻ ⊕ σ g)))
    ∙ ⊕-assoc (σ f) (v⁻ ⊕ σ g) (γ .snd .snd)
    ∙ ap (σ f ⊕_) (⊕-assoc v⁻ (σ g) (γ .snd .snd)) )
model .graph⁻.cut⁻ f g = ψ ((σ f ⊕ v⁺) ⊕ σ g) , funext λ γ →
  ap (γ .fst .snd ⊕_)
    ( ap (_⊕ γ .snd .snd) (σψ ((σ f ⊕ v⁺) ⊕ σ g))
    ∙ ⊕-assoc (σ f ⊕ v⁺) (σ g) (γ .snd .snd) )
  ∙ sym (⊕-assoc (γ .fst .snd) (σ f ⊕ v⁺) (σ g ⊕ γ .snd .snd))

open system⁻ model (λ _ → tier⁺)
```

## The kills

The extraction computes: `twist⁺` is `ψ v⁻ = v⁺` and the `⁺` centre is
`ψ v⁺ = c⁺`, one further step around the cycle. The two differ in their
first component, so the agreement — and with it the term-side
cancellation and the involution at the twist field — is refutable.

```agda
is-true : Bool → Type
is-true true  = ⊤
is-true false = ⊥

no-agree : agree → ⊥
no-agree a = subst (λ w → is-true (w .fst)) (a tt) tt

no-cancel⁺ : cancel⁺ → ⊥
no-cancel⁺ c = no-agree (cancel⁺→agree c)
```

Right-cancellability of `_⨾⁻ twist⁺` holds here — the hand is a
composite of injections — so the readback-record reduction's hypothesis
is satisfiable while its conclusion fails. What dies instead is the
frame law the readback record proves as `unitl⁻ (twist⁺ x)`: cutting
the posited twist against the extracted one lands on the unit of the
group, not on the extracted twist.

```agda
⨾⁻twist⁺-cancellable : {a b : K} → a ⨾⁻ twist⁺ tt ≡ b ⨾⁻ twist⁺ tt → a ≡ b
⨾⁻twist⁺-cancellable {a} {b} p =
  σ-inj (⊕-cancel-r v⁺ (⊕-cancel-r v⁻
    (sym (σψ ((σ a ⊕ v⁺) ⊕ v⁻)) ∙ ap σ p ∙ σψ ((σ b ⊕ v⁺) ⊕ v⁻))))

no-frame⁻ : twist⁻ tt ⨾⁻ twist⁺ tt ≡ twist⁺ tt → ⊥
no-frame⁻ p = subst (λ w → is-true (w .fst)) (sym p) tt
```
