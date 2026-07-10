Lane Biocini
July 2026

The two reference instances of `codep-category`, both abstracting a
concrete category from the `Cat.*` layer, together with their coupling
and unit fills and the specialization checks that the generic `assoc`,
`pentagon`, and unit fragment instantiate at each.

`Type-codep` reads off `Cat.Type.category` — the anchor is the identity
morphism `C.idn`. `Monoidal-codep` reads off `Cat.Monoidal.monoidal`
over the one-object `⊤` — the anchor is the tensor unit object `I`, and
with the canonical binder the passenger is `⊤`-wrapped one level deeper.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep.Instances where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Equiv.Base using (is-equiv)

open import Cat.Type
open import Cat.Monoidal
open import Cat.Codep
```

## Instance 1 — Cat.Type

Passenger `(v , (w , a))`: acted-object `v`, then the inert binder
`(w , a)`, which is `v`-independent; `idn-b` at object `y` is
`(y , C.idn)`. Because `act`/`act-comp` are derived, `act φ g α`
computes to `C.noy g v α` on the nose, and `yon`/`noy` reduce to
`C.yon`/`C.noy` — so the coupling and unit fields fill directly from
`C.interchange`, `C.yon-eval`, and `C.unit`. `sub` acts on the single
`b : hom y v` slot.

```agda
module TypeInstance {o h} (C : category o h) where
  private module C = Virtual C

  LooseT : C.ob → C.ob → Type (o ⊔ h)
  LooseT x y =
    (γ : Σ φ ∶ (Σ v ∶ C.ob , (Σ w ∶ C.ob , C.hom w x)) , C.hom y (φ .fst))
    → C.hom (γ .fst .snd .fst) (γ .fst .fst)

  uncurryT : ∀ {x y}
    → (∀ w → C.hom w x → ∀ v → C.hom y v → C.hom w v)
    → LooseT x y
  uncurryT G γ =
    G (γ .fst .snd .fst) (γ .fst .snd .snd) (γ .fst .fst) (γ .snd)

  curryT : ∀ {x y}
    → LooseT x y
    → (∀ w → C.hom w x → ∀ v → C.hom y v → C.hom w v)
  curryT F w a v b = F ((v , (w , a)) , b)

  Type-codep : codep-category {o} {h} C.ob
  Type-codep .codep-category.hom = C.hom
  Type-codep .codep-category.idn x = C.idn
  Type-codep .codep-category.emb f = uncurryT (C.emb f)
  Type-codep .codep-category.compose-contr f g .center =
    (f C.⨾ g) , ap uncurryT (C.compose-contr f g .center .snd)
  Type-codep .codep-category.compose-contr f g .paths (s , q) i =
    let p = C.compose-contr f g .paths (s , ap curryT q) i
    in p .fst , ap uncurryT (p .snd)

  Type-coupling : codep-coupling Type-codep
  Type-coupling .codep-coupling.interchange f g {w} a {v} b =
    C.interchange f g w a v b
  Type-coupling .codep-coupling.yon-eval f = C.yon-eval f

  Type-unit : codep-unit Type-codep Type-coupling
  Type-unit .codep-unit.unit-l-equiv = C.unit-eqvl
  Type-unit .codep-unit.unit-r-equiv = C.unit-eqvr

  -- The generic assoc reduces to the concrete assoc.
  _ : ∀ {x y z w} (f : C.hom x y) (g : C.hom y z) (h : C.hom z w)
    → (f C.⨾ g) C.⨾ h ≡ f C.⨾ (g C.⨾ h)
  _ = Derived.assoc Type-codep

  -- The pentagon machinery specializes to the concrete category.
  module _ {x y z w v : C.ob}
    (f : C.hom x y) (g : C.hom y z) (h : C.hom z w) (k : C.hom w v)
    where
    open Pentagon.PentagonFibers Type-codep f g h k
    _ = face₁₂
    _ = face₂₃
    _ = face₁₄
    _ = face₄₅
    _ = Pentagon35.face₃₅ Type-codep f g h k
    _ = hom-identity
    _ = Pentagon5.pentagon Type-codep f g h k

  private module UT = UnitDerived Type-codep Type-coupling Type-unit
```

`absorb-l` lands on `C.absorb-l` definitionally. As at Monoidal, `unitl`
and `unit-is-prop` specialize in statement but not proof-term: the
generic `unitl` routes through its own `emb-image-contr` (a `subst` on
`compose-contr (idn) f`), whereas `C.unitl` uses `composable-contr
idn f` directly — two fibers giving the same edge, so not `refl`-equal.

```agda
  _ : ∀ {x v} (b : C.hom x v) → UT.absorb-l b ≡ C.absorb-l b
  _ = λ b → refl

  _ : ∀ {x y} (f : C.hom x y) → C.idn C.⨾ f ≡ f
  _ = UT.unitl

  _ : ∀ {x} (e : C.hom x x)
    → (∀ {w} → is-equiv (λ (a : C.hom w x) → C.emb e w a x e))
    → C.yon e x e ≡ e → e ≡ C.idn
  _ = UT.unit-is-prop
```

## Instance 2 — Cat.Monoidal

`ob = ⊤`; the acted-object `v` is a dummy, the binder carries the
tensor factor `l`, and `idn` is the unit object `I` — so `act l g r`
computes to `noy g r = tensor-emb g I r`. With the canonical binder,
`binder ⊤ = Σ w ∶ ⊤ , C.ob` is `⊤`-wrapped, the projections dig one
level deeper, and `⊤`-eta carries the round-trip. The coupling and unit
fields fill from `tensor-interchange`, `tensor-yon-eval`, and
`tensor-unit`.

```agda
module MonoidalInstance {o hh} {C : category o hh} (M : monoidal C) where
  private module C = Virtual C
  open monoidal M

  LooseM : ⊤ → ⊤ → Type o
  LooseM x y = (γ : Σ φ ∶ (⊤ × (Σ v ∶ ⊤ , C.ob)) , C.ob) → C.ob

  uncurryM : (C.ob → C.ob → C.ob) → LooseM tt tt
  uncurryM G γ = G (γ .fst .snd .snd) (γ .snd)

  curryM : LooseM tt tt → (C.ob → C.ob → C.ob)
  curryM F l r = F ((tt , (tt , l)) , r)

  Monoidal-codep : codep-category {0ℓ} {o} ⊤
  Monoidal-codep .codep-category.hom _ _ = C.ob
  Monoidal-codep .codep-category.idn _ = I
  Monoidal-codep .codep-category.emb x = uncurryM (tensor-emb x)
  Monoidal-codep .codep-category.compose-contr x y .center =
    (x ⊗ y) , ap uncurryM (tensor-emb-composite x y)
  Monoidal-codep .codep-category.compose-contr x y .paths (s , q) i =
    let p = tensor-compose-contr x y .paths (s , ap curryM q) i
    in p .fst , ap uncurryM (p .snd)

  Monoidal-coupling : codep-coupling Monoidal-codep
  Monoidal-coupling .codep-coupling.interchange f g a b =
    tensor-interchange f g a b
  Monoidal-coupling .codep-coupling.yon-eval f = tensor-yon-eval f

  Monoidal-unit : codep-unit Monoidal-codep Monoidal-coupling
  Monoidal-unit .codep-unit.unit-l-equiv = tensor-unit-eqvl
  Monoidal-unit .codep-unit.unit-r-equiv = tensor-unit-eqvr

  -- The generic assoc reduces to the concrete ⊗-assoc.
  _ : (x y z : C.ob) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
  _ = Derived.assoc Monoidal-codep {tt} {tt} {tt} {tt}

  -- The pentagon machinery specializes to the concrete monoidal category.
  module _ (x y z w : C.ob) where
    open Pentagon.PentagonFibers Monoidal-codep {tt} {tt} {tt} {tt} {tt} x y z w
    _ = face₁₂
    _ = face₂₃
    _ = face₁₄
    _ = face₄₅
    _ = Pentagon35.face₃₅ Monoidal-codep {tt} {tt} {tt} {tt} {tt} x y z w
    _ = hom-identity
    _ = Pentagon5.pentagon Monoidal-codep {tt} {tt} {tt} {tt} {tt} x y z w

  private module UM = UnitDerived Monoidal-codep Monoidal-coupling Monoidal-unit
```

`absorb-l` lands on `Cat.Monoidal`'s `absorb-l` definitionally (both are
`equiv→lc tensor-unit-eqvl` over the same idempotency). `unitl` and
`unit-is-prop` specialize in statement (`I ⊗ x ≡ x`, `e ≡ I`) but not
proof-term: the generic `unitl` builds its own `emb-image-contr` (a
`subst` on `compose-contr (idn) f`), whereas `⊗-unitl` uses
`tensor-composable-contr` directly — two fibers giving the same edge,
so not `refl`-equal.

```agda
  _ : (b : C.ob) → UM.absorb-l b ≡ absorb-l b
  _ = λ b → refl

  _ : (x : C.ob) → I ⊗ x ≡ x
  _ = UM.unitl

  _ : (e : C.ob)
      (re : ∀ {_ : ⊤} → is-equiv (λ (l : C.ob) → tensor-emb e l e))
      (idpt : yon e e ≡ e)
    → e ≡ I
  _ = UM.unit-is-prop
```
