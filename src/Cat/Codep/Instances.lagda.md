Lane Biocini
July 2026

The two reference instances of `codep-category`, both abstracting a
concrete category from the `Cat.*` layer, and the specialization checks
that the generic `assoc` and `pentagon` instantiate at each.

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

open import Cat.Type
open import Cat.Monoidal
open import Cat.Codep
```

## Instance 1 — Cat.Type

Passenger `(v , (w , a))`: acted-object `v`, then the inert binder
`(w , a)`; `sub` acts on the single `b : hom y v` slot.

```agda
module TypeInstance {o h} (C : category o h) where
  private module C = Virtual C

  -- passenger (v , (w , a)); binder (w , a) is v-independent; idn-b at
  -- object y is (y , C.idn). `act`/`act-comp` are derived — `act φ g α`
  -- computes to `C.noy g v α` on the nose.
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
```

## Instance 2 — Cat.Monoidal

`ob = ⊤`; the tensor factor lives in the binder, the anchor is `I`.

```agda
module MonoidalInstance {o hh} {C : category o hh} (M : monoidal C) where
  private module C = Virtual C
  open monoidal M

  -- ob = ⊤, so the acted-object v is a dummy; the binder carries the
  -- tensor factor `l`, and idn is the unit object `I`. `act l g r`
  -- computes to `noy g r = tensor-emb g I r` on the nose.
  -- With canonical binder, `binder ⊤ = Σ w ∶ ⊤ , C.ob` is ⊤-wrapped;
  -- the projections dig one level deeper. ⊤-eta carries the round-trip.
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
```
