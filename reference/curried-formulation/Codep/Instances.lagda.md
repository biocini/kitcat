Lane Biocini
July 2026

Instances of the trilayer. `walking-arrow` is the simplest possible one
— the interval category **2**, a direct multi-object triple — kept as
the API's worked example and the regression guard for the termination
class the split defeats. `type-instance` and `monoidal-instance` are
the two reference instances, each abstracting a concrete category from
the `Cat.Depreciated.*` layer as a structure + axioms + bundle triple, together
with their five-axiom fills and the specialization checks that the
generic `assoc`, `pentagon`, and unit fragment instantiate at each.

With the derived laws consolidated into `hcategory-axioms`, the unit
specialization checks read the bundle's record projections directly —
`absorb-l`, `unitl`, `unit-is-prop` off `hcategory C` — rather
than through a separate `unit-laws` module.

`type-instance` reads off `Cat.Depreciated.Type.category` — the anchor is the
identity morphism `C.idn`, and the merged axioms' coupling/unit fills
are name-identical to `Cat.Depreciated.Type`'s own (`unit-eqvl = C.unit-eqvl`).
`monoidal-instance` reads off `Cat.Depreciated.Monoidal.monoidal` over the
one-object `⊤` — the anchor is the tensor unit object `I`. Its
curry/uncurry glue carries some `⊤`-noise, an acceptable
instance-internal cost.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Depreciated.Codep.Instances where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Data.Empty using (⊥; ex-falso)
open import Core.Transport.Properties
  using (prop-inhabited→is-contr; is-prop→is-set)
open import Core.HLevel.Base using (Π-is-set)
open import Core.Function.Embedding using (injective→is-embedding)
open import Core.Equiv.Base using (is-equiv; eqv-fibers)
open import Core.Equiv.Properties using (prop→endo-is-equiv)

open import Cat.Depreciated.Type
open import Cat.Depreciated.Monoidal
open import Cat.Depreciated.Codep
```

The walking arrow **2**: a direct, naive `hcategory-structure` +
`hcategory-axioms` + `hcategory` triple. It is thin (every hom a
proposition), so `composite` is a Π into propositions and the five
axioms are prop-level: `compose-contr` from the contractible image
fibre, `interchange`/`post-eval` immediate, the two unit equivalences
from `Core.Equiv.Properties.prop→endo-is-equiv` (a thin endomap of a
proposition is an equivalence). It is a non-groupoid (`hom o1 o0 = ⊥`);
and its `emb` is an equivalence — the last cell of the
`emb`-equivalence × groupoid-ness independence square. A multi-object
instance whose `idn` cases on the object was exactly the shape that
tripped the termination checker before the split; that it now goes
through directly is what this instance certifies.

```agda
module walking-arrow where
  data Ob : Type where
    o0 o1 : Ob

  homW : Ob → Ob → Type
  homW o0 o0 = ⊤
  homW o0 o1 = ⊤
  homW o1 o0 = ⊥
  homW o1 o1 = ⊤

  comp3 : ∀ {w x y v} → homW w x → homW x y → homW y v → homW w v
  comp3 {w = o0} {v = o0}                   _ _ _ = tt
  comp3 {w = o0} {v = o1}                   _ _ _ = tt
  comp3 {w = o1} {v = o1}                   _ _ _ = tt
  comp3 {w = o1} {x = o0} {v = o0}          a _ _ = ex-falso a
  comp3 {w = o1} {x = o1} {y = o0} {v = o0} _ f _ = ex-falso f
  comp3 {w = o1} {x = o1} {y = o1} {v = o0} _ _ b = ex-falso b

  transW : ∀ {x y z} → homW x y → homW y z → homW x z
  transW {x = o0} {z = o0}          _ _ = tt
  transW {x = o0} {z = o1}          _ _ = tt
  transW {x = o1} {z = o1}          _ _ = tt
  transW {x = o1} {y = o0} {z = o0} a _ = ex-falso a
  transW {x = o1} {y = o1} {z = o0} _ b = ex-falso b

  hom-prop : (x y : Ob) → is-prop (homW x y)
  hom-prop o0 o0 = λ _ _ → refl
  hom-prop o0 o1 = λ _ _ → refl
  hom-prop o1 o0 = λ e _ → ex-falso e
  hom-prop o1 o1 = λ _ _ → refl

  walk-structure : hcategory-structure 0ℓ Ob
  walk-structure .hcategory-structure.hom = homW
  walk-structure .hcategory-structure.idn o0 = tt
  walk-structure .hcategory-structure.idn o1 = tt
  walk-structure .hcategory-structure.emb f ((_ , a) , (_ , b)) = comp3 a f b

  open hcategory-structure walk-structure

  -- `composite` is a Π into propositions, hence a proposition.
  comp-prop : ∀ {x y} → is-prop (composite x y)
  comp-prop F G = funext (λ γ → hom-prop _ _ (F γ) (G γ))

  walk-axioms : hcategory-axioms walk-structure
  walk-axioms .hcategory-axioms.compose-contr {x} {_} {z} f g =
    prop-inhabited→is-contr fib-prop pt
    where
      emb-inj : ∀ {h h'} → emb h ≡ emb h' → h ≡ h'
      emb-inj {h} {h'} _ = hom-prop x z h h'

      fib-prop : is-prop (fiber emb _)
      fib-prop =
        injective→is-embedding
          (Π-is-set (λ _ → is-prop→is-set (hom-prop _ _))) emb emb-inj _

      pt : fiber emb _
      pt = transW f g , comp-prop _ _
  walk-axioms .hcategory-axioms.interchange f g a b = hom-prop _ _ _ _
  walk-axioms .hcategory-axioms.post-eval f = hom-prop _ _ _ _
  walk-axioms .hcategory-axioms.unit-eqvl {x} {v} =
    prop→endo-is-equiv (hom-prop x v) (pre (idn x) {v})
  walk-axioms .hcategory-axioms.unit-eqvr {x} {w} =
    prop→endo-is-equiv (hom-prop w x) (post (idn x) {w})

  walk-cat : hcategory 0ℓ 0ℓ
  walk-cat .hcategory.ob = Ob
  walk-cat .hcategory.structure = walk-structure
  walk-cat .hcategory.axioms = walk-axioms

  -- Thin `emb` is an equivalence: evaluation at the canonical context
  -- inverts it, `composite` being a Π into propositions.
  emb-is-equiv : ∀ {x y} → is-equiv (emb {x} {y})
  emb-is-equiv {x} {y} .eqv-fibers F =
    prop-inhabited→is-contr fib-prop (F γ⋆ , comp-prop _ _)
    where
      γ⋆ : ctx x y
      γ⋆ = (x , idn x) , (y , idn y)

      emb-inj : ∀ {h h'} → emb h ≡ emb h' → h ≡ h'
      emb-inj {h} {h'} _ = hom-prop x y h h'

      fib-prop : is-prop (fiber emb F)
      fib-prop =
        injective→is-embedding
          (Π-is-set (λ _ → is-prop→is-set (hom-prop _ _))) emb emb-inj F
```

`type-instance`: the reference instance over `Cat.Depreciated.Type.category`. The
five-axiom fills are name-identical to `Cat.Depreciated.Type`'s own operations.

```agda
module type-instance {o h} (C : category o h) where
  private module C = Virtual C

  CompositeT : C.ob → C.ob → Type (o ⊔ h)
  CompositeT x y =
    (γ : (Σ w ∶ C.ob , C.hom w x) × (Σ v ∶ C.ob , C.hom y v))
    → C.hom (γ .fst .fst) (γ .snd .fst)

  uncurryT : ∀ {x y}
    → (∀ w → C.hom w x → ∀ v → C.hom y v → C.hom w v)
    → CompositeT x y
  uncurryT G γ =
    G (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

  curryT : ∀ {x y}
    → CompositeT x y
    → (∀ w → C.hom w x → ∀ v → C.hom y v → C.hom w v)
  curryT F w a v b = F ((w , a) , (v , b))

  Type-structure : hcategory-structure h C.ob
  Type-structure .hcategory-structure.hom = C.hom
  Type-structure .hcategory-structure.idn x = C.idn
  Type-structure .hcategory-structure.emb f = uncurryT (C.emb f)

  Type-axioms : hcategory-axioms Type-structure
  Type-axioms .hcategory-axioms.compose-contr f g .center =
    (f C.⨾ g) , ap uncurryT (C.compose-contr f g .center .snd)
  Type-axioms .hcategory-axioms.compose-contr f g .paths (s , q) i =
    let p = C.compose-contr f g .paths (s , ap curryT q) i
    in p .fst , ap uncurryT (p .snd)
  Type-axioms .hcategory-axioms.interchange f g {w} a {v} b =
    C.interchange f g w a v b
  Type-axioms .hcategory-axioms.post-eval f = C.yon-eval f
  Type-axioms .hcategory-axioms.unit-eqvl = C.unit-eqvl
  Type-axioms .hcategory-axioms.unit-eqvr = C.unit-eqvr

  Type-cat : hcategory o h
  Type-cat .hcategory.ob = C.ob
  Type-cat .hcategory.structure = Type-structure
  Type-cat .hcategory.axioms = Type-axioms

  -- The generic assoc reduces to the concrete assoc.
  _ : ∀ {x y z w} (f : C.hom x y) (g : C.hom y z) (h : C.hom z w)
    → (f C.⨾ g) C.⨾ h ≡ f C.⨾ (g C.⨾ h)
  _ = assoc-tower.assoc Type-cat

  -- The pentagon machinery specializes to the concrete category.
  module _ {x y z w v : C.ob}
    (f : C.hom x y) (g : C.hom y z) (h : C.hom z w) (k : C.hom w v)
    where
    open pentagon-tower.pentagon-fibers Type-cat f g h k
    _ = face₁₂
    _ = face₂₃
    _ = face₁₄
    _ = face₄₅
    _ = face₃₅
    _ = hom-identity
    _ = pentagon

  -- The consolidated record's unit fragment reduces to the concrete one.
  private module TC = hcategory Type-cat
  _ : ∀ {x v} (b : C.hom x v) → TC.absorb-l b ≡ C.absorb-l b
  _ = λ b → refl

  _ : ∀ {x y} (f : C.hom x y) → C.idn C.⨾ f ≡ f
  _ = TC.unitl

  _ : ∀ {x} (e : C.hom x x)
    → (∀ {w} → is-equiv (λ (a : C.hom w x) → C.emb e w a x e))
    → C.yon e x e ≡ e → e ≡ C.idn
  _ = TC.unit-is-prop
```

`monoidal-instance`: the reference instance over `Cat.Depreciated.Monoidal.monoidal`
at the one-object `⊤`.

```agda
module monoidal-instance {o hh} {C : category o hh} (M : monoidal C) where
  private module C = Virtual C
  open monoidal M

  CompositeM : ⊤ → ⊤ → Type o
  CompositeM x y = (γ : (Σ w ∶ ⊤ , C.ob) × (Σ v ∶ ⊤ , C.ob)) → C.ob

  uncurryM : (C.ob → C.ob → C.ob) → CompositeM tt tt
  uncurryM G γ = G (γ .fst .snd) (γ .snd .snd)

  curryM : CompositeM tt tt → (C.ob → C.ob → C.ob)
  curryM F l r = F ((tt , l) , (tt , r))

  Monoidal-structure : hcategory-structure o ⊤
  Monoidal-structure .hcategory-structure.hom _ _ = C.ob
  Monoidal-structure .hcategory-structure.idn _ = I
  Monoidal-structure .hcategory-structure.emb x = uncurryM (tensor-emb x)

  Monoidal-axioms : hcategory-axioms Monoidal-structure
  Monoidal-axioms .hcategory-axioms.compose-contr x y .center =
    (x ⊗ y) , ap uncurryM (tensor-emb-composite x y)
  Monoidal-axioms .hcategory-axioms.compose-contr x y .paths (s , q) i =
    let p = tensor-compose-contr x y .paths (s , ap curryM q) i
    in p .fst , ap uncurryM (p .snd)
  Monoidal-axioms .hcategory-axioms.interchange f g a b =
    tensor-interchange f g a b
  Monoidal-axioms .hcategory-axioms.post-eval f = tensor-yon-eval f
  Monoidal-axioms .hcategory-axioms.unit-eqvl = tensor-unit-eqvl
  Monoidal-axioms .hcategory-axioms.unit-eqvr = tensor-unit-eqvr

  Monoidal-cat : hcategory 0ℓ o
  Monoidal-cat .hcategory.ob = ⊤
  Monoidal-cat .hcategory.structure = Monoidal-structure
  Monoidal-cat .hcategory.axioms = Monoidal-axioms

  -- The generic assoc reduces to the concrete ⊗-assoc.
  _ : (x y z : C.ob) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
  _ = assoc-tower.assoc Monoidal-cat {tt} {tt} {tt} {tt}

  -- The pentagon machinery specializes to the concrete monoidal category.
  module _ (x y z w : C.ob) where
    open pentagon-tower.pentagon-fibers
      Monoidal-cat {tt} {tt} {tt} {tt} {tt} x y z w
    _ = face₁₂
    _ = face₂₃
    _ = face₁₄
    _ = face₄₅
    _ = face₃₅
    _ = hom-identity
    _ = pentagon

  private module MC = hcategory Monoidal-cat
  _ : (b : C.ob) → MC.absorb-l b ≡ absorb-l b
  _ = λ b → refl

  _ : (x : C.ob) → I ⊗ x ≡ x
  _ = MC.unitl

  _ : (e : C.ob)
      (re : ∀ {_ : ⊤} → is-equiv (λ (l : C.ob) → tensor-emb e l e))
      (idpt : yon e e ≡ e)
    → e ≡ I
  _ = MC.unit-is-prop
```
