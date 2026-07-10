Lane Biocini
July 2026

Instances of the trilayer. `walking-arrow` is the simplest possible one
— the interval category **2**, a direct multi-object triple — kept as
the API's worked example and the regression guard for the termination
class the split defeats. `type-instance` and `monoidal-instance` are
the two reference instances, each abstracting a concrete category from
the `Cat.*` layer as a structure + axioms + bundle triple, together
with their five-axiom fills and the specialization checks that the
generic `assoc`, `pentagon`, and unit fragment instantiate at each.

`type-instance` reads off `Cat.Type.category` — the anchor is the
identity morphism `C.idn`, and the merged axioms' coupling/unit fills
are name-identical to `Cat.Type`'s own (`unit-eqvl = C.unit-eqvl`).
`monoidal-instance` reads off `Cat.Monoidal.monoidal` over the
one-object `⊤` — the anchor is the tensor unit object `I`, and with the
canonical binder the passenger is `⊤`-wrapped one level deeper.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep.Instances where

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

open import Cat.Type
open import Cat.Monoidal
open import Cat.Codep
```

The walking arrow **2**: a direct, naive `codep-structure` +
`codep-axioms` + `codep-category` triple. It is thin (every hom a
proposition), so `composite` is a Π into propositions and the five
axioms are prop-level: `compose-contr` from the contractible image
fibre, `interchange`/`post-eval` immediate, the two unit equivalences
from `Core.Equiv.Properties.prop→endo-is-equiv` (a thin endomap of a
proposition is an equivalence). It is a non-groupoid (`hom o1 o0 = ⊥`);
and its `emb` is
an equivalence — the last cell of the `emb`-equivalence × groupoid-ness
independence square. A multi-object instance whose `idn` cases on the
object was exactly the shape that tripped the termination checker before
the split; that it now goes through directly is what this instance
certifies.

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

  walk-structure : codep-structure Ob
  walk-structure .codep-structure.hom = homW
  walk-structure .codep-structure.idn o0 = tt
  walk-structure .codep-structure.idn o1 = tt
  walk-structure .codep-structure.emb f ((_ , (_ , a)) , b) = comp3 a f b

  open codep-structure walk-structure

  -- `composite` is a Π into propositions, hence a proposition.
  comp-prop : ∀ {x y} → is-prop (composite x y)
  comp-prop F G = funext (λ γ → hom-prop _ _ (F γ) (G γ))

  walk-axioms : codep-axioms walk-structure
  walk-axioms .codep-axioms.compose-contr {x} {_} {z} f g =
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
  walk-axioms .codep-axioms.interchange f g a b = hom-prop _ _ _ _
  walk-axioms .codep-axioms.post-eval f = hom-prop _ _ _ _
  walk-axioms .codep-axioms.unit-eqvl {x} {v} =
    prop→endo-is-equiv (hom-prop x v) (pre (idn x) {v})
  walk-axioms .codep-axioms.unit-eqvr {x} {w} =
    prop→endo-is-equiv (hom-prop w x) (post (idn x) {w})

  walk-cat : codep-category 0ℓ 0ℓ
  walk-cat .codep-category.ob = Ob
  walk-cat .codep-category.structure = walk-structure
  walk-cat .codep-category.axioms = walk-axioms

  -- Thin `emb` is an equivalence: evaluation at the canonical context
  -- inverts it, `composite` being a Π into propositions.
  emb-is-equiv : ∀ {x y} → is-equiv (emb {x} {y})
  emb-is-equiv {x} {y} .eqv-fibers F =
    prop-inhabited→is-contr fib-prop (F γ⋆ , comp-prop _ _)
    where
      γ⋆ : ctx x y
      γ⋆ = (y , (x , idn x)) , idn y

      emb-inj : ∀ {h h'} → emb h ≡ emb h' → h ≡ h'
      emb-inj {h} {h'} _ = hom-prop x y h h'

      fib-prop : is-prop (fiber emb F)
      fib-prop =
        injective→is-embedding
          (Π-is-set (λ _ → is-prop→is-set (hom-prop _ _))) emb emb-inj F
```

`type-instance`: the reference instance over `Cat.Type.category`. The
five-axiom fills are name-identical to `Cat.Type`'s own operations.

```agda
module type-instance {o h} (C : category o h) where
  private module C = Virtual C

  CompositeT : C.ob → C.ob → Type (o ⊔ h)
  CompositeT x y =
    (γ : Σ φ ∶ (Σ v ∶ C.ob , (Σ w ∶ C.ob , C.hom w x)) , C.hom y (φ .fst))
    → C.hom (γ .fst .snd .fst) (γ .fst .fst)

  uncurryT : ∀ {x y}
    → (∀ w → C.hom w x → ∀ v → C.hom y v → C.hom w v)
    → CompositeT x y
  uncurryT G γ =
    G (γ .fst .snd .fst) (γ .fst .snd .snd) (γ .fst .fst) (γ .snd)

  curryT : ∀ {x y}
    → CompositeT x y
    → (∀ w → C.hom w x → ∀ v → C.hom y v → C.hom w v)
  curryT F w a v b = F ((v , (w , a)) , b)

  Type-structure : codep-structure {o} {h} C.ob
  Type-structure .codep-structure.hom = C.hom
  Type-structure .codep-structure.idn x = C.idn
  Type-structure .codep-structure.emb f = uncurryT (C.emb f)

  Type-axioms : codep-axioms Type-structure
  Type-axioms .codep-axioms.compose-contr f g .center =
    (f C.⨾ g) , ap uncurryT (C.compose-contr f g .center .snd)
  Type-axioms .codep-axioms.compose-contr f g .paths (s , q) i =
    let p = C.compose-contr f g .paths (s , ap curryT q) i
    in p .fst , ap uncurryT (p .snd)
  Type-axioms .codep-axioms.interchange f g {w} a {v} b =
    C.interchange f g w a v b
  Type-axioms .codep-axioms.post-eval f = C.yon-eval f
  Type-axioms .codep-axioms.unit-eqvl = C.unit-eqvl
  Type-axioms .codep-axioms.unit-eqvr = C.unit-eqvr

  Type-cat : codep-category o h
  Type-cat .codep-category.ob = C.ob
  Type-cat .codep-category.structure = Type-structure
  Type-cat .codep-category.axioms = Type-axioms

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
    _ = face₃₅-proof.face₃₅ Type-cat f g h k
    _ = hom-identity
    _ = pentagon.pentagon Type-cat f g h k

  private module UT = unit-laws Type-cat
  _ : ∀ {x v} (b : C.hom x v) → UT.absorb-l b ≡ C.absorb-l b
  _ = λ b → refl

  _ : ∀ {x y} (f : C.hom x y) → C.idn C.⨾ f ≡ f
  _ = UT.unitl

  _ : ∀ {x} (e : C.hom x x)
    → (∀ {w} → is-equiv (λ (a : C.hom w x) → C.emb e w a x e))
    → C.yon e x e ≡ e → e ≡ C.idn
  _ = UT.unit-is-prop
```

`monoidal-instance`: the reference instance over `Cat.Monoidal.monoidal`
at the one-object `⊤`.

```agda
module monoidal-instance {o hh} {C : category o hh} (M : monoidal C) where
  private module C = Virtual C
  open monoidal M

  CompositeM : ⊤ → ⊤ → Type o
  CompositeM x y = (γ : Σ φ ∶ (⊤ × (Σ v ∶ ⊤ , C.ob)) , C.ob) → C.ob

  uncurryM : (C.ob → C.ob → C.ob) → CompositeM tt tt
  uncurryM G γ = G (γ .fst .snd .snd) (γ .snd)

  curryM : CompositeM tt tt → (C.ob → C.ob → C.ob)
  curryM F l r = F ((tt , (tt , l)) , r)

  Monoidal-structure : codep-structure {0ℓ} {o} ⊤
  Monoidal-structure .codep-structure.hom _ _ = C.ob
  Monoidal-structure .codep-structure.idn _ = I
  Monoidal-structure .codep-structure.emb x = uncurryM (tensor-emb x)

  Monoidal-axioms : codep-axioms Monoidal-structure
  Monoidal-axioms .codep-axioms.compose-contr x y .center =
    (x ⊗ y) , ap uncurryM (tensor-emb-composite x y)
  Monoidal-axioms .codep-axioms.compose-contr x y .paths (s , q) i =
    let p = tensor-compose-contr x y .paths (s , ap curryM q) i
    in p .fst , ap uncurryM (p .snd)
  Monoidal-axioms .codep-axioms.interchange f g a b =
    tensor-interchange f g a b
  Monoidal-axioms .codep-axioms.post-eval f = tensor-yon-eval f
  Monoidal-axioms .codep-axioms.unit-eqvl = tensor-unit-eqvl
  Monoidal-axioms .codep-axioms.unit-eqvr = tensor-unit-eqvr

  Monoidal-cat : codep-category 0ℓ o
  Monoidal-cat .codep-category.ob = ⊤
  Monoidal-cat .codep-category.structure = Monoidal-structure
  Monoidal-cat .codep-category.axioms = Monoidal-axioms

  -- The generic assoc reduces to the concrete ⊗-assoc.
  _ : (x y z : C.ob) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
  _ = assoc-tower.assoc Monoidal-cat {tt} {tt} {tt} {tt}

  -- The pentagon machinery specializes to the concrete monoidal category.
  module _ (x y z w : C.ob) where
    open pentagon-tower.pentagon-fibers Monoidal-cat {tt} {tt} {tt} {tt} {tt} x y z w
    _ = face₁₂
    _ = face₂₃
    _ = face₁₄
    _ = face₄₅
    _ = face₃₅-proof.face₃₅ Monoidal-cat {tt} {tt} {tt} {tt} {tt} x y z w
    _ = hom-identity
    _ = pentagon.pentagon Monoidal-cat {tt} {tt} {tt} {tt} {tt} x y z w

  private module UM = unit-laws Monoidal-cat
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
