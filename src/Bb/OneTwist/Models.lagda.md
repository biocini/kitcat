Spike: the one-twist carrier against the two stock models.

`Bb.WeakDeductiveSystem.Gist.FramedCut` and
`Bb.WeakDeductiveSystem.Gist.FramedGroup` run the two-twist
record through the path groupoid and the abelian group. This
spike runs the
one-twist carrier of `Bb.OneTwist.Base`, with the `⁺` tier of
`Bb.OneTwist.Cancel`, through the same two models.

The path groupoid inhabits every field at an arbitrary negative
framing over an arbitrary type, with no h-level hypothesis — the
carrier imposes no truncation. The abelian group inhabits every field
at an arbitrary element, and there the extraction shows its teeth: any
proof of the `⁻` tier has the twist's inverse as its centre, so the
framing freedom is one element where the two-twist record has two. The
`⁺` centre is the double inverse, so the term-side cancellation holds
in every group model — the separation needs the twisted reflection of
`Bb.OneTwist.Cancel`.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.OneTwist.Models where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan using (_∙_; is-contr→is-prop)
open import Core.Path.Base
open import Core.Equiv.Base using (_≃_; is-equiv; eqv-fibers; iso→equiv)
open import Core.Equiv.Properties using (_∙e_; Π-contr-dom)
open import Core.Groupoid.Virtual using (module yon-unbiased)
open import Core.HLevel.Base using (Π-is-hlevel)
open import Core.Function.Embedding using (injective→is-embedding)
open import Core.Transport.Properties using (prop-inhabited→is-contr)

open import Bb.OneTwist.Base
open import Bb.OneTwist.Cancel using (module system⁻)
```

## The path groupoid, framed on one side

```agda
module path-model {u} {A : Type u} (t⁻ : (x : A) → x ≡ x) where

  emb : {x y : A} → x ≡ y → ∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z
  emb = yon-unbiased.emb {A = λ _ → A}

  emb-equiv : {x y : A} → is-equiv (emb {x} {y})
  emb-equiv = yon-unbiased.emb-equiv {A = λ _ → A}

  Tm : A → Type u
  Tm x = Sigma A (λ w → w ≡ x)

  Cot : A → Type u
  Cot y = Sigma A (λ v → y ≡ v)

  Rf : {x y : A} → x ≡ y → (γ : Tm x × Cot y) → γ .fst .fst ≡ γ .snd .fst
  Rf f γ = emb f (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd)

  term-contr : ∀ x → is-contr (Tm x)
  term-contr x .center = x , refl
  term-contr x .paths (w , p) i = p (~ i) , λ j → p (~ i ∨ j)

  coterm-contr : ∀ y → is-contr (Cot y)
  coterm-contr y .center = y , refl
  coterm-contr y .paths (v , p) i = p i , λ j → p (i ∧ j)

  recentre : ∀ {ℓ} {T : Type ℓ} → is-contr T → T → is-contr T
  recentre c t .center = t
  recentre c t .paths s = sym (c .paths t) ∙ c .paths s

  curry≃ : ∀ {x y}
         → (∀ w → w ≡ x → ∀ z → y ≡ z → w ≡ z)
         ≃ ((γ : Tm x × Cot y) → γ .fst .fst ≡ γ .snd .fst)
  curry≃ = iso→equiv
    (λ Φ γ → Φ (γ .fst .fst) (γ .fst .snd) (γ .snd .fst) (γ .snd .snd))
    (λ α w p z r → α ((w , p) , (z , r)))
    (λ _ → refl) (λ _ → refl)

  Rf-equiv : ∀ {x y} → is-equiv (Rf {x} {y})
  Rf-equiv = ((emb , emb-equiv) ∙e curry≃) .snd

  slot≃ : ∀ {x y}
        → ((γ : Tm x × Cot y) → γ .fst .fst ≡ γ .snd .fst)
        ≃ ((t : Tm x) (γ : Cot y) → t .fst ≡ γ .fst)
  slot≃ = iso→equiv (λ α t γ → α (t , γ)) (λ Φ δ → Φ (δ .fst) (δ .snd))
                    (λ _ → refl) (λ _ → refl)

  slot-swap≃ : ∀ {x y}
             → ((γ : Tm x × Cot y) → γ .fst .fst ≡ γ .snd .fst)
             ≃ ((γ : Cot y) (t : Tm x) → t .fst ≡ γ .fst)
  slot-swap≃ = iso→equiv (λ α γ t → α (t , γ)) (λ Φ δ → Φ (δ .snd) (δ .fst))
                         (λ _ → refl) (λ _ → refl)

  cπ-equiv : ∀ x → is-equiv (λ (f : x ≡ x) (k : Cot x) → Rf f ((x , t⁻ x) , k))
  cπ-equiv x =
    ( (Rf , Rf-equiv)
    ∙e slot≃
    ∙e Π-contr-dom (recentre (term-contr x) (x , t⁻ x)) ) .snd
```

Both cuts land in fibers of an equivalence, so representability is
total and the composite formulas can be written out flat.

```agda
  C⁺ : ∀ {x y z} (f : x ≡ y) (g : y ≡ z)
     → (γ : Tm x × Cot z) → γ .fst .fst ≡ γ .snd .fst
  C⁺ {y = y} f g γ =
    Rf f (γ .fst , (γ .snd .fst , Rf g ((y , t⁻ y) , γ .snd)))

  τ⁺ : (x : A) → x ≡ x
  τ⁺ x = eqv-fibers (cπ-equiv x) snd .center .fst

  C⁻ : ∀ {x y z} (f : x ≡ y) (g : y ≡ z)
     → (γ : Tm x × Cot z) → γ .fst .fst ≡ γ .snd .fst
  C⁻ {y = y} f g γ =
    Rf g ((γ .fst .fst , Rf f (γ .fst , (y , τ⁺ y))) , γ .snd)

  PG : graph⁻ u u
  PG .graph⁻.ob       = A
  PG .graph⁻.hom x y  = x ≡ y
  PG .graph⁻.reflect  = Rf
  PG .graph⁻.twist⁻   = t⁻
  PG .graph⁻.unital⁻ x = eqv-fibers (cπ-equiv x) snd
  PG .graph⁻.stable α  = is-contr→is-prop (eqv-fibers Rf-equiv α)
  PG .graph⁻.cut⁺ f g  = eqv-fibers Rf-equiv (C⁺ f g) .center
  PG .graph⁻.cut⁻ f g  = eqv-fibers Rf-equiv (C⁻ f g) .center

  aπ-equiv : ∀ x → is-equiv (graph⁻.act-π PG {x} {x})
  aπ-equiv x =
    ( (Rf , Rf-equiv)
    ∙e slot-swap≃
    ∙e Π-contr-dom (recentre (coterm-contr x) (x , τ⁺ x)) ) .snd

  PG-invertible⁺ : ∀ x → is-contr (fiber (graph⁻.act-π PG {x} {x}) snd)
  PG-invertible⁺ x = eqv-fibers (aπ-equiv x) snd

  open system⁻ PG PG-invertible⁺ using (unitl⁻; cancel⁺; agree)
```

Every field of the carrier and both tiers, at an arbitrary one-sided
framing over an arbitrary type — no h-level enters.

## The abelian group, framed on one side

```agda
module group-model {u} {A : Type u}
  (_·_ : A → A → A) (e : A) (inv : A → A)
  (A-set : is-set A)
  (assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))
  (comm  : ∀ a b → a · b ≡ b · a)
  (unitl : ∀ a → e · a ≡ a)
  (invl  : ∀ a → inv a · a ≡ e)
  (t⁻ : A)
  where

  unitr : ∀ a → a · e ≡ a
  unitr a = comm a e ∙ unitl a

  invr : ∀ a → a · inv a ≡ e
  invr a = comm a (inv a) ∙ invl a

  inv-invol : ∀ a → inv (inv a) ≡ a
  inv-invol a = cancel-r (inv a) (invl (inv a) ∙ sym (invr a))
    where
    cancel-r : ∀ b {x y} → x · b ≡ y · b → x ≡ y
    cancel-r b {x} {y} p =
      sym (unitr x)
      ∙ ap (x ·_) (sym (invl b) ∙ comm (inv b) b)
      ∙ sym (assoc x b (inv b))
      ∙ ap (_· inv b) p
      ∙ assoc y b (inv b)
      ∙ ap (y ·_) (invr b)
      ∙ unitr y

  cancel-l : ∀ a {x y} → a · x ≡ a · y → x ≡ y
  cancel-l a {x} {y} p =
    sym (unitl x)
    ∙ ap (_· x) (sym (invl a))
    ∙ assoc (inv a) a x
    ∙ ap (inv a ·_) p
    ∙ sym (assoc (inv a) a y)
    ∙ ap (_· y) (invl a)
    ∙ unitl y

  cancel-r : ∀ a {x y} → x · a ≡ y · a → x ≡ y
  cancel-r a {x} {y} p = cancel-l a (comm a x ∙ p ∙ comm y a)

  cπ : A → Sigma ⊤ (λ _ → A) → A
  cπ m k = t⁻ · (m · k .snd)

  aπ : A → Sigma ⊤ (λ _ → A) → A
  aπ m t = t .snd · (m · inv t⁻)

  gf : A → Sigma ⊤ (λ _ → A) × Sigma ⊤ (λ _ → A) → A
  gf m γ = γ .fst .snd · (m · γ .snd .snd)

  cπ-inj : {m n : A} → cπ m ≡ cπ n → m ≡ n
  cπ-inj p = cancel-r e (cancel-l t⁻ (happly p (tt , e)))

  aπ-inj : {m n : A} → aπ m ≡ aπ n → m ≡ n
  aπ-inj p = cancel-r (inv t⁻) (cancel-l e (happly p (tt , e)))

  gf-inj : {m n : A} → gf m ≡ gf n → m ≡ n
  gf-inj p = cancel-r e (cancel-l e (happly p ((tt , e) , (tt , e))))

  absorb-wit : ∀ (k : Sigma ⊤ (λ _ → A)) → cπ (inv t⁻) k ≡ k .snd
  absorb-wit k =
    sym (assoc t⁻ (inv t⁻) (k .snd)) ∙ ap (_· k .snd) (invr t⁻) ∙ unitl (k .snd)

  tier⁻ : is-contr (fiber cπ snd)
  tier⁻ = prop-inhabited→is-contr
    (injective→is-embedding (Π-is-hlevel 2 λ _ → A-set) cπ cπ-inj snd)
    (inv t⁻ , funext absorb-wit)

  tier⁺ : is-contr (fiber aπ snd)
  tier⁺ = prop-inhabited→is-contr
    (injective→is-embedding (Π-is-hlevel 2 λ _ → A-set) aπ aπ-inj snd)
    ( inv (inv t⁻)
    , funext λ t → ap (t .snd ·_) (invl (inv t⁻)) ∙ unitr (t .snd) )

  GM : graph⁻ 0ℓ u
  GM .graph⁻.ob       = ⊤
  GM .graph⁻.hom _ _  = A
  GM .graph⁻.reflect m γ = γ .fst .snd · (m · γ .snd .snd)
  GM .graph⁻.twist⁻ _ = t⁻
  GM .graph⁻.unital⁻ x = tier⁻
  GM .graph⁻.stable α =
    injective→is-embedding (Π-is-hlevel 2 λ _ → A-set) gf gf-inj α
  GM .graph⁻.cut⁺ f g = f · (t⁻ · g) , funext λ γ →
    ap (γ .fst .snd ·_)
      (assoc f (t⁻ · g) (γ .snd .snd) ∙ ap (f ·_) (assoc t⁻ g (γ .snd .snd)))
  GM .graph⁻.cut⁻ f g = (f · inv t⁻) · g , funext λ γ →
    ap (γ .fst .snd ·_) (assoc (f · inv t⁻) g (γ .snd .snd))
    ∙ sym (assoc (γ .fst .snd) (f · inv t⁻) (g · γ .snd .snd))

  GM-invertible⁺ : ∀ x → is-contr (fiber (graph⁻.act-π GM {x} {x}) snd)
  GM-invertible⁺ x = tier⁺

  open system⁻ GM GM-invertible⁺ using (agree; cancel⁺; agree→cancel⁺)
```

The extraction is forced: whatever proof the `⁻` tier is given, its
centre is the inverse of the posited twist. The two-twist record's
second framing element collapses to one point.

```agda
  twist⁺-forced : (c : is-contr (fiber (graph⁻.coact-π GM {tt} {tt}) snd))
                → c .center .fst ≡ inv t⁻
  twist⁺-forced c = ap fst (c .paths (inv t⁻ , funext absorb-wit))
```

And the `⁺` centre is the double inverse, so the term-side
cancellation holds in every abelian-group model: the group cannot
separate the centre from the posited twist.

```agda
  group-agree : agree
  group-agree x = inv-invol t⁻

  group-cancel⁺ : cancel⁺
  group-cancel⁺ = agree→cancel⁺ group-agree
```
