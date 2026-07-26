Virtual double category structure with tight and loose morphisms.

```agda

{-# OPTIONS --safe --erased-cubical #-}

module Core.Virtual where

open import Core.Type
open import Core.Base
open import Core.Data
open import Core.Kan
open import Core.Transport
open import Core.Equiv
open import Core.HLevel
open import Core.Trait.Cast

record Virtual v w : Type (v ₊ ⊔ w ₊) where
  field
    Ob : Type v
    Tc : Ob → Ob → Type w -- tight morphisms (cells)

    cat𝑡 : ∀ {a b c} → Tc a b → Tc b c → Tc a c
    vassoc : ∀ {a b c d} (f : Tc a b) (g : Tc b c) (h : Tc c d)
           → cat𝑡 (cat𝑡 f g) h ≡ cat𝑡 f (cat𝑡 g h)
    idn-tight : ∀ x → Σ i ∶ Tc x x
                    , (cat𝑡 i i ≡ i)
                    × (∀ {w} → is-equiv (λ (f : Tc w x) → cat𝑡 f i)
                    × (∀ {y} → is-equiv (λ (f : Tc x y) → cat𝑡 i f)))

  idnT : ∀ {x} → Tc x x
  idnT {x} = fst (idn-tight x)

  videm = fst ∘ snd ∘ idn-tight

  field
    Lc : Ob → Ob → Type w -- loose morphisms (cells)
    Comp : Ob → Ob → Type w
    cut : ∀ {m n k} → Comp m n → Lc n k → Comp m k
    Vcell : ∀ {a b c d}
          → Tc a c
          → Lc a b
          → Tc b d
          → Lc c d
          → Type w

  -- fibroid : ∀ {a b c} → Lc b c → Lc a c → Type w
  -- fibroid {a} {b} h s = Σ g ∶ Lc a b , Vcell idnT (cut g h) idnT s

  -- cofibroid : ∀ {a b c} → Lc a b → Lc a c → Type w
  -- cofibroid {b = b} {c} g s = Σ h ∶ Lc b c , Vcell idnT (cut g h) idnT s

  -- is-isomorphism : ∀ {x y} → Lc x y → Type (v ⊔ w)
  -- is-isomorphism {x} {y} e = (∀ {w} (f : Lc w y) → is-contr (fibroid e f))
  --                          × (∀ {z} (f : Lc x z) → is-contr (cofibroid e f))

  -- is-loose-unit : ∀ {x} → Lc x x → Type (v ⊔ w)
  -- is-loose-unit {x} i = (∀ {w} (f : Lc w x) → Vcell idnT (cut (cut f i) i) idnT (cut f i))
  --                     × (∀ {y} (f : Lc x y) → Vcell idnT (cut i (cut i f)) idnT (cut i f))
  --                     × is-isomorphism i

  -- is-unital : ∀ x → Type (v ⊔ w)
  -- is-unital x = Σ i ∶ Lc x x , is-loose-unit i

  -- span : ∀ {x c d} → Tc x c → Tc x d → Lc c d → Type (v ⊔ w)
  -- span {x} f g q = Σ 𝟙 ∶ is-unital x , Vcell f (𝟙 .fst) g q

  -- cospan : ∀ {a b y} → Tc a y → Tc b y → Lc a b → Type (v ⊔ w)
  -- cospan {y = y} f g p = Σ 𝟙 ∶ is-unital y , Vcell f p g (𝟙 .fst)

  -- all-composites : Type (v ⊔ w)
  -- all-composites = ∀ x → is-unital x

  -- comp-η : ∀ {a b} → Tc a b  → Lc a b → Type (v ⊔ w)
  -- comp-η {a = a} f s = Σ 𝟙 ∶ is-unital a , Vcell idnT (𝟙 .fst) f s

  -- comp-ε : ∀ {a b} → Tc a b  → Lc a b → Type (v ⊔ w)
  -- comp-ε {b = b} f s = Σ 𝟙 ∶ is-unital b , Vcell f s idnT (𝟙 .fst)

  -- conj-η : ∀ {a b} → Tc a b  → Lc b a → Type (v ⊔ w)
  -- conj-η {a = a} f s = Σ 𝟙 ∶ is-unital a , Vcell f (𝟙 .fst) idnT s

  -- conj-ε : ∀ {a b} → Tc a b  → Lc b a → Type (v ⊔ w)
  -- conj-ε {b = b} f s = Σ 𝟙 ∶ is-unital b , Vcell idnT s f (𝟙 .fst)

```
  field
    vcomp : ∀ {a b c x y z u v f g h k}
          → {s0 : Lc a b} {s1 : Lc b c}
          → {t0 : Lc x y} {t1 : Lc y z}
          → Vcell f (cut s0 s1) h (cut t0 t1)
          → {r : Lc u v} → Vcell g (cut t0 t1) k r
          → Vcell (cat𝑡 f g) (cut s0 s1) (cat𝑡 h k) r
    vcomp-assoc : ∀ {a b c x y z u' v' w' p q f g i h k j}
                → {s0 : Lc a b} {s1 : Lc b c}
                → {t0 : Lc x y} {t1 : Lc y z}
                → {u0 : Lc u' v'} {u1 : Lc v' w'}
                → {r : Lc p q}
                → (α : Vcell f (cut s0 s1) h (cut t0 t1))
                → (β : Vcell g (cut t0 t1) k (cut u0 u1))
                → (γ : Vcell i (cut u0 u1) j r)
                → PathP (λ l → Vcell (vassoc f g i l) (cut s0 s1) (vassoc h k j l) r)
                        (vcomp (vcomp α β) γ)
                        (vcomp α (vcomp β γ))
    veqv : ∀ {a b} {f : Lc a b} → Vcell idnT f idnT f
    veqv-idem : ∀ {a b c} {s0 : Lc a b} {s1 : Lc b c}
              → PathP (λ i → Vcell (videm a i) (cut s0 s1) (videm c i) (cut s0 s1))
                 (vcomp veqv veqv) veqv
    veqv-divl : ∀ {a b c x y f g} {s0 : Lc a b} {s1 : Lc b c} {t : Lc x y}
              → is-equiv (λ (β : Vcell f (cut s0 s1) g t) → vcomp veqv β)
    veqv-divr : ∀ {a b c x y z f g} {s0 : Lc a b} {s1 : Lc b c} {t0 : Lc x y} {t1 : Lc y z}
              → is-equiv (λ (α : Vcell f (cut s0 s1) g (cut t0 t1)) → vcomp α veqv)

  glob-contr : ∀ {a b c} (p : Lc a b) (q : Lc b c)
              → is-contr (Σ s ∶ Lc a c , Vcell idnT (cut p q) idnT s)
  glob-contr p q = Contr ((cut p q) , veqv) λ (s , α) → cut-total p q idnT idnT ((cut p q) , veqv) (s , α)

  vcomp-glob : ∀ {a b c x y z u v f g h k}
        → {s0 : Lc a b} {s1 : Lc b c}
        → {t0 : Lc x y} {t1 : Lc y z}
        → Vcell f (cut s0 s1) h (cut t0 t1)
        → {r : Lc u v} → Vcell g (cut t0 t1) k r
        → Vcell (cat𝑡 f g) (cut s0 s1) (cat𝑡 h k) r
  vcomp-glob p q = transport {!!} p

  -- Notation for globular cells
  _=>_ : ∀ {x y} → Lc x y → Lc x y → Type w
  f => g = Vcell idnT f idnT g

    -- Weak divisibility (propositional)
  weakly-right-divisible : ∀ {x y z} → Lc x y → Lc x z → Type w
  weakly-right-divisible f s = is-prop (cofibroid f s)

  weakly-left-divisible : ∀ {w x y} → Lc x y → Lc w y → Type _
  weakly-left-divisible f s = is-prop (fibroid f s)

  -- Strong divisibility (contractible)
  right-divisible : ∀ {x y z} → Lc x y → Lc x z → Type w
  right-divisible f s = is-contr (cofibroid f s)

  left-divisible : ∀ {w x y} → Lc x y → Lc w y → Type _
  left-divisible f s = is-contr (fibroid f s)

  -- Isomorphism of loose morphisms
  is-loose-iso : ∀ {x y} → Lc x y → Type (v ⊔ w)
  is-loose-iso {x} {y} f =
      (∀ {w} (s : Lc w y) → left-divisible f s)
    × (∀ {z} (s : Lc x z) → right-divisible f s)

  -- -- Homotopy (equivalence of globular cells)
--   is-homotopy : ∀ {x y} {s r : Lc x y} → s => r → Type w
--   is-homotopy {s = s} {r} H =
--       (∀ {k} (S : s => k) → is-contr (2-fibroid H S))
--     × (∀ {h} (S : h => r) → is-contr (2-cofibroid H S))

--   -- veqv is a homotopy
--   veqv-is-homotopy : ∀ {a b c} {s0 : Lc a b} {s1 : Lc b c}
--                    → is-homotopy (veqv {f = cut s0 s1})
--   veqv-is-homotopy = {!!}  -- derivable from veqv-homotopy

-- ```
