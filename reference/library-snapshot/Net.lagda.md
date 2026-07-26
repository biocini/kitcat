```
{-# OPTIONS --safe --erased-cubical #-}

module Net where

open import Core.Base
open import Core.Data hiding (dup)
open import Core.HLevel
open import Core.Kan
open import Core.Equiv
open import Core.Type
open import Core.Transport

--infix 5 _~>_

-- The James construction
data FM {u} (A : Type u) (x0 : A) : Type u where
  [] : FM A x0
  _<>_ : A → FM A x0 → FM A x0
  unit : (xs : FM A x0) → xs ≡ x0 <> xs

[_] : ∀ {u} {A : Type u} {x0 : A} → A → FM A x0
[_] = _<> []

-- infixl 7 _⨾_
-- -- infixl 9 _⊗_
-- infix 40 _-

data Tree : Nat → Type where
  ε  : Tree 0
  ρ : Tree 1
  γ  : ∀ {n k} → Tree n → Tree k → Tree (n + k)
  δ  : ∀ {n k} → Tree n → Tree k → Tree (n + k)

data Gen : Type where
  tr : ∀ {n} → Tree n → Gen
  cotr : ∀ {n} → Tree n → Gen
  path : ∀ {n} (x : Tree n) → tr x ≡ cotr x

Mor = FM Gen (cotr ε)


infix 4 _>>_
data _>>_ : Nat → Nat → Type where
  nil : 0 >> 0
  ρ : ∀ {n k} → n >> k → 1 + n >> 1 + k
  τ : ∀ {n k} → n >> k → 2 + n >> 2 + k
  ∩ : ∀ {n k} → n >> k → 2 + n >> k
  ∪ : ∀ {n k} → n >> k → n >> 2 + k
  hp : ∀ {n k} → n >> k → 2 + n >> 2 + k

_◆_ : ∀ {m n k} → m >> n → n >> k → m >> k
p ◆ nil = p
ρ p ◆ ρ q = ρ (p ◆ q)
τ p ◆ ρ (ρ q) = τ (p ◆ q)
τ (ρ p) ◆ ρ (τ q) = {!!}
τ (τ p) ◆ ρ (τ q) = {!!}
τ (∩ p) ◆ ρ (τ q) = {!!}
τ (∪ p) ◆ ρ (τ q) = {!!}
τ (hp p) ◆ ρ (τ q) = {!!}
τ p ◆ ρ (∩ q) = {!!}
τ p ◆ ρ (∪ q) = {!!}
τ p ◆ ρ (hp q) = {!!}
∩ p ◆ ρ q = {!!}
∪ p ◆ ρ q = {!!}
hp p ◆ ρ q = {!!}
p ◆ τ q = {!!}
p ◆ ∩ q = {!!}
p ◆ ∪ q = {!!}
p ◆ hp q = {!!}


-- data Gen : Nat → Nat → Type where
--   φ : Gen 0 0
--   ε : ∀ {i j} → Gen i j → Gen i (1 + j)
--   γ : ∀ {i j} → Gen i j → Gen (2 + i) (1 + j)
--   δ : ∀ {i j} → Gen i j → Gen (2 + i) (1 + j)
--   _- : ∀ {m n} → Gen m n → Gen n m
--   invo : ∀ {m n} (f : Gen m n) → f ≡ f - -
--   nilp : φ ≡ φ -

-- data Partition : Nat → Nat → Type where
--   done  : Partition 0 0
--   left  : Partition l r n → Partition (1 + l) r (1 + n)
--   right : Partition l r n → Partition l (1 + r) (1 + n)

data Wire : Nat → Nat → Type where
  nil : Wire 0 0
  ρ : ∀ {i j} → Wire i j → Wire (1 + i) (1 + j)
  τ : ∀ {i j} → Wire i j → Wire (2 + i) (2 + j)
  ∩ : ∀ {i j} → Wire i j → Wire (2 + i) j
  ∪ : ∀ {i j} → Wire i j → Wire i (2 + j)

idn𝑡 : ∀ {x} → Wire x x
idn𝑡 {(Z)} = nil
idn𝑡 {S x} = ρ idn𝑡

-- data Xt : Nat → Nat → Type where
--   ctx : ∀ {i} → Xt i i
--   _⨾_ : ∀ {m n k} → Xt m n → Wire n k → Xt m k
--   rho : ∀ {m n} (xs : Xt m n) → xs ⨾ idn𝑡 ≡ xs
--   tau : ∀ {m n k l} (xs : Xt m (2 + n)) {ys : Wire n k} {zs : Wire k l}
--       → (xs ⨾ τ ys ⨾ τ zs) ≡ (xs ⨾ ρ (ρ ys) ⨾ ρ (ρ zs))
--   snake-r : ∀ {m n k} (xs : Xt m (1 + n)) {ys : Wire n k}
--           → (xs ⨾ ρ (∪ ys)) ⨾ {!!} ≡ {!!}

-- --_⋆_ :




--data Seq

-- data Gen : Nat → Nat → Type
-- --data Gen-op : Nat → Nat → Type

-- data Gen where
--   φ : Gen 0 0
--   ε : Gen 0 1
--   ε* : Gen 1 0
--   γ : Gen 2 1
--   γ* : Gen 1 2
--   δ : Gen 2 1
--   δ* : Gen 1 2
--   εε : Gen 0 2
--   χ : Gen 1 1
--   χ₁₂ : Gen 1 2
--   id2 : Gen 2 2
--   τ : Gen 2 2

-- gc : ∀ {m n k} → Gen m n → Gen n k → Gen m k
-- gc φ g = g
-- gc χ₁₂ γ = {!!}
-- gc χ₁₂ δ = {!!}
-- gc χ₁₂ id2 = {!!}
-- gc χ₁₂ τ = {!!}
-- gc ε ε* = φ
-- gc ε γ* = εε
-- gc ε δ* = εε
-- gc ε χ = ε
-- gc ε χ₁₂ = {!!}
-- gc ε* φ = ε*
-- gc ε* ε = χ
-- gc ε* εε = {!!}
-- gc γ g = {!!}
-- gc γ* g = {!!}
-- gc δ g = {!!}
-- gc δ* g = {!!}
-- gc εε g = {!!}
-- gc χ g = {!!}
-- gc id2 g = {!!}
-- gc τ g = {!!}
-- data Gen where
--   φ : Gen 0 0
--   ε : Gen 0 1
--   ε* : Gen 1 0
--   γ : Gen 2 1
--   γ* : Gen 1 2
--   δ : Gen 2 1
--   δ* : Gen 1 2
--   τ : Gen 2 2



-- data Cx : Nat → Nat → Type where
--   [] : Cx 0 0
--   _⨾_ :


-- data Vcell {m n} : FPro Gen ρ m n → FPro Gen ρ m n → Type where


--pattern _⨾_ x y = _<>_ y x

-- data ITree : Type where
--   leaf : ITree -- eraser
--   unit : ITree -- wire
--   node : Bool → ITree → ITree → ITree
--   leaf-eta : ∀ {a} → node a leaf leaf ≡ leaf -- leaf is idempotent under the magma

-- data ITape : Type where
--   [] : ITape
--   σ : ITape → ITape
--   υ : ITape → ITape
--   _⊗_ : ITree → ITape → ITape


-- data Mor : Nat → Nat → Type where
--   [] : ∀ {n} → Gen 0 n → Mor 0 n
--   _⨾_ : ∀ {m n k} → Mor m n → Gen n k → Mor m k
--   η-ε : ∀ {b m n k l} (hs : Mor m n) (f : Gen n k) (g : Gen k l)
--       → hs ⨾ ε (ε f) ⨾ cell b g ≡ hs ⨾ f ⨾ ε g
--   cross : ∀ {m n k l} (hs : Mor (2 + m) (2 + n)) (f : Gen n k) (g : Gen k l)
--         → hs ⨾ σ f  ⨾ σ g ≡ hs ⨾ ρ (ρ f) ⨾ ρ (ρ g)
--   ∪σ : ∀ {e k} {xs : Gen 0 n} (f : Gen n k)
--     → [] (υ xs) ⨾ σ f ≡ [] xs ⨾ υ f



-- Well-formed composites
-- data Cmp : List Gen → List Gen → Type where
--   emp : Cmp [] []
--   -- Canonical monoidal composites
--   ρ : ∀ {xs ys} → Cmp xs ys → Cmp (ρ ∷ xs) (ρ ∷ ys)
--   ε : ∀ {xs ys} → Cmp xs ys → Cmp xs (ε ∷ ys)
--   γ : ∀ {xs ys} → Cmp xs ys → Cmp xs {!γ ∷ ys!}

--   --ρ : ∀ xs → Cmp (xs ⨾) → Cmp {!!}




-- data Prenet : Nat → Nat → Type where
--   _◆_ : Stack → Prenet


-- data Cell : Stack → Stack → Type where
--   id0 : Cell [] []
--   sup : ∀ {xs n k} → Cell xs n k → Cell (γ ∷ xs) (2 + n) (1 + k)
--   dup : ∀ {xs n k} → Cell xs n k → Cell (δ ∷ xs) (2 + n) (1 + k)
--   era : ∀ {xs n k} → Cell xs n k → Cell (ε ∷ xs) n (1 + k)

```
data Cell : Nat → Nat → Type where
  id0 : Cell 0 0
  ε : ∀ {n k} → Cell n k → Cell n (1 + k)
  δ : ∀ {n k} → Cell n k → Cell (2 + n) (1 + k)
  γ : ∀ {n k} → Cell n k → Cell (2 + n) (1 + k)

data Wire : Type where
  id0 : Wire
  cup : Wire
  cap : Wire
  ρ : Wire
  σ : Wire

Wiring = FM (FM Wire id0) [ id0 ]


data Cx : Nat → Nat → Type where
  [] : ∀ {n} → Cx n n
  _⨾_ : ∀ {m n k} → Cx m n → Cell n k → Cx m k



  --hunit : ∀ {m n} (xs : Cx m n) → xs ≡ xs ⨾ idn
  -- η-cross : ∀ {m n k l} (x : Cell m n) (y : Cell n k) (xs : Cx (2 + k) (2 + l))
  --         → cross x ∷ cross y ∷ xs ≡ ρ (ρ x) ∷ ρ (ρ y) ∷ xs
  -- η-γ : ∀ {m n k l} (x : Cell m n) (y : Cell n k) (xs : Cx (1 + k) l)
  --     → γ* x ∷ γ y ∷ xs ≡ ρ x ∷ ρ y ∷ xs
  -- η-δ : ∀ {m n k l} (x : Cell m n) (y : Cell n k) (xs : Cx (1 + k) l)
  --     → δ* x ∷ cross idn ∷ δ y ∷ xs ≡ ρ x ∷ ρ y ∷ xs
  -- η-εδ : ∀ {m n k} (x : Cell m n) (y : Cell n k) (xs : Cx (1 + k) m)
  --     → ε (ε x) ∷ δ y ∷ xs ≡ x ∷ ε y ∷ xs
  -- η-εγ : ∀ {m n k} (x : Cell m n) (y : Cell n k) (xs : Cx (1 + k) m)
  --     → ε (ε x) ∷ γ y ∷ xs ≡ x ∷ ε y ∷ xs
  -- η-δγ : ∀ {m n k l} → (x : Cell m n) (y : Cell n k) (xs : Cx (1 + k) l)
  --      → δ (δ x) ∷ γ y ∷ xs ≡ ρ (cross (ρ idn)) ∷ γ (γ x) ∷ δ y ∷ xs

-- data Net : ∀ {m n} → Cx m n → Type where
--   empty : Net ([] {0})


-- data ⟨_⟩ : Cell → Type where
--   id0 : ⟨ 0 ~> 0 ⟩
--   idw : ∀ {n k} → ⟨ n ~> k ⟩ → ⟨ 1 + n ~> 1 + k ⟩
--   ε : ∀ {n k} → ⟨ n ~> k ⟩ → ⟨ n ~> 1 + k ⟩
--   δ : ∀ {n k} → ⟨ n ~> k ⟩ → ⟨ 2 + n ~> 1 + k ⟩
--   σ : ∀ {n k} → ⟨ n ~> k ⟩ → ⟨ 2 + n ~> 1 + k ⟩

-- ⟨_⟩* : Cell → Type
-- ⟨ m ~> k ⟩* = ⟨ k ~> m ⟩
-- ⟨ step x i ⟩* = ⟨ step x (~ i) ⟩

-- Z-sym : ∀ k → Z ~> k ≡ k ~> Z
-- Z-sym Z = refl
-- Z-sym (S k) = step (Z-sym k)

-- inv : ∀ {p} → ⟨ p ⟩ → ⟨ p ⟩*
-- inv {Z ~> Z} = id
-- inv {Z ~> S k} =  transport (ap ⟨_⟩ (step (Z-sym k)))
-- inv {S m ~> k} = {!!}
-- inv {step x i} = {!!}

```
