```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Bool.Properties where

open import Core.Type
open import Core.Base
open import Core.Data
open import Data.Bool

-- Involution
not-involutive : ∀ b → Bool.not (Bool.not b) ≡ b
not-involutive ff = refl
not-involutive tt = refl

-- Commutativity
and-comm : ∀ a b → a && b ≡ b && a
and-comm ff ff = refl
and-comm ff tt = refl
and-comm tt ff = refl
and-comm tt tt = refl

or-comm : ∀ a b → Bool.or a b ≡ Bool.or b a
or-comm ff ff = refl
or-comm ff tt = refl
or-comm tt ff = refl
or-comm tt tt = refl

xor-comm : ∀ a b → xor a b ≡ xor b a
xor-comm ff ff = refl
xor-comm ff tt = refl
xor-comm tt ff = refl
xor-comm tt tt = refl

-- Associativity
and-assoc : ∀ a b c → (a && b) && c ≡ a && (b && c)
and-assoc ff _ _ = refl
and-assoc tt ff _ = refl
and-assoc tt tt ff = refl
and-assoc tt tt tt = refl

or-assoc : ∀ a b c → Bool.or (Bool.or a b) c ≡ Bool.or a (Bool.or b c)
or-assoc ff ff ff = refl
or-assoc ff ff tt = refl
or-assoc ff tt _ = refl
or-assoc tt _ _ = refl

xor-assoc : ∀ a b c → xor (xor a b) c ≡ xor a (xor b c)
xor-assoc ff ff ff = refl
xor-assoc ff ff tt = refl
xor-assoc ff tt ff = refl
xor-assoc ff tt tt = refl
xor-assoc tt ff ff = refl
xor-assoc tt ff tt = refl
xor-assoc tt tt ff = refl
xor-assoc tt tt tt = refl

-- Identity elements
and-tt : ∀ b → b && tt ≡ b
and-tt ff = refl
and-tt tt = refl

tt-and : ∀ b → tt && b ≡ b
tt-and _ = refl

and-ff : ∀ b → b && ff ≡ ff
and-ff ff = refl
and-ff tt = refl

ff-and : ∀ b → ff && b ≡ ff
ff-and _ = refl

or-ff : ∀ b → Bool.or b ff ≡ b
or-ff ff = refl
or-ff tt = refl

ff-or : ∀ b → Bool.or ff b ≡ b
ff-or _ = refl

or-tt : ∀ b → Bool.or b tt ≡ tt
or-tt ff = refl
or-tt tt = refl

tt-or : ∀ b → Bool.or tt b ≡ tt
tt-or _ = refl

xor-ff : ∀ b → xor b ff ≡ b
xor-ff ff = refl
xor-ff tt = refl

-- De Morgan's laws
demorgan-and : ∀ a b → Bool.not (a && b) ≡ Bool.or (Bool.not a) (Bool.not b)
demorgan-and ff ff = refl
demorgan-and ff tt = refl
demorgan-and tt ff = refl
demorgan-and tt tt = refl

demorgan-or : ∀ a b → Bool.not (Bool.or a b) ≡ (Bool.not a) && (Bool.not b)
demorgan-or ff ff = refl
demorgan-or ff tt = refl
demorgan-or tt ff = refl
demorgan-or tt tt = refl

-- Idempotence
and-idem : ∀ b → b && b ≡ b
and-idem ff = refl
and-idem tt = refl

or-idem : ∀ b → Bool.or b b ≡ b
or-idem ff = refl
or-idem tt = refl

-- Self-inverse
xor-self : ∀ b → xor b b ≡ ff
xor-self ff = refl
xor-self tt = refl

-- Distributivity
and-distrib-or : ∀ a b c → a && (Bool.or b c) ≡ Bool.or (a && b) (a && c)
and-distrib-or ff _ _ = refl
and-distrib-or tt ff ff = refl
and-distrib-or tt ff tt = refl
and-distrib-or tt tt _ = refl

or-distrib-and : ∀ a b c → Bool.or a (b && c) ≡ (Bool.or a b) && (Bool.or a c)
or-distrib-and ff ff ff = refl
or-distrib-and ff ff tt = refl
or-distrib-and ff tt ff = refl
or-distrib-and ff tt tt = refl
or-distrib-and tt _ _ = refl

```