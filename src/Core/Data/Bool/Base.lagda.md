Operations on booleans.

```agda

{-# OPTIONS --safe --cubical-compatible --no-guardedness #-}

module Core.Data.Bool.Base where

open import Core.Type
open import Core.Data.Bool.Type
open import Core.Data.Empty using (⊥; ex-falso)

ind : ∀ {u} (P : Bool → Type u) → P true → P false → ∀ b → P b
ind P t f true  = t
ind P t f false = f
{-# INLINE ind #-}

not : Bool → Bool
not true  = false
not false = true
{-# INLINE not #-}

and : Bool → Bool → Bool
and true  b = b
and false b = false
{-# INLINE and #-}

_&&_ : Bool → Bool → Bool
_&&_ = and
{-# INLINE _&&_ #-}
infixr 6 _&&_

or : Bool → Bool → Bool
or true  b = true
or false b = b
{-# INLINE or #-}

_||_ : Bool → Bool → Bool
_||_ = or
{-# INLINE _||_ #-}
infixr 5 _||_

xor : Bool → Bool → Bool
xor true  true  = false
xor true  false = true
xor false true  = true
xor false false = false
{-# INLINE xor #-}

implies : Bool → Bool → Bool
implies false _ = true
implies true  b = b
{-# INLINE implies #-}

if-then-else : ∀ {u} {@0 P : Bool → Type u} (b : Bool) → P true → P false → P b
if-then-else true  x y = x
if-then-else false x y = y
{-# INLINE if-then-else #-}

```

## Boolean witnesses

`So` sends a boolean check to the proposition it decides: the
contractible case at `true`, the empty one at `false`.

```agda

So : Bool → Type
So true  = ⊤
So false = ⊥

so-and : ∀ a b → So a → So b → So (a && b)
so-and true  b sa sb = sb
so-and false b sa sb = ex-falso sa

so-fst : ∀ a b → So (a && b) → So a
so-fst true  b s = tt
so-fst false b s = ex-falso s

so-snd : ∀ a b → So (a && b) → So b
so-snd true  b s = s
so-snd false b s = ex-falso s

so-absurd : ∀ b → So b → So (not b) → ⊥
so-absurd true  s ns = ns
so-absurd false s ns = s

```
