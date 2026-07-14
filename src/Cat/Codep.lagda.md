Representable codependent categories: the trilayer presentation
(`category-structure` / `category-axioms` / `category` bundle)
and its associativity/pentagon coherence. The coupling and unit
fragments are consolidated into `category-axioms` (`Cat.Type`)
— the former `Cat.Codep.Coupling`/`Cat.Codep.Unit` modules are
absorbed there. `Cat.Codep.Op` builds the opposite category as the
polarity mirror — reversing `hom` and swapping `pre ↔ post` — and
certifies `op (op C) ≡ C`. `Cat.Codep.Coherent` overlays the three
wild-categorical coherence cells on the bundle and dualizes them
covariantly along `op`. `Cat.Codep.Triangle` carries the Mac Lane
weak triangle (associator plus the free unitr face) over the bundle;
its full-triangle unitl face is blocked at the `absorb-r`/`post-eval`
inner-form mismatch documented there. `Cat.Codep.Instances` (the
concrete `Cat.Type` and `Cat.Monoidal` instances) is kept separate,
imported on demand.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep where

open import Cat.Type public
open import Cat.Codep.Coherence public
open import Cat.Codep.Coherent public
open import Cat.Codep.Op public
open import Cat.Codep.Triangle public
```
