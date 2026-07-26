Lane Biocini
February 2025

Wild categories with quasi-unital identities.

In what follows we engages in a synthesis over the following
constructions, but guided along the lines of Chen's "2-Coherent
Internal Models of Homotopical Type Theory" as well as
Capirotti-Kraus' work. The idea is we define a notion of identity that
is a *characterization* of the sort of data that satisfies the
definition of a unital morphism, such that any other morphism
satisfying this characterization is provably identical to the
canonical one.

Implicitly this entails we shift our perspective with regard to

References:
- John Chen, "Semicategories with Identities"
           & "2-Coherent Internal Models of Homotopical Type Theory"
- Capriotti-Kraus, "Univalent Higher Categories via Complete Semi-Segal Types"

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Cat.Magmoid where

open import Cat.Magmoid.Base public
open import Cat.Magmoid.Units public
open import Cat.Magmoid.Assoc public
```
