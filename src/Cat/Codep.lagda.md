Representable codependent categories: the trilayer presentation
(`codep-structure` / `codep-axioms` / `codep-category` bundle), its
associativity/pentagon coherence, and the coupling + unit layers.
`Cat.Codep.Instances` (the concrete `Cat.Type` and `Cat.Monoidal`
instances) is kept separate, imported on demand.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep where

open import Cat.Codep.Base public
open import Cat.Codep.Coherence public
open import Cat.Codep.Coupling public
open import Cat.Codep.Unit public
```
