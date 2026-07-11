Representable codependent categories: the trilayer presentation
(`hcategory-structure` / `hcategory-axioms` / `hcategory` bundle)
and its associativity/pentagon coherence. The coupling and unit
fragments are consolidated into `hcategory-axioms` (`Cat.Codep.Base`)
— the former `Cat.Codep.Coupling`/`Cat.Codep.Unit` modules are
absorbed there. `Cat.Codep.Instances` (the concrete `Cat.Type` and
`Cat.Monoidal` instances) is kept separate, imported on demand.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Codep where

open import Cat.Codep.Base public
open import Cat.Codep.Coherence public
```
