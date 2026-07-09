
```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module All where

import Cat.Base
import Cat.Coherence
import Cat.Covariant
import Cat.Dep
import Cat.Groupoid
import Cat.Iso
import Cat.Monoidal
import Cat.Monoidal.Bifunctor
import Cat.Monoidal.Coherence
import Cat.Monoidal.Iso
import Cat.Type
import Cat.Virtual
import Cat.Virtual.Product
import Cat.Yoneda

import Core.Data.Bool
import Core.Data.Empty
import Core.Data.Fin
import Core.Data.Fin.Monotone
import Core.Data.Id
import Core.Data.List
import Core.Data.Maybe
import Core.Data.Nat
import Core.Data.Pointed
import Core.Data.String
import Core.Data.Sum
import Core.Data.Trunc
import Core.Discrete
import Core.Equiv.PropIndexed
import Core.Function
import Core.Function.Partial.Graph
import Core.Glue
import Core.Groupoid
import Core.Groupoid.Virtual
import Core.IdSys
import Core.Interval
import Core.Prelude
import Core.Type.Exo

import Data.Thin.Base
import Data.Thin.Tri
import Data.Thin.Type
import Data.Tree
import Data.Tree.BinTree
import Data.W

import HData.Join
import HData.Pushout
import HData.Quotient
import HData.Thinning
import HData.Thinning.Properties

import Lib.Relation.Binary
import Lib.Relation.Unary
import Lib.Ternary.Bundles
import Lib.Ternary.Construct.Empty
import Lib.Ternary.Construct.Function
import Lib.Ternary.Construct.Product
import Lib.Ternary.Construct.Unit
import Lib.Ternary.Core
import Lib.Ternary.Respect.Propositional
import Lib.Ternary.Structures
import Lib.Ternary.Structures.Syntax

import Test.Scratch

-- import Cat.Rezk  -- WIP: decode-gen holes at L203/204
-- import Cat.Slice  -- WIP: open holes at L211/262/280
-- import Core.Coherence.Paths  -- WIP: open face holes at L149/152/155/183
-- import Core.Path.Coherence  -- WIP: open cell/hcomp holes at L52/67/94-99
-- import Core.Path.Composition  -- WIP: open test-* holes at L425/453/476
-- import Data.Thin.Category  -- WIP: emb-compose-contr hole at L142
-- import Data.Thin.Separated  -- WIP: UnequalTerms de Bruijn mismatch at L116
-- import Data.Thin.Cover  -- WIP: copU hole at L96
-- import Data.Thin.Properties  -- WIP: law holes at L32/35/39
-- import Cat.Displayed  -- WIP: open holes in compose-contr contraction
-- import Cat.Units  -- WIP: proof error at line 382
-- import Cat.Product  -- WIP: mid-edit, MetaCannotDependOn at L237
-- import HData.Rack  -- WIP: pre-existing unsolved metas at L31-34, unrelated to ternary port
import Cat.Monoidal.Indiscrete
import Cat.Monoidal.Twist
import Cat.Monoidal.Braid
import Cat.Monoidal.Hexagon
import Core.Coherence.Base
```
