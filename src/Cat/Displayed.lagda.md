Lane Biocini
July 2026

A displayed category over a `Cat.Type` category: the representable
presentation, displaced. Everything displaces by taking sections over
the graph of a base operator — the context calculus Σ-by-Σ, and
`composite[ α ] x' y'` as a family of displayed results over the base
contexts, the base context a visible argument exactly as `composite`
keeps its context visible. The axiom scheme displaces over the base's
canonical paths: `interchange♭ᴰ` over `interchange♭ U V`, the
displayed spine over the base spine center's projections, `unitᴰ`
over `unit f`. The displayed axioms therefore open `Cat.Base.theory`,
not merely the record: the spine displaces over derived theory.

Displayed composition `_⨾ᴰ_` is extracted from the contractible
displayed spine, and displayed associativity and the unit laws are
theorems of `Cat.Displayed.Base.theoryᴰ`. This is the contrast with
an Ahrens–Lumsdaine-style presentation, which posits `_∘[_]_` and
then axiomatizes its coherence as PathPs over base coherence: here
both the operation and its coherence are projections of
contractibility.

Instances are moral and checked-against, never routed through:
`monoidal-axioms₁` over `monoidal-axioms₀` transcribes this record at
the squared one-object base — `⊗₁-composite` is `composite[_]` with
the fiber Σ's inlined, `⊗₁-spine` is `spineᴰ` verbatim, `⊗₁-wit` is
`is-representable[_]` at a pair of base witnesses, `⊗₁-interchange♭`
is `interchange♭ᴰ` over it with `⊗₁-interchange` the `⊗₁-wit-nrm`
instance — and `Cat.Type` itself is the instance over the point. The one
`monoidal-axioms₁` field with no counterpart here is `⊗₁-emb-⨾`: its
displayed homs carry an ambient vertical composition, and
functoriality of the embedding for it is enrichment — data beyond
displayed structure.

Naming. Bracket names carry the base index when naming a type family
(`ob[_]`, `hom[_]`, `over[_]`, `ctx[_]`, `res[_]`, `composite[_]`,
`is-representable[_]`) and the principal displayed argument when
naming an operation (`idn[_]`, `emb[_]`, `ev[_]`, `nrm[_]`,
`pre[_]`, `sub[_]`) — the bracket is notation only where an argument
fills it. Everything else takes the `ᴰ` suffix: records, modules,
lemmas, and the displaced infix operators (`_▾ᴰ_`, `_⨾ᴰ_`, `_●ᴰ_`),
whose base mates they shadow glyph for glyph. `_$ᴰ_` applies a
displayed composite with the base context read off the displayed
context's type.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Cat.Displayed where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan

open import Cat.Type
open import Cat.Base
```

## Displayed reflexive graphs

```agda
record reflexive-graphᴰ {u v} (S : reflexive-graph u v)
  (u' v' : Level) : Type₊ (u ⊔ v ⊔ u' ⊔ v') where
  private module S = reflexive-graph S
  field
    ob[_]  : S.ob → Type u'
    hom[_] : ∀ {x y} → S.edge x y → ob[ x ] → ob[ y ] → Type v'
    idn[_] : ∀ {x} (x' : ob[ x ]) → hom[ S.rx x ] x' x'
```

## The displaced context calculus

Each `virtual` combinator displaces Σ-by-Σ, and the displayed
centers sit over the base centers on the nose. `composite[_]`
quantifies its base context visibly, mirroring `composite`: a
hidden-Π-headed family would be eta-expanded with context metas at
every inference-mode position, so the frame stays in the Π and
`_$ᴰ_` recovers implicit application.

```agda
module virtualᴰ {o h o' h'} {S : reflexive-graph o h}
  (Dᴿ : reflexive-graphᴰ S o' h') where

  open virtual S
  open reflexive-graphᴰ Dᴿ public

  over[_] : ∀ {x} → over x → ob[ x ] → Type (o' ⊔ h')
  over[ ω ] x' = Σ w' ∶ ob[ ω .fst ] , hom[ ω .snd ] w' x'

  ov-ctr[_] : ∀ {x y} {f : hom x y} {x' y'}
            → hom[ f ] x' y' → over[ ov-ctr f ] y'
  ov-ctr[_] {x' = x'} f' = x' , f'

  ov-idn[_] : ∀ {x} (x' : ob[ x ]) → over[ ov-idn x ] x'
  ov-idn[ x' ] = x' , idn[ x' ]

  under[_] : ∀ {y} → under y → ob[ y ] → Type (o' ⊔ h')
  under[ υ ] y' = Σ v' ∶ ob[ υ .fst ] , hom[ υ .snd ] y' v'

  un-ctr[_] : ∀ {x y} {f : hom x y} {x' y'}
            → hom[ f ] x' y' → under[ un-ctr f ] x'
  un-ctr[_] {y' = y'} f' = y' , f'

  un-idn[_] : ∀ {y} (y' : ob[ y ]) → under[ un-idn y ] y'
  un-idn[ y' ] = y' , idn[ y' ]

  ctx[_] : ∀ {x y} → ctx x y → ob[ x ] → ob[ y ] → Type (o' ⊔ h')
  ctx[ γ ] x' y' = over[ γ .fst ] x' × under[ γ .snd ] y'

  emp[_] : ∀ {w x y z} {a : hom w x} {b : hom y z} {w' x' y' z'}
         → hom[ a ] w' x' → hom[ b ] y' z' → ctx[ emp a b ] x' y'
  emp[ a' ] b' = ov-ctr[ a' ] , un-ctr[ b' ]

  res[_] : ∀ {x y} {γ : ctx x y} {x' y'}
         → res γ → ctx[ γ ] x' y' → Type h'
  res[ s ] γ' = hom[ s ] (γ' .fst .fst) (γ' .snd .fst)

  composite[_] : ∀ {x y} → composite x y → ob[ x ] → ob[ y ]
               → Type (o ⊔ h ⊔ o' ⊔ h')
  composite[ α ] x' y' = ∀ γ (γ' : ctx[ γ ] x' y') → res[ α γ ] γ'

  -- application, with the base context read off the displayed
  -- context's type
  _$ᴰ_ : ∀ {x y} {α : composite x y} {x' y'}
        → composite[ α ] x' y'
        → ∀ {γ} (γ' : ctx[ γ ] x' y') → res[ α γ ] γ'
  _$ᴰ_ α' {γ} γ' = α' γ γ'
  infixl 90 _$ᴰ_

  ev[_] : ∀ {x y} {α : composite x y} {x' y'}
        → composite[ α ] x' y' → hom[ ev α ] x' y'
  ev[_] {x} {y} {x' = x'} {y'} α' =
    α' (ov-idn x , un-idn y) (ov-idn[ x' ] , un-idn[ y' ])
```

## The displaced representable layer

Displaced representability is the fiber of `emb[_]` over a chosen
base representability witness: over `U = (m , p)`, a displayed
witness is a lift of `m` together with a PathP over `p`. The
operator calculus displaces token-for-token; the `res[_]`
computations that make each clause typecheck are the same
definitional computations as in the base, so `_▾ᴰ_` collapses to
`_▿ᴰ_` against an embedded factor exactly as `_▾_` does to `_▿_`.
The displaced closure `interchange♭-fromᴰ` — instance sugar, a
double dependent J over the total fibers — is deferred with the
J-straightening cluster; the axiom field below takes the ♭ form
directly, so nothing routes through it.

```agda
module representableᴰ {o h o' h'}
  {S : reflexive-graph o h}
  (emb : ∀ {x y} → reflexive-graph.edge S x y → virtual.composite S x y)
  (Dᴿ : reflexive-graphᴰ S o' h')
  (let private module S' = reflexive-graph S
       private module Vᴰ = virtualᴰ Dᴿ)
  (emb[_] : ∀ {x y} {f : S'.edge x y} {x' y'}
          → Vᴰ.hom[ f ] x' y' → Vᴰ.composite[ emb f ] x' y')
  where

  open virtual S
  open virtualᴰ Dᴿ
  open representable S emb

  is-representable[_]
    : ∀ {x y} {α : composite x y} {x' y'}
    → is-representable α → composite[ α ] x' y'
    → Type (o ⊔ h ⊔ o' ⊔ h')
  is-representable[_] {x' = x'} {y'} (m , p) α' =
    Σ m' ∶ hom[ m ] x' y' ,
      PathP (λ i → composite[ p i ] x' y') (emb[ m' ]) α'

  nrm[_] : ∀ {x y} {f : hom x y} {x' y'} (f' : hom[ f ] x' y')
         → is-representable[ nrm f ] (emb[ f' ])
  nrm[ f' ] = f' , refl

  pre[_] : ∀ {y z} {g : hom y z} {y' z'} (g' : hom[ g ] y' z')
         → ∀ {v} {b : hom z v} {v'}
         → hom[ b ] z' v' → hom[ pre g b ] y' v'
  pre[ g' ] b' = emb[ g' ] $ᴰ (ov-idn[ _ ] , un-ctr[ b' ])

  post[_] : ∀ {x y} {f : hom x y} {x' y'} (f' : hom[ f ] x' y')
          → ∀ {w} {a : hom w x} {w'}
          → hom[ a ] w' x' → hom[ post f a ] w' y'
  post[ f' ] a' = emb[ f' ] $ᴰ (ov-ctr[ a' ] , un-idn[ _ ])

  sub[_] : ∀ {x y z} {g : hom y z} {y' z'} (g' : hom[ g ] y' z')
         → ∀ {γ : ctx x z} {x'}
         → ctx[ γ ] x' z' → ctx[ sub g γ ] x' y'
  sub[ g' ] (c' , (v' , b')) = c' , (v' , pre[ g' ] b')

  cosub[_] : ∀ {x y z} {g : hom x y} {x' y'} (g' : hom[ g ] x' y')
           → ∀ {γ : ctx x z} {z'}
           → ctx[ γ ] x' z' → ctx[ cosub g γ ] y' z'
  cosub[ g' ] ((w' , a') , υ') = (w' , post[ g' ] a') , υ'

  _▾ᴰ_ : ∀ {x y z} {α : composite x y} {g : hom y z} {x' y' z'}
        → composite[ α ] x' y' → hom[ g ] y' z'
        → composite[ α ▾ g ] x' z'
  _▾ᴰ_ {g = g} α' g' γ γ' = α' (sub g γ) (sub[ g' ] γ')
  infixl 30 _▾ᴰ_

  _▴ᴰ_ : ∀ {x y z} {f : hom x y} {β : composite y z} {x' y' z'}
        → hom[ f ] x' y' → composite[ β ] y' z'
        → composite[ f ▴ β ] x' z'
  _▴ᴰ_ {f = f} f' β' γ γ' = β' (cosub f γ) (cosub[ f' ] γ')
  infixl 30 _▴ᴰ_

  _▿ᴰ_ : ∀ {x y z} {A : composite x y} {B : composite y z} {x' y' z'}
        → composite[ A ] x' y' → composite[ B ] y' z'
        → composite[ A ▿ B ] x' z'
  _▿ᴰ_ {y = y} {B = B} {y' = y'} α' β' γ γ' =
    α' (γ .fst , (γ .snd .fst , B (ov-idn y , γ .snd)))
       (γ' .fst , (γ' .snd .fst ,
         β' (ov-idn y , γ .snd) (ov-idn[ y' ] , γ' .snd)))
  infixl 30 _▿ᴰ_

  _▵ᴰ_ : ∀ {x y z} {A : composite x y} {B : composite y z} {x' y' z'}
        → composite[ A ] x' y' → composite[ B ] y' z'
        → composite[ A ▵ B ] x' z'
  _▵ᴰ_ {y = y} {A = A} {y' = y'} α' β' γ γ' =
    β' ((γ .fst .fst , A (γ .fst , un-idn y)) , γ .snd)
       ((γ' .fst .fst ,
         α' (γ .fst , un-idn y) (γ' .fst , un-idn[ y' ])) , γ' .snd)
  infixl 30 _▵ᴰ_
```

## `category-axiomsᴰ`

The displayed axiom record, over a base *category* rather than a
bare graph: the displayed spine displaces over `f ⨾ g` and the base
spine center's projections, so `Cat.Base.theory` is in scope — the
same layering `monoidal-axioms₁` exhibits over `monoidal-axioms₀`'s
spine projections. The record takes the ♭ form of interchange
faithfully, over displayed representables; `interchangeᴰ` is its
`nrm[_]` instance, exactly as `interchange` is at the base.

```agda
record category-axiomsᴰ {o h o' h'} (C : category o h)
  (Dᴿ : reflexive-graphᴰ (C .category.structure) o' h')
  : Type (o ⊔ h ⊔ o' ⊔ h') where

  open category C
  open theory C
  open virtualᴰ Dᴿ

  field
    emb[_] : ∀ {x y} {f : hom x y} {x' y'}
           → hom[ f ] x' y' → composite[ emb f ] x' y'

  open representableᴰ emb Dᴿ emb[_] public

  field
    interchange♭ᴰ
      : ∀ {x y z} {A : composite x y} {B : composite y z} {x' y' z'}
          {U : is-representable A} {V : is-representable B}
          {A' : composite[ A ] x' y'} {B' : composite[ B ] y' z'}
      → is-representable[ U ] A' → is-representable[ V ] B'
      → PathP (λ i → composite[ interchange♭ U V i ] x' z')
              (A' ▿ᴰ B') (A' ▵ᴰ B')

  interchangeᴰ
    : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
      (f' : hom[ f ] x' y') (g' : hom[ g ] y' z')
    → PathP (λ i → composite[ interchange f g i ] x' z')
            (emb[ f' ] ▾ᴰ g') (f' ▴ᴰ emb[ g' ])
  interchangeᴰ f' g' = interchange♭ᴰ nrm[ f' ] nrm[ g' ]

  spineᴰ : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
         → hom[ f ] x' y' → hom[ g ] y' z' → Type (o ⊔ h ⊔ o' ⊔ h')
  spineᴰ {f = f} {g} {x'} {y'} {z'} f' g' =
    Σ k' ∶ hom[ f ⨾ g ] x' z' ,
    Σ P ∶ PathP (λ i → composite[ emb-comp f g i ] x' z')
                (emb[ k' ]) (emb[ f' ] ▾ᴰ g') ,
    Σ Q ∶ PathP (λ i → composite[ emb-comp-op f g i ] x' z')
                (emb[ k' ]) (f' ▴ᴰ emb[ g' ]) ,
      PathP (λ i → PathP (λ j → composite[ emb-comp-coh f g i j ] x' z')
                         (emb[ k' ]) (interchangeᴰ f' g' i))
            P Q

  field
    spineᴰ-contr
      : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
        (f' : hom[ f ] x' y') (g' : hom[ g ] y' z')
      → is-contr (spineᴰ f' g')

    unitᴰ
      : ∀ {x y} {f : hom x y} {x' y'} (f' : hom[ f ] x' y')
      → PathP (λ i → hom[ unit f i ] x' y') (ev[ emb[ f' ] ]) f'

  _⨾ᴰ_ : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
        → hom[ f ] x' y' → hom[ g ] y' z' → hom[ f ⨾ g ] x' z'
  f' ⨾ᴰ g' = spineᴰ-contr f' g' .center .fst
  infixr 40 _⨾ᴰ_

  emb-compᴰ
    : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
      (f' : hom[ f ] x' y') (g' : hom[ g ] y' z')
    → PathP (λ i → composite[ emb-comp f g i ] x' z')
            (emb[ f' ⨾ᴰ g' ]) (emb[ f' ] ▾ᴰ g')
  emb-compᴰ f' g' = spineᴰ-contr f' g' .center .snd .fst

  emb-comp-opᴰ
    : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
      (f' : hom[ f ] x' y') (g' : hom[ g ] y' z')
    → PathP (λ i → composite[ emb-comp-op f g i ] x' z')
            (emb[ f' ⨾ᴰ g' ]) (f' ▴ᴰ emb[ g' ])
  emb-comp-opᴰ f' g' = spineᴰ-contr f' g' .center .snd .snd .fst

  -- the displayed spine's 2-cell
  emb-comp-cohᴰ
    : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
      (f' : hom[ f ] x' y') (g' : hom[ g ] y' z')
    → PathP (λ i → PathP (λ j → composite[ emb-comp-coh f g i j ] x' z')
                         (emb[ f' ⨾ᴰ g' ]) (interchangeᴰ f' g' i))
            (emb-compᴰ f' g') (emb-comp-opᴰ f' g')
  emb-comp-cohᴰ f' g' = spineᴰ-contr f' g' .center .snd .snd .snd
```

## The bundle

```agda
record categoryᴰ {o h} (C : category o h) (o' h' : Level)
  : Type₊ (o ⊔ h ⊔ o' ⊔ h') where
  field
    structureᴰ : reflexive-graphᴰ (C .category.structure) o' h'
    axiomsᴰ    : category-axiomsᴰ C structureᴰ

  open virtualᴰ structureᴰ public
  open category-axiomsᴰ axiomsᴰ public
```
