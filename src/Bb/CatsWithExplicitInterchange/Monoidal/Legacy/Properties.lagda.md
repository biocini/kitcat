Lane Biocini
July 2026

Presentation-comparison material for the monoidal axioms, at both
grades. The records' interchange fields are the ♭ forms and
instances prove them in that shape; the pointwise-to-♭ closures
below are the nontrivial directions of the comparison between the
two possible presentations of each axiom — J-towers over the
fibers of the embeddings, agreeing with their inputs at normal
forms only propositionally (the J lottery that ruled the fields).
Nothing on the spine routes through them: they live here as the
material a presentation-equivalence theorem would consume.

The swap-half comparison delivers the first such theorem: the
braided `-l` hexagon field against the swap-half presentation of
the same coherence, as a genuine two-sided equivalence of
statement types at both grades. It is the consumer of
`⊗₀/⊗₁-interchange-natural` and the `ι-mult` hypotheses, consumed
nowhere on the spine since the full-braid field ruling.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Properties where

open import Core.Type
open import Core.Base hiding (I)
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base using (ap-merge; comp-pathp₂-merge-map)
open import Core.Transport.Base using (transport; transport-filler)
open import Core.Transport.Properties using (transport-equiv)
open import Core.Equiv.Base using (_≃_)
open import Core.Transport.J using (J)

open import Bb.CatsWithExplicitInterchange.Type
open import Bb.CatsWithExplicitInterchange.Monoidal.Legacy
open import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Bifunctor
open import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Coherence
open import Bb.CatsWithExplicitInterchange.Monoidal.Legacy.Braid
```

## The object grade

```agda
module _ {o h} (C : category o h) (I : category.ob C)
  (⊗₀-emb : category.ob C → tensor-virtual.⊗₀-composite C I)
  where

  open tensor-virtual C I
  open tensor-representable C I ⊗₀-emb
  private module C = category C

  ⊗₀-interchange♭-from
    : ((x y : C.ob) → ⊗₀-emb x ▾₀ y ≡ x ▴₀ ⊗₀-emb y)
    → {A B : ⊗₀-composite}
    → is-⊗₀-representable A → is-⊗₀-representable B
    → A ▿₀ B ≡ A ▵₀ B
  ⊗₀-interchange♭-from ι {B = B} (m , p) (n , q) =
    J (λ F' _ → F' ▿₀ B ≡ F' ▵₀ B)
      (J (λ G' _ → ⊗₀-emb m ▿₀ G' ≡ ⊗₀-emb m ▵₀ G') (ι m n) q)
      p
```

## The morphism grade

One dependent J per side, each over the witness's total path —
the base lines paired with the characterization, re-bent as a
single path in the graph Σ of `⊗₁-composite`.

```agda
module _ {o h} (C : category o h) (I : category.ob C)
  (⊗₀-emb : category.ob C → tensor-virtual.⊗₀-composite C I)
  (⊗₁-emb : ∀ {x x'} → category.hom C x x'
          → tensor-virtual₁.⊗₁-composite C I (⊗₀-emb x) (⊗₀-emb x'))
  where

  open tensor-virtual C I
  open tensor-virtual₁ C I
  open tensor-representable C I ⊗₀-emb
  open tensor-representable₁ C I ⊗₀-emb ⊗₁-emb
  private module C = category C

  ⊗₁-interchange♭-from
    : (ι : ∀ {A B : ⊗₀-composite}
         → is-⊗₀-representable A → is-⊗₀-representable B
         → A ▿₀ B ≡ A ▵₀ B)
    → (∀ {x x'} (φ : C.hom x x') {y y'} (ψ : C.hom y y')
       → PathP (λ i → ⊗₁-composite (ι (⊗₀-nrm x) (⊗₀-nrm y) i)
                                    (ι (⊗₀-nrm x') (⊗₀-nrm y') i))
               (⊗₁-emb φ ▾₁ ψ) (φ ▴₁ ⊗₁-emb ψ))
    → ∀ {A A' B B' : ⊗₀-composite}
        {U : is-⊗₀-representable A} {U' : is-⊗₀-representable A'}
        {V : is-⊗₀-representable B} {V' : is-⊗₀-representable B'}
        {η : ⊗₁-composite A A'} {ζ : ⊗₁-composite B B'}
    → ⊗₁-wit U U' η → ⊗₁-wit V V' ζ
    → PathP (λ i → ⊗₁-composite (ι U V i) (ι U' V' i))
            (η ▿₁ ζ) (η ▵₁ ζ)
  ⊗₁-interchange♭-from ι ι₁
    {U = m , p} {m' , p'} {n , q} {n' , q'} {ζ = ζ} (σ , P) (τ , Q) =
    J {A = Σ T ∶ ⊗₀-composite × ⊗₀-composite , ⊗₁-composite (T .fst) (T .snd)}
      (λ T t →
        PathP (λ i → ⊗₁-composite (ι (m , λ j → t j .fst .fst) (n , q) i)
                                   (ι (m' , λ j → t j .fst .snd) (n' , q') i))
              (T .snd ▿₁ ζ) (T .snd ▵₁ ζ))
      (J {A = Σ T ∶ ⊗₀-composite × ⊗₀-composite , ⊗₁-composite (T .fst) (T .snd)}
         (λ T t →
           PathP (λ i → ⊗₁-composite (ι (⊗₀-nrm m) (n , λ j → t j .fst .fst) i)
                                      (ι (⊗₀-nrm m') (n' , λ j → t j .fst .snd) i))
                 (⊗₁-emb σ ▿₁ T .snd) (⊗₁-emb σ ▵₁ T .snd))
         (ι₁ σ τ)
         (λ i → (q i , q' i) , Q i))
      (λ i → (p i , p' i) , P i)
```

## The swap-half presentation of the -l hexagon

The `-l` hexagon's subject is the braid of a pairing,
`⊗₀-braid♭ (U ●₀ V) W`, and the field identifies it with the two
whiskered single braids. Splitting the braid into its interchange
and flank-swap halves, the same coherence has a second
presentation stated on the flank swap alone: the swap-half's
subject `(F ▿₀ G) ▵₀ H` has no strict redistribution into
single-factor flanks — a `▿₀`-block in a `▵₀`-flank moves only
along interchange lines — so the block enters flank position
along its own interchange, and the two single swaps then fire in
their native slots, the strict mixed associativities gluing the
seams. `decomp` names that composite; the swap-half statement
identifies `⊗₀-flank-swap♭ (U ●₀ V) W` with it.

```agda
module _ {o h} {C : category o h} {M : monoidal C} (B : braided M) where
  open monoidal M
  open theory₁ M
  open coherence M
  open braided B
  open braid-theory B
  private module C = category C

  module swap-half₀ {F G H : ⊗₀-composite}
    (U : is-⊗₀-representable F) (V : is-⊗₀-representable G)
    (W : is-⊗₀-representable H)
    where

    -- the interchange conjugators the comparison routes through:
    -- the pairing's own (at both pairings), and U against the
    -- right pairing, its braid transport, and the swapped pairing
    ιc : F ▿₀ G ▿₀ H ≡ (F ▿₀ G) ▵₀ H
    ιc = ⊗₀-interchange♭ (U ●₀ V) W

    ιo : (F ▵₀ G) ▿₀ H ≡ (F ▵₀ G) ▵₀ H
    ιo = ⊗₀-interchange♭ (U ○₀ V) W

    ιr : F ▿₀ G ▿₀ H ≡ F ▵₀ (G ▿₀ H)
    ιr = ⊗₀-interchange♭ U (V ●₀ W)

    ιt : F ▿₀ H ▿₀ G ≡ F ▵₀ (H ▿₀ G)
    ιt = ⊗₀-interchange♭ U ((V ●₀ W) ↝ ⊗₀-braid♭ V W)

    ιw : F ▿₀ H ▿₀ G ≡ F ▵₀ (H ▿₀ G)
    ιw = ⊗₀-interchange♭ U (W ●₀ V)

    -- the whiskered legs, named once: every chain and every
    -- displaced ascription rides them by name
    bvw▿ : F ▿₀ G ▿₀ H ≡ F ▿₀ H ▿₀ G
    bvw▿ = ap (λ X → F ▿₀ X) (⊗₀-braid♭ V W)

    bvw▵ : F ▵₀ (G ▿₀ H) ≡ F ▵₀ (H ▿₀ G)
    bvw▵ = ap (λ X → F ▵₀ X) (⊗₀-braid♭ V W)

    buw▿ : F ▿₀ H ▿₀ G ≡ H ▿₀ F ▿₀ G
    buw▿ = ap (λ X → X ▿₀ G) (⊗₀-braid♭ U W)

    ιuw▿ : F ▿₀ H ▿₀ G ≡ F ▵₀ (H ▿₀ G)
    ιuw▿ = ap (λ X → X ▿₀ G) (⊗₀-interchange♭ U W)

    suw▿ : F ▵₀ (H ▿₀ G) ≡ H ▿₀ F ▿₀ G
    suw▿ = ap (λ X → X ▿₀ G) (⊗₀-flank-swap♭ U W)

    ιvw▵ : F ▵₀ (G ▿₀ H) ≡ F ▵₀ (G ▵₀ H)
    ιvw▵ = ap (λ X → F ▵₀ X) (⊗₀-interchange♭ V W)

    svw▵ : F ▵₀ (G ▵₀ H) ≡ F ▵₀ (H ▿₀ G)
    svw▵ = ap (λ X → F ▵₀ X) (⊗₀-flank-swap♭ V W)

    ιuv▿ : F ▿₀ G ▿₀ H ≡ (F ▵₀ G) ▿₀ H
    ιuv▿ = ap (λ X → X ▿₀ H) (⊗₀-interchange♭ U V)

    ιuv▵ : (F ▿₀ G) ▵₀ H ≡ (F ▵₀ G) ▵₀ H
    ιuv▵ = ap (λ X → X ▵₀ H) (⊗₀-interchange♭ U V)
```

The two stated composites: the field's right-hand side, and the
swap-half decomposition — one interchange conjugator moving the
block into flank position, then the two single flank swaps.

```agda
    swapc : (F ▿₀ G) ▵₀ H ≡ H ▿₀ F ▿₀ G
    swapc = ⊗₀-flank-swap♭ (U ●₀ V) W

    two-step : F ▿₀ G ▿₀ H ≡ H ▿₀ F ▿₀ G
    two-step = bvw▿ ∙ buw▿

    decomp : (F ▿₀ G) ▵₀ H ≡ H ▿₀ F ▿₀ G
    decomp = ιuv▵ ∙ svw▵ ∙ suw▿
```

The braid deformation-retracts onto its swap half along its own
interchange: `cat.rfill` transposed and reversed is a line of
paths over `ιc` from the braid to the flank swap, every face
definitional. The same filler at `decomp` seats the other end of
the comparison.

```agda
    braid-fill : PathP (λ j → ιc j ≡ H ▿₀ F ▿₀ G)
                 (⊗₀-braid♭ (U ●₀ V) W) swapc
    braid-fill j i = cat.rfill ιc swapc i (~ j)

    decomp-fill : PathP (λ j → ιc j ≡ H ▿₀ F ▿₀ G) (ιc ∙ decomp) decomp
    decomp-fill j i = cat.rfill ιc decomp i (~ j)
```

The bridge: the field's right-hand side rewritten into
`ιc ∙ decomp` by an eight-link chain. The merges are `ap-merge`
at the two braid splittings; `cast` recasts the whiskered
interchange as the interchange at the swapped pairing through the
`ι-mult` hypothesis and the sealed braid σ-line; `ι-slide` is the
free naturality of the interchange along the braid line — the
`↝-fill` slide of the pairing read through `Path.commutes`; `mult`
consumes the two remaining `ι-mult` hypotheses; `natural` is
`⊗₀-interchange-natural`; the flattens reassociate onto the
stated composite.

```agda
    module compare
      (mr : ι-mult-r₀ U V W) (ml : ι-mult-l₀ U V W)
      (mw : ι-mult-r₀ U W V)
      where

      σ-leg : ιw ≡ ιt
      σ-leg i = ⊗₀-interchange♭ U (braid-σ●₀ V W (~ i))

      cast-arg : ιuw▿ ≡ ιt
      cast-arg = mw ∙ σ-leg

      slide-sq : Square bvw▿ ιr bvw▵ ιt
      slide-sq j m = ⊗₀-interchange♭ U (↝-fill (V ●₀ W) (⊗₀-braid♭ V W) m) j

      ι-slide : bvw▿ ∙ ιt ≡ ιr ∙ bvw▵
      ι-slide = Path.commutes bvw▿ ιt ιr bvw▵ slide-sq

      mult-arg : ιr ∙ ιvw▵ ≡ ιuv▿ ∙ ιo
      mult-arg i = mr (~ i) ∙ ml i

      -- stations of the chain, F ▿₀ G ▿₀ H ≡ H ▿₀ F ▿₀ G throughout
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ : F ▿₀ G ▿₀ H ≡ H ▿₀ F ▿₀ G
      c₁ = (bvw▿ ∙ ιuw▿) ∙ suw▿
      c₂ = (bvw▿ ∙ ιt) ∙ suw▿
      c₃ = (ιr ∙ bvw▵) ∙ suw▿
      c₄ = ((ιr ∙ ιvw▵) ∙ svw▵) ∙ suw▿
      c₅ = ((ιuv▿ ∙ ιo) ∙ svw▵) ∙ suw▿
      c₆ = ((ιc ∙ ιuv▵) ∙ svw▵) ∙ suw▿
      c₇ = (ιc ∙ ιuv▵) ∙ (svw▵ ∙ suw▿)

      merge-r : two-step ≡ c₁
      merge-r =
        sym (ap-merge (λ X → X ▿₀ G) bvw▿
              (⊗₀-interchange♭ U W) (⊗₀-flank-swap♭ U W))

      cast : c₁ ≡ c₂
      cast = ap (λ t → (bvw▿ ∙ t) ∙ suw▿) cast-arg

      commute : c₂ ≡ c₃
      commute = ap (_∙ suw▿) ι-slide

      merge-l : c₃ ≡ c₄
      merge-l =
        ap (_∙ suw▿)
           (sym (ap-merge (λ X → F ▵₀ X) ιr
                  (⊗₀-interchange♭ V W) (⊗₀-flank-swap♭ V W)))

      mult : c₄ ≡ c₅
      mult = ap (λ t → (t ∙ svw▵) ∙ suw▿) mult-arg

      natural : c₅ ≡ c₆
      natural = ap (λ t → (t ∙ svw▵) ∙ suw▿) (⊗₀-interchange-natural U V W)

      flatten₁ : c₆ ≡ c₇
      flatten₁ = sym (Path.assoc (ιc ∙ ιuv▵) svw▵ suw▿)

      flatten₂ : c₇ ≡ ιc ∙ decomp
      flatten₂ = sym (Path.assoc ιc ιuv▵ (svw▵ ∙ suw▿))

      bridge : two-step ≡ ιc ∙ decomp
      bridge =
        merge-r ∙ cast ∙ commute ∙ merge-l ∙ mult ∙ natural
        ∙ flatten₁ ∙ flatten₂
```

The bridge pasted into fill form: the tube prepends the bridge to
`decomp-fill` inside the one path space, and its lid is the line
of paths over `ιc` from the field's right-hand side to the
decomposition.

```agda
      bridge-tube : (j k : Core.Base.I) → ιc j ≡ H ▿₀ F ▿₀ G
      bridge-tube j k = hfil (∂ j) k λ where
        l (j = i0) → bridge (~ l)
        l (j = i1) → decomp
        l (l = i0) → decomp-fill j

      bridge-fill : PathP (λ j → ιc j ≡ H ▿₀ F ▿₀ G) two-step decomp
      bridge-fill j = bridge-tube j i1
```

The equivalence: `braid-fill` against `bridge-fill` is a line of
statement types from the field form to the swap-half form, and
transport along it is an equivalence — both directions and the
round-trips in one move.

```agda
      stmt-line
        : (⊗₀-braid♭ (U ●₀ V) W ≡ two-step)
        ≡ (⊗₀-flank-swap♭ (U ●₀ V) W ≡ decomp)
      stmt-line j = braid-fill j ≡ bridge-fill j

      hexagon-l≃swap-half
        : (⊗₀-braid♭ (U ●₀ V) W ≡ two-step)
        ≃ (⊗₀-flank-swap♭ (U ●₀ V) W ≡ decomp)
      hexagon-l≃swap-half = transport stmt-line , transport-equiv stmt-line
```

## The displaced comparison

The same construction one level up, slot for slot. The level-0
cells alias by name, the whiskered legs displace to `▿₁`/`▵₁`
whiskers of the field cells, and every chain link carries one
displaced cell over it: the merges are `comp-pathp₂-merge-map`
(the whisker-of-glue ends it reconciles are exactly the braid
whiskers the record's field states), `cast` glues the level-1
`ι-mult` hypothesis to the interchange field at the
`braid-σ●₁` line, `ι-slide` is `comp-pathp₂-commutes` at the
`↝̂-fill` slide — the cap and com ends make its walls
definitional — `mult` glues the two hypothesis squares, `natural`
is `⊗₁-interchange-natural`, and the flattens are reversed
`comp-pathp₂-assoc`. The fillers displace to
`comp-pathp₂-rfill`, the prepend to one `com` along the level-0
tube, and the equivalence is transport along the line of
displaced statement types, threaded over the `transport-filler`
of the level-0 line at a given pair of object-grade proofs.

```agda
  module swap-half₁
    {F F' G G' H H' : ⊗₀-composite}
    {U : is-⊗₀-representable F} {U' : is-⊗₀-representable F'}
    {V : is-⊗₀-representable G} {V' : is-⊗₀-representable G'}
    {W : is-⊗₀-representable H} {W' : is-⊗₀-representable H'}
    {η : ⊗₁-composite F F'} {ζ : ⊗₁-composite G G'}
    {θ : ⊗₁-composite H H'}
    (Û : ⊗₁-wit U U' η) (V̂ : ⊗₁-wit V V' ζ) (Ŵ : ⊗₁-wit W W' θ)
    (mr : ι-mult-r₀ U V W) (mr' : ι-mult-r₀ U' V' W')
    (ml : ι-mult-l₀ U V W) (ml' : ι-mult-l₀ U' V' W')
    (mw : ι-mult-r₀ U W V) (mw' : ι-mult-r₀ U' W' V')
    (m̂r : ι-mult-r₁ mr mr' Û V̂ Ŵ)
    (m̂l : ι-mult-l₁ ml ml' Û V̂ Ŵ)
    (m̂w : ι-mult-r₁ mw mw' Û Ŵ V̂)
    where

    private
      module Q  = swap-half₀ U V W
      module Q' = swap-half₀ U' V' W'
      module Qc  = Q.compare mr ml mw
      module Qc' = Q'.compare mr' ml' mw'

    N₀ : ⊗₁-composite (F ▿₀ G ▿₀ H) (F' ▿₀ G' ▿₀ H')
    N₀ = η ▿₁ ζ ▿₁ θ

    N₁ : ⊗₁-composite (H ▿₀ F ▿₀ G) (H' ▿₀ F' ▿₀ G')
    N₁ = θ ▿₁ η ▿₁ ζ

    private
      Famc : F ▿₀ G ▿₀ H ≡ H ▿₀ F ▿₀ G
           → F' ▿₀ G' ▿₀ H' ≡ H' ▿₀ F' ▿₀ G'
           → Type (o ⊔ h)
      Famc p p' = PathP (λ i → ⊗₁-composite (p i) (p' i)) N₀ N₁
```

The displaced conjugators and legs, over exactly the level-0
lines.

```agda
    ι̂c : PathP (λ i → ⊗₁-composite (Q.ιc i) (Q'.ιc i)) N₀ (η ▿₁ ζ ▵₁ θ)
    ι̂c = ⊗₁-interchange♭ (Û ●₁ V̂) Ŵ

    ι̂o : PathP (λ i → ⊗₁-composite (Q.ιo i) (Q'.ιo i))
               (η ▵₁ ζ ▿₁ θ) (η ▵₁ ζ ▵₁ θ)
    ι̂o = ⊗₁-interchange♭ (Û ○₁ V̂) Ŵ

    ι̂r : PathP (λ i → ⊗₁-composite (Q.ιr i) (Q'.ιr i)) N₀ (η ▵₁ ζ ▿₁ θ)
    ι̂r = ⊗₁-interchange♭ Û (V̂ ●₁ Ŵ)

    ι̂t : PathP (λ i → ⊗₁-composite (Q.ιt i) (Q'.ιt i))
               (η ▿₁ θ ▿₁ ζ) (η ▵₁ θ ▿₁ ζ)
    ι̂t = ⊗₁-interchange♭ Û ((V̂ ●₁ Ŵ) ↝̂ ⊗₁-braid♭ V̂ Ŵ)

    ι̂w : PathP (λ i → ⊗₁-composite (Q.ιw i) (Q'.ιw i))
               (η ▿₁ θ ▿₁ ζ) (η ▵₁ θ ▿₁ ζ)
    ι̂w = ⊗₁-interchange♭ Û (Ŵ ●₁ V̂)

    ŝc : PathP (λ i → ⊗₁-composite (Q.swapc i) (Q'.swapc i))
               (η ▿₁ ζ ▵₁ θ) N₁
    ŝc = ⊗₁-flank-swap♭ (Û ●₁ V̂) Ŵ

    b̂vw▿ : PathP (λ i → ⊗₁-composite (Q.bvw▿ i) (Q'.bvw▿ i)) N₀ (η ▿₁ θ ▿₁ ζ)
    b̂vw▿ i = η ▿₁ ⊗₁-braid♭ V̂ Ŵ i

    b̂vw▵ : PathP (λ i → ⊗₁-composite (Q.bvw▵ i) (Q'.bvw▵ i))
                 (η ▵₁ ζ ▿₁ θ) (η ▵₁ θ ▿₁ ζ)
    b̂vw▵ i = η ▵₁ ⊗₁-braid♭ V̂ Ŵ i

    b̂uw▿ : PathP (λ i → ⊗₁-composite (Q.buw▿ i) (Q'.buw▿ i)) (η ▿₁ θ ▿₁ ζ) N₁
    b̂uw▿ i = ⊗₁-braid♭ Û Ŵ i ▿₁ ζ

    ι̂uw▿ : PathP (λ i → ⊗₁-composite (Q.ιuw▿ i) (Q'.ιuw▿ i))
                 (η ▿₁ θ ▿₁ ζ) (η ▵₁ θ ▿₁ ζ)
    ι̂uw▿ i = ⊗₁-interchange♭ Û Ŵ i ▿₁ ζ

    ŝuw▿ : PathP (λ i → ⊗₁-composite (Q.suw▿ i) (Q'.suw▿ i))
                 (η ▵₁ θ ▿₁ ζ) N₁
    ŝuw▿ i = ⊗₁-flank-swap♭ Û Ŵ i ▿₁ ζ

    ι̂vw▵ : PathP (λ i → ⊗₁-composite (Q.ιvw▵ i) (Q'.ιvw▵ i))
                 (η ▵₁ ζ ▿₁ θ) (η ▵₁ ζ ▵₁ θ)
    ι̂vw▵ i = η ▵₁ ⊗₁-interchange♭ V̂ Ŵ i

    ŝvw▵ : PathP (λ i → ⊗₁-composite (Q.svw▵ i) (Q'.svw▵ i))
                 (η ▵₁ ζ ▵₁ θ) (η ▵₁ θ ▿₁ ζ)
    ŝvw▵ i = η ▵₁ ⊗₁-flank-swap♭ V̂ Ŵ i

    ι̂uv▿ : PathP (λ i → ⊗₁-composite (Q.ιuv▿ i) (Q'.ιuv▿ i))
                 N₀ (η ▵₁ ζ ▿₁ θ)
    ι̂uv▿ i = ⊗₁-interchange♭ Û V̂ i ▿₁ θ

    ι̂uv▵ : PathP (λ i → ⊗₁-composite (Q.ιuv▵ i) (Q'.ιuv▵ i))
                 (η ▿₁ ζ ▵₁ θ) (η ▵₁ ζ ▵₁ θ)
    ι̂uv▵ i = ⊗₁-interchange♭ Û V̂ i ▵₁ θ
```

The stated displaced composites, gluing the legs by
`comp-pathp₂` along exactly the level-0 trees — `two-step̂` is
the `⊗₁-hexagon-l♭` field's right-hand side.

```agda
    t̂ail : PathP (λ i → ⊗₁-composite ((Q.svw▵ ∙ Q.suw▿) i) ((Q'.svw▵ ∙ Q'.suw▿) i))
                 (η ▵₁ ζ ▵₁ θ) N₁
    t̂ail = comp-pathp₂ ⊗₁-composite Q.svw▵ Q.suw▿ Q'.svw▵ Q'.suw▿ ŝvw▵ ŝuw▿

    decomp̂ : PathP (λ i → ⊗₁-composite (Q.decomp i) (Q'.decomp i))
                   (η ▿₁ ζ ▵₁ θ) N₁
    decomp̂ =
      comp-pathp₂ ⊗₁-composite
        Q.ιuv▵ (Q.svw▵ ∙ Q.suw▿) Q'.ιuv▵ (Q'.svw▵ ∙ Q'.suw▿)
        ι̂uv▵ t̂ail

    two-step̂ : Famc Q.two-step Q'.two-step
    two-step̂ = comp-pathp₂ ⊗₁-composite Q.bvw▿ Q.buw▿ Q'.bvw▿ Q'.buw▿ b̂vw▿ b̂uw▿
```

The displaced chain: the argument cells first — the σ-line slide
of the interchange field, the hypothesis glue behind `cast`, and
the stagewise hypothesis glue behind `mult` — then the stations
and one displaced cell per link.

```agda
    σ-lêg : PathP (λ m → PathP (λ i → ⊗₁-composite (Qc.σ-leg m i) (Qc'.σ-leg m i))
                         (η ▿₁ θ ▿₁ ζ) (η ▵₁ θ ▿₁ ζ))
                  ι̂w ι̂t
    σ-lêg m = ⊗₁-interchange♭ Û (braid-σ●₁ V̂ Ŵ (~ m))

    cast-arĝ : PathP (λ m → PathP (λ i → ⊗₁-composite (Qc.cast-arg m i)
                                                       (Qc'.cast-arg m i))
                           (η ▿₁ θ ▿₁ ζ) (η ▵₁ θ ▿₁ ζ))
                     ι̂uw▿ ι̂t
    cast-arĝ =
      comp-pathp₂
        (λ p p' → PathP (λ i → ⊗₁-composite (p i) (p' i))
                        (η ▿₁ θ ▿₁ ζ) (η ▵₁ θ ▿₁ ζ))
        mw Qc.σ-leg mw' Qc'.σ-leg m̂w σ-lêg

    mult-arĝ : PathP (λ m → PathP (λ i → ⊗₁-composite (Qc.mult-arg m i)
                                                       (Qc'.mult-arg m i))
                           N₀ (η ▵₁ ζ ▵₁ θ))
                     (comp-pathp₂ ⊗₁-composite Q.ιr Q.ιvw▵ Q'.ιr Q'.ιvw▵ ι̂r ι̂vw▵)
                     (comp-pathp₂ ⊗₁-composite Q.ιuv▿ Q.ιo Q'.ιuv▿ Q'.ιo ι̂uv▿ ι̂o)
    mult-arĝ m =
      comp-pathp₂ ⊗₁-composite (mr (~ m)) (ml m) (mr' (~ m)) (ml' m)
        (m̂r (~ m)) (m̂l m)
```

The displaced stations, each spelled once.

```agda
    ĉ₁ : Famc Qc.c₁ Qc'.c₁
    ĉ₁ = comp-pathp₂ ⊗₁-composite
           (Q.bvw▿ ∙ Q.ιuw▿) Q.suw▿ (Q'.bvw▿ ∙ Q'.ιuw▿) Q'.suw▿
           (comp-pathp₂ ⊗₁-composite Q.bvw▿ Q.ιuw▿ Q'.bvw▿ Q'.ιuw▿ b̂vw▿ ι̂uw▿)
           ŝuw▿

    ĉ₂ : Famc Qc.c₂ Qc'.c₂
    ĉ₂ = comp-pathp₂ ⊗₁-composite
           (Q.bvw▿ ∙ Q.ιt) Q.suw▿ (Q'.bvw▿ ∙ Q'.ιt) Q'.suw▿
           (comp-pathp₂ ⊗₁-composite Q.bvw▿ Q.ιt Q'.bvw▿ Q'.ιt b̂vw▿ ι̂t)
           ŝuw▿

    ĉ₃ : Famc Qc.c₃ Qc'.c₃
    ĉ₃ = comp-pathp₂ ⊗₁-composite
           (Q.ιr ∙ Q.bvw▵) Q.suw▿ (Q'.ιr ∙ Q'.bvw▵) Q'.suw▿
           (comp-pathp₂ ⊗₁-composite Q.ιr Q.bvw▵ Q'.ιr Q'.bvw▵ ι̂r b̂vw▵)
           ŝuw▿

    ĉ₄ : Famc Qc.c₄ Qc'.c₄
    ĉ₄ = comp-pathp₂ ⊗₁-composite
           ((Q.ιr ∙ Q.ιvw▵) ∙ Q.svw▵) Q.suw▿
           ((Q'.ιr ∙ Q'.ιvw▵) ∙ Q'.svw▵) Q'.suw▿
           (comp-pathp₂ ⊗₁-composite
             (Q.ιr ∙ Q.ιvw▵) Q.svw▵ (Q'.ιr ∙ Q'.ιvw▵) Q'.svw▵
             (comp-pathp₂ ⊗₁-composite Q.ιr Q.ιvw▵ Q'.ιr Q'.ιvw▵ ι̂r ι̂vw▵)
             ŝvw▵)
           ŝuw▿

    ĉ₅ : Famc Qc.c₅ Qc'.c₅
    ĉ₅ = comp-pathp₂ ⊗₁-composite
           ((Q.ιuv▿ ∙ Q.ιo) ∙ Q.svw▵) Q.suw▿
           ((Q'.ιuv▿ ∙ Q'.ιo) ∙ Q'.svw▵) Q'.suw▿
           (comp-pathp₂ ⊗₁-composite
             (Q.ιuv▿ ∙ Q.ιo) Q.svw▵ (Q'.ιuv▿ ∙ Q'.ιo) Q'.svw▵
             (comp-pathp₂ ⊗₁-composite Q.ιuv▿ Q.ιo Q'.ιuv▿ Q'.ιo ι̂uv▿ ι̂o)
             ŝvw▵)
           ŝuw▿

    ĥead : PathP (λ i → ⊗₁-composite ((Q.ιc ∙ Q.ιuv▵) i) ((Q'.ιc ∙ Q'.ιuv▵) i))
                 N₀ (η ▵₁ ζ ▵₁ θ)
    ĥead = comp-pathp₂ ⊗₁-composite Q.ιc Q.ιuv▵ Q'.ιc Q'.ιuv▵ ι̂c ι̂uv▵

    ĉ₆ : Famc Qc.c₆ Qc'.c₆
    ĉ₆ = comp-pathp₂ ⊗₁-composite
           ((Q.ιc ∙ Q.ιuv▵) ∙ Q.svw▵) Q.suw▿
           ((Q'.ιc ∙ Q'.ιuv▵) ∙ Q'.svw▵) Q'.suw▿
           (comp-pathp₂ ⊗₁-composite
             (Q.ιc ∙ Q.ιuv▵) Q.svw▵ (Q'.ιc ∙ Q'.ιuv▵) Q'.svw▵
             ĥead ŝvw▵)
           ŝuw▿

    ĉ₇ : Famc Qc.c₇ Qc'.c₇
    ĉ₇ = comp-pathp₂ ⊗₁-composite
           (Q.ιc ∙ Q.ιuv▵) (Q.svw▵ ∙ Q.suw▿)
           (Q'.ιc ∙ Q'.ιuv▵) (Q'.svw▵ ∙ Q'.suw▿)
           ĥead t̂ail
```

The displaced links.

```agda
    merge-r̂ : PathP (λ m → Famc (Qc.merge-r m) (Qc'.merge-r m)) two-step̂ ĉ₁
    merge-r̂ m =
      comp-pathp₂-merge-map ⊗₁-composite ⊗₁-composite
        (λ X → X ▿₀ G) (λ X → X ▿₀ G') (λ ξ → ξ ▿₁ ζ)
        Q.bvw▿ (⊗₀-interchange♭ U W) (⊗₀-flank-swap♭ U W)
        Q'.bvw▿ (⊗₀-interchange♭ U' W') (⊗₀-flank-swap♭ U' W')
        b̂vw▿ (⊗₁-interchange♭ Û Ŵ) (⊗₁-flank-swap♭ Û Ŵ)
        (~ m)

    câst : PathP (λ m → Famc (Qc.cast m) (Qc'.cast m)) ĉ₁ ĉ₂
    câst m =
      comp-pathp₂ ⊗₁-composite
        (Q.bvw▿ ∙ Qc.cast-arg m) Q.suw▿ (Q'.bvw▿ ∙ Qc'.cast-arg m) Q'.suw▿
        (comp-pathp₂ ⊗₁-composite Q.bvw▿ (Qc.cast-arg m) Q'.bvw▿ (Qc'.cast-arg m)
          b̂vw▿ (cast-arĝ m))
        ŝuw▿

    ι-slidê : PathP (λ m → PathP (λ i → ⊗₁-composite (Qc.ι-slide m i)
                                                      (Qc'.ι-slide m i))
                          N₀ (η ▵₁ θ ▿₁ ζ))
                    (comp-pathp₂ ⊗₁-composite Q.bvw▿ Q.ιt Q'.bvw▿ Q'.ιt b̂vw▿ ι̂t)
                    (comp-pathp₂ ⊗₁-composite Q.ιr Q.bvw▵ Q'.ιr Q'.bvw▵ ι̂r b̂vw▵)
    ι-slidê =
      comp-pathp₂-commutes ⊗₁-composite
        Q.bvw▿ Q.ιt Q.ιr Q.bvw▵ Q'.bvw▿ Q'.ιt Q'.ιr Q'.bvw▵
        Qc.slide-sq Qc'.slide-sq
        b̂vw▿ ι̂t ι̂r b̂vw▵
        (λ j m → ⊗₁-interchange♭ Û (↝̂-fill (V̂ ●₁ Ŵ) (⊗₁-braid♭ V̂ Ŵ) m) j)

    commutê : PathP (λ m → Famc (Qc.commute m) (Qc'.commute m)) ĉ₂ ĉ₃
    commutê m =
      comp-pathp₂ ⊗₁-composite
        (Qc.ι-slide m) Q.suw▿ (Qc'.ι-slide m) Q'.suw▿
        (ι-slidê m) ŝuw▿

    merge-l̂ : PathP (λ m → Famc (Qc.merge-l m) (Qc'.merge-l m)) ĉ₃ ĉ₄
    merge-l̂ m =
      comp-pathp₂ ⊗₁-composite
        (ap-merge (λ X → F ▵₀ X) Q.ιr
          (⊗₀-interchange♭ V W) (⊗₀-flank-swap♭ V W) (~ m))
        Q.suw▿
        (ap-merge (λ X → F' ▵₀ X) Q'.ιr
          (⊗₀-interchange♭ V' W') (⊗₀-flank-swap♭ V' W') (~ m))
        Q'.suw▿
        (comp-pathp₂-merge-map ⊗₁-composite ⊗₁-composite
          (λ X → F ▵₀ X) (λ X → F' ▵₀ X) (λ ξ → η ▵₁ ξ)
          Q.ιr (⊗₀-interchange♭ V W) (⊗₀-flank-swap♭ V W)
          Q'.ιr (⊗₀-interchange♭ V' W') (⊗₀-flank-swap♭ V' W')
          ι̂r (⊗₁-interchange♭ V̂ Ŵ) (⊗₁-flank-swap♭ V̂ Ŵ)
          (~ m))
        ŝuw▿

    mult̂ : PathP (λ m → Famc (Qc.mult m) (Qc'.mult m)) ĉ₄ ĉ₅
    mult̂ m =
      comp-pathp₂ ⊗₁-composite
        (Qc.mult-arg m ∙ Q.svw▵) Q.suw▿ (Qc'.mult-arg m ∙ Q'.svw▵) Q'.suw▿
        (comp-pathp₂ ⊗₁-composite
          (Qc.mult-arg m) Q.svw▵ (Qc'.mult-arg m) Q'.svw▵
          (mult-arĝ m) ŝvw▵)
        ŝuw▿

    naturâl : PathP (λ m → Famc (Qc.natural m) (Qc'.natural m)) ĉ₅ ĉ₆
    naturâl m =
      comp-pathp₂ ⊗₁-composite
        (⊗₀-interchange-natural U V W m ∙ Q.svw▵) Q.suw▿
        (⊗₀-interchange-natural U' V' W' m ∙ Q'.svw▵) Q'.suw▿
        (comp-pathp₂ ⊗₁-composite
          (⊗₀-interchange-natural U V W m) Q.svw▵
          (⊗₀-interchange-natural U' V' W' m) Q'.svw▵
          (⊗₁-interchange-natural Û V̂ Ŵ m) ŝvw▵)
        ŝuw▿

    flatten̂₁ : PathP (λ m → Famc (Qc.flatten₁ m) (Qc'.flatten₁ m)) ĉ₆ ĉ₇
    flatten̂₁ m =
      comp-pathp₂-assoc ⊗₁-composite
        (Q.ιc ∙ Q.ιuv▵) Q.svw▵ Q.suw▿ (Q'.ιc ∙ Q'.ιuv▵) Q'.svw▵ Q'.suw▿
        ĥead ŝvw▵ ŝuw▿ (~ m)

    flatten̂₂ : PathP (λ m → Famc (Qc.flatten₂ m) (Qc'.flatten₂ m)) ĉ₇
                (comp-pathp₂ ⊗₁-composite Q.ιc Q.decomp Q'.ιc Q'.decomp ι̂c decomp̂)
    flatten̂₂ m =
      comp-pathp₂-assoc ⊗₁-composite
        Q.ιc Q.ιuv▵ (Q.svw▵ ∙ Q.suw▿) Q'.ιc Q'.ιuv▵ (Q'.svw▵ ∙ Q'.suw▿)
        ι̂c ι̂uv▵ t̂ail (~ m)
```

The displaced bridge, glued by `comp-pathp₂` at the family of
statement lines along exactly the base tree, and the displaced
fillers: `comp-pathp₂-rfill` transposed and reversed over the
level-0 fills, and the prepend retaken as one `com` along the
level-0 tube.

```agda
    bridgê : PathP (λ m → Famc (Qc.bridge m) (Qc'.bridge m)) two-step̂
             (comp-pathp₂ ⊗₁-composite Q.ιc Q.decomp Q'.ιc Q'.decomp ι̂c decomp̂)
    bridgê =
      comp-pathp₂ Famc
        Qc.merge-r
        (Qc.cast ∙ Qc.commute ∙ Qc.merge-l ∙ Qc.mult ∙ Qc.natural
         ∙ Qc.flatten₁ ∙ Qc.flatten₂)
        Qc'.merge-r
        (Qc'.cast ∙ Qc'.commute ∙ Qc'.merge-l ∙ Qc'.mult ∙ Qc'.natural
         ∙ Qc'.flatten₁ ∙ Qc'.flatten₂)
        merge-r̂
        (comp-pathp₂ Famc
          Qc.cast
          (Qc.commute ∙ Qc.merge-l ∙ Qc.mult ∙ Qc.natural
           ∙ Qc.flatten₁ ∙ Qc.flatten₂)
          Qc'.cast
          (Qc'.commute ∙ Qc'.merge-l ∙ Qc'.mult ∙ Qc'.natural
           ∙ Qc'.flatten₁ ∙ Qc'.flatten₂)
          câst
          (comp-pathp₂ Famc
            Qc.commute
            (Qc.merge-l ∙ Qc.mult ∙ Qc.natural ∙ Qc.flatten₁ ∙ Qc.flatten₂)
            Qc'.commute
            (Qc'.merge-l ∙ Qc'.mult ∙ Qc'.natural ∙ Qc'.flatten₁ ∙ Qc'.flatten₂)
            commutê
            (comp-pathp₂ Famc
              Qc.merge-l
              (Qc.mult ∙ Qc.natural ∙ Qc.flatten₁ ∙ Qc.flatten₂)
              Qc'.merge-l
              (Qc'.mult ∙ Qc'.natural ∙ Qc'.flatten₁ ∙ Qc'.flatten₂)
              merge-l̂
              (comp-pathp₂ Famc
                Qc.mult (Qc.natural ∙ Qc.flatten₁ ∙ Qc.flatten₂)
                Qc'.mult (Qc'.natural ∙ Qc'.flatten₁ ∙ Qc'.flatten₂)
                mult̂
                (comp-pathp₂ Famc
                  Qc.natural (Qc.flatten₁ ∙ Qc.flatten₂)
                  Qc'.natural (Qc'.flatten₁ ∙ Qc'.flatten₂)
                  naturâl
                  (comp-pathp₂ Famc
                    Qc.flatten₁ Qc.flatten₂ Qc'.flatten₁ Qc'.flatten₂
                    flatten̂₁ flatten̂₂))))))

    braid-fill̂
      : PathP (λ m → PathP (λ i → ⊗₁-composite (Q.braid-fill m i)
                                                (Q'.braid-fill m i))
                     (ι̂c m) N₁)
        (⊗₁-braid♭ (Û ●₁ V̂) Ŵ) ŝc
    braid-fill̂ m i = comp-pathp₂-rfill ⊗₁-composite Q.ιc Q.swapc Q'.ιc Q'.swapc ι̂c ŝc i (~ m)

    decomp-fill̂
      : PathP (λ m → PathP (λ i → ⊗₁-composite (Q.decomp-fill m i)
                                                (Q'.decomp-fill m i))
                     (ι̂c m) N₁)
        (comp-pathp₂ ⊗₁-composite Q.ιc Q.decomp Q'.ιc Q'.decomp ι̂c decomp̂)
        decomp̂
    decomp-fill̂ m i =
      comp-pathp₂-rfill ⊗₁-composite Q.ιc Q.decomp Q'.ιc Q'.decomp ι̂c decomp̂ i (~ m)

    bridge-fill̂
      : PathP (λ m → PathP (λ i → ⊗₁-composite (Qc.bridge-fill m i)
                                                (Qc'.bridge-fill m i))
                     (ι̂c m) N₁)
        two-step̂ decomp̂
    bridge-fill̂ m =
      com (λ k → PathP (λ i → ⊗₁-composite (Qc.bridge-tube m k i)
                                            (Qc'.bridge-tube m k i))
                 (ι̂c m) N₁)
          (∂ m) λ where
        k (m = i0) → bridgê (~ k)
        k (m = i1) → decomp̂
        k (k = i0) → decomp-fill̂ m
```

The displaced equivalence: for any pair of object-grade
statement proofs, the displaced statement types line up over the
`transport-filler` of the level-0 statement line, and transport
along the displaced line is the equivalence — the `-l` hexagon
field statement at grade 1 against the swap-half statement over
the transported grade-0 proofs.

```agda
    module _ (e₀ : ⊗₀-braid♭ (U ●₀ V) W ≡ Q.two-step)
             (e₀' : ⊗₀-braid♭ (U' ●₀ V') W' ≡ Q'.two-step)
      where

      private
        Ê₀ : PathP (λ m → Qc.stmt-line m) e₀ (transport Qc.stmt-line e₀)
        Ê₀ = transport-filler Qc.stmt-line e₀

        Ê₀' : PathP (λ m → Qc'.stmt-line m) e₀' (transport Qc'.stmt-line e₀')
        Ê₀' = transport-filler Qc'.stmt-line e₀'

      stmt-linê
        : (PathP (λ k → PathP (λ i → ⊗₁-composite (e₀ k i) (e₀' k i)) N₀ N₁)
             (⊗₁-braid♭ (Û ●₁ V̂) Ŵ) two-step̂)
        ≡ (PathP (λ k → PathP (λ i → ⊗₁-composite
                                       (transport Qc.stmt-line e₀ k i)
                                       (transport Qc'.stmt-line e₀' k i))
                        (η ▿₁ ζ ▵₁ θ) N₁)
             (⊗₁-flank-swap♭ (Û ●₁ V̂) Ŵ) decomp̂)
      stmt-linê m =
        PathP (λ k → PathP (λ i → ⊗₁-composite (Ê₀ m k i) (Ê₀' m k i))
                     (ι̂c m) N₁)
              (braid-fill̂ m) (bridge-fill̂ m)

      hexagon-l≃swap-half
        : (PathP (λ k → PathP (λ i → ⊗₁-composite (e₀ k i) (e₀' k i)) N₀ N₁)
             (⊗₁-braid♭ (Û ●₁ V̂) Ŵ) two-step̂)
        ≃ (PathP (λ k → PathP (λ i → ⊗₁-composite
                                       (transport Qc.stmt-line e₀ k i)
                                       (transport Qc'.stmt-line e₀' k i))
                        (η ▿₁ ζ ▵₁ θ) N₁)
             (⊗₁-flank-swap♭ (Û ●₁ V̂) Ŵ) decomp̂)
      hexagon-l≃swap-half = transport stmt-linê , transport-equiv stmt-linê
```
