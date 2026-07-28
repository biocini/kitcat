Lane Biocini
July 2026

`theoryᴰ`: the derived theory of a displayed category, displacing
`Bb.CatsWithExplicitInterchange.Base.theory` clause by clause. Unlike
the monoidal `theory₀` — a transcription whose delta was pure erasure —
this is a genuinely displaced development: each `∙` in a
`Bb.CatsWithExplicitInterchange.Base` proof becomes a `comp-pathp₁` over
the composed base path, each `subst` a transport along a line of
displayed types. The proof shapes follow
`Bb.CatsWithExplicitInterchange.Base` line by line, and the monoidal
`theory₁` is the worked one-object special case of exactly this glue.

The spine of the development: the displayed hom-fiber is
contractible by projection from `spineᴰ-contr` (the Kan lid over the
base spine's coherence square); the displayed unit chain rides
`comp-pathp₁` over the base chain; the displayed image fiber
contracts by straightening the push fiber along `unitl` — the
`sq-from-∙` square of `ap emb (unitl f)`'s decomposition, whose
computation is pure base theory. From there the displaced witness
calculus is uniform: `repr-contrᴰ` slides any inhabitant's
characterization along its own base line, `repr-σᴰ[_]` threads two
witnesses through the pointwise-contractible line over an arbitrary
base identification (opaque, so consumers' families keep its
projections neutral, and sealed base σ-lines are consumed as
neutral families — no unfolding), and every displaced identity is
the calculus projection at normal witnesses — one construction
each, never two constructions and a bridge: `assocᴰ` is `assoc●ᴰ`
at `nrm[_]`s exactly as `assoc` is `assoc●` at `nrm`s, and the
unitors are the hom shadows of `repr-σᴰ[_]` at the sealed unitor
σ-lines.

Deferred, with the square-level calculus: the displaced
`repr-lc`/`repr-refl`/`repr-ap`/`repr-∙`/`↝-repr` (2-cell
displacements over the base repr algebra) and the total category
`∫` — its Σ-reshuffle `split` is the construction's one genuine
obligation and gets its own spike first.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Bb.CatsWithExplicitInterchange.Displayed.Base where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Path.Base
open import Core.Transport.Base using (is-prop→PathP; transport)
open import Core.Transport.J using (subst)
open import Core.Transport.Properties using (ap-fst-fiber; sq-from-∙)
open import Core.Equiv.Base using (iso→equiv; _≃_; is-equiv; id-equiv)

open import Bb.CatsWithExplicitInterchange.Type
open import Bb.CatsWithExplicitInterchange.Base
open import Bb.CatsWithExplicitInterchange.Displayed

module theoryᴰ {o h o' h'} {C : category o h} (D : categoryᴰ C o' h') where
  open category C
  open theory C
  open categoryᴰ D
```

## The displaced total-space equivalence

```agda
  hom≃total-representableᴰ
    : ∀ {x y} {f : hom x y} {x' y'}
    → hom[ f ] x' y'
    ≃ (Σ α' ∶ composite[ emb f ] x' y' , is-representable[ nrm f ] α')
  hom≃total-representableᴰ {f = f} {x'} {y'} = iso→equiv fwd bwd ret sec
    where
      fwd : hom[ f ] x' y'
          → Σ α' ∶ composite[ emb f ] x' y' , is-representable[ nrm f ] α'
      fwd f' = emb[ f' ] , f' , refl

      bwd : (Σ α' ∶ composite[ emb f ] x' y' , is-representable[ nrm f ] α')
          → hom[ f ] x' y'
      bwd (_ , m' , _) = m'

      ret : ∀ f' → bwd (fwd f') ≡ f'
      ret f' = refl

      sec : ∀ s → fwd (bwd s) ≡ s
      sec (_ , m' , P) i = P i , m' , λ j → P (i ∧ j)
```

## The contractible displayed hom-fiber

A displayed spine candidate with the pre-side characterization
extends to a full `spineᴰ`: over the base spine's coherence square,
the pre side (base of the box), the constant `emb[ k' ]`, and
`interchangeᴰ` bound an open box whose lid is the post side. The
fiber is then contractible by projection from `spineᴰ-contr`, in
both directions.

```agda
  module hfiberᴰ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
    (f' : hom[ f ] x' y') (g' : hom[ g ] y' z') where

    p-charᴰ : hom[ f ⨾ g ] x' z' → Type (o ⊔ h ⊔ o' ⊔ h')
    p-charᴰ k' =
      PathP (λ i → composite[ emb-comp f g i ] x' z')
            (emb[ k' ]) (emb[ f' ] ▾ᴰ g')

    q-charᴰ : hom[ f ⨾ g ] x' z' → Type (o ⊔ h ⊔ o' ⊔ h')
    q-charᴰ k' =
      PathP (λ i → composite[ emb-comp-op f g i ] x' z')
            (emb[ k' ]) (f' ▴ᴰ emb[ g' ])

    private
      lid : ∀ {k'} (pc : p-charᴰ k') (i j : I)
          → composite[ emb-comp-coh f g i j ] x' z'
      lid {k'} pc i j =
        fil (λ k → composite[ emb-comp-coh f g k j ] x' z') (∂ j) i λ where
          k (j = i0) → emb[ k' ]
          k (j = i1) → interchangeᴰ f' g' k
          k (k = i0) → pc j

    extend-q : ∀ {k'} → p-charᴰ k' → q-charᴰ k'
    extend-q pc j = lid pc i1 j

    extend-θ
      : ∀ {k'} (pc : p-charᴰ k')
      → PathP (λ i → PathP (λ j → composite[ emb-comp-coh f g i j ] x' z')
                     (emb[ k' ]) (interchangeᴰ f' g' i))
              pc (extend-q pc)
    extend-θ pc i j = lid pc i j

    pull-contrᴰ : is-contr (Σ k' ∶ hom[ f ⨾ g ] x' z' , p-charᴰ k')
    pull-contrᴰ .center = f' ⨾ᴰ g' , emb-compᴰ f' g'
    pull-contrᴰ .paths (k' , pc) i = Φ i .fst , Φ i .snd .fst
      where
        Φ : spineᴰ-contr f' g' .center ≡ (k' , pc , extend-q pc , extend-θ pc)
        Φ = spineᴰ-contr f' g' .paths (k' , pc , extend-q pc , extend-θ pc)

    private
      rlid : ∀ {k'} (qc : q-charᴰ k') (i j : I)
           → composite[ emb-comp-coh f g (~ i) j ] x' z'
      rlid {k'} qc i j =
        fil (λ k → composite[ emb-comp-coh f g (~ k) j ] x' z') (∂ j) i λ where
          k (j = i0) → emb[ k' ]
          k (j = i1) → interchangeᴰ f' g' (~ k)
          k (k = i0) → qc j

    extend-p : ∀ {k'} → q-charᴰ k' → p-charᴰ k'
    extend-p qc j = rlid qc i1 j

    extend-θ⁻
      : ∀ {k'} (qc : q-charᴰ k')
      → PathP (λ i → PathP (λ j → composite[ emb-comp-coh f g i j ] x' z')
                     (emb[ k' ]) (interchangeᴰ f' g' i))
              (extend-p qc) qc
    extend-θ⁻ qc i j = rlid qc (~ i) j

    push-contrᴰ : is-contr (Σ k' ∶ hom[ f ⨾ g ] x' z' , q-charᴰ k')
    push-contrᴰ .center = f' ⨾ᴰ g' , emb-comp-opᴰ f' g'
    push-contrᴰ .paths (k' , qc) i = Φ i .fst , Φ i .snd .snd .fst
      where
        Φ : spineᴰ-contr f' g' .center ≡ (k' , extend-p qc , qc , extend-θ⁻ qc)
        Φ = spineᴰ-contr f' g' .paths (k' , extend-p qc , qc , extend-θ⁻ qc)

  cast-pathᴰ
    : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
        {f' : hom[ f ] x' y'} {g' : hom[ g ] y' z'}
        {k' : hom[ f ⨾ g ] x' z'}
    → hfiberᴰ.p-charᴰ f' g' k' → f' ⨾ᴰ g' ≡ k'
  cast-pathᴰ {f' = f'} {g'} {k'} pc = ap fst (hfiberᴰ.pull-contrᴰ f' g' .paths (k' , pc))

  cast-path⁻¹ᴰ
    : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
        {f' : hom[ f ] x' y'} {g' : hom[ g ] y' z'}
        {k' : hom[ f ⨾ g ] x' z'}
    → f' ⨾ᴰ g' ≡ k' → hfiberᴰ.p-charᴰ f' g' k'
  cast-path⁻¹ᴰ {f' = f'} {g'} p = pcom (ap (λ t → emb[ t ]) p) (emb-compᴰ f' g') refl
```

## The displaced unit chain

Each link of `Bb.CatsWithExplicitInterchange.Base`'s unit chain has a
displayed image over the same base path, glued link by link by
`comp-pathp₁` at the family `hom[_]`; the second factor of each link is
the pointwise action of a displayed operator on `unitᴰ`.

```agda
  comp-eq-evᴰ
    : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
      (f' : hom[ f ] x' y') (g' : hom[ g ] y' z')
    → PathP (λ i → hom[ comp-eq-ev f g i ] x' z')
            (f' ⨾ᴰ g') (ev[ emb[ f' ] ▾ᴰ g' ])
  comp-eq-evᴰ {f = f} {g} {x'} {z' = z'} f' g' =
    comp-pathp₁ (λ t → hom[ t ] x' z')
      (sym (unit (f ⨾ g))) (ap (λ α → ev α) (emb-comp f g))
      (λ i → unitᴰ (f' ⨾ᴰ g') (~ i))
      (λ i → ev[ emb-compᴰ f' g' i ])

  comp-eq-preᴰ
    : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
      (f' : hom[ f ] x' y') (g' : hom[ g ] y' z')
    → PathP (λ i → hom[ comp-eq-pre f g i ] x' z')
            (f' ⨾ᴰ g') (pre[ f' ] g')
  comp-eq-preᴰ {f = f} {g} {x'} {z' = z'} f' g' =
    comp-pathp₁ (λ t → hom[ t ] x' z')
      (comp-eq-ev f g) (ap (λ t → pre f t) (unit g))
      (comp-eq-evᴰ f' g')
      (λ i → pre[ f' ] (unitᴰ g' i))

  comp-eq-postᴰ
    : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
      (f' : hom[ f ] x' y') (g' : hom[ g ] y' z')
    → PathP (λ i → hom[ comp-eq-post f g i ] x' z')
            (f' ⨾ᴰ g') (post[ g' ] f')
  comp-eq-postᴰ {f = f} {g} {x'} {z' = z'} f' g' =
    comp-pathp₁ (λ t → hom[ t ] x' z')
      (sym (unit (f ⨾ g)))
      (ap (λ α → ev α) (emb-comp-op f g) ∙ ap (λ t → post g t) (unit f))
      (λ i → unitᴰ (f' ⨾ᴰ g') (~ i))
      (comp-pathp₁ (λ t → hom[ t ] x' z')
        (ap (λ α → ev α) (emb-comp-op f g)) (ap (λ t → post g t) (unit f))
        (λ i → ev[ emb-comp-opᴰ f' g' i ])
        (λ i → post[ g' ] (unitᴰ f' i)))

  pre-is-postᴰ
    : ∀ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
      (f' : hom[ f ] x' y') (g' : hom[ g ] y' z')
    → PathP (λ i → hom[ pre-is-post f g i ] x' z')
            (pre[ f' ] g') (post[ g' ] f')
  pre-is-postᴰ {f = f} {g} {x'} {z' = z'} f' g' =
    comp-pathp₁ (λ t → hom[ t ] x' z')
      (sym (comp-eq-pre f g)) (comp-eq-post f g)
      (λ i → comp-eq-preᴰ f' g' (~ i)) (comp-eq-postᴰ f' g')

  absorb-lᴰ
    : ∀ {x v} {b : hom x v} {x' v'} (b' : hom[ b ] x' v')
    → PathP (λ i → hom[ absorb-l b i ] x' v') (pre[ idn[ x' ] ] b') b'
  absorb-lᴰ {x} {b = b} {x'} {v'} b' =
    comp-pathp₁ (λ t → hom[ t ] x' v')
      (pre-is-post (idn x) b) (unit b)
      (pre-is-postᴰ idn[ x' ] b') (unitᴰ b')

  absorb-rᴰ
    : ∀ {w x} {a : hom w x} {w' x'} (a' : hom[ a ] w' x')
    → PathP (λ i → hom[ absorb-r a i ] w' x') (post[ idn[ x' ] ] a') a'
  absorb-rᴰ {a = a} {w'} {x'} a' =
    comp-pathp₁ (λ t → hom[ t ] w' x')
      (sym (pre-is-post a (idn _))) (unit a)
      (λ i → pre-is-postᴰ a' idn[ x' ] (~ i)) (unitᴰ a')
```

## Displaced funext and the identity absorptions

The displayed funext absorptions are direct interval terms — the
context reindexed by the displaced absorption, over the base's
pointwise `funext`.

```agda
  idn-▴ᴰ
    : ∀ {x y} {β : composite x y} {x' y'} (β' : composite[ β ] x' y')
    → PathP (λ i → composite[ idn-▴ β i ] x' y') (idn[ x' ] ▴ᴰ β') β'
  idn-▴ᴰ β' i γ γ' =
    β' ((γ .fst .fst , absorb-r (γ .fst .snd) i) , γ .snd)
       ((γ' .fst .fst , absorb-rᴰ (γ' .fst .snd) i) , γ' .snd)

  ▾-idnᴰ
    : ∀ {x y} {α : composite x y} {x' y'} (α' : composite[ α ] x' y')
    → PathP (λ i → composite[ ▾-idn α i ] x' y') (α' ▾ᴰ idn[ y' ]) α'
  ▾-idnᴰ α' i γ γ' =
    α' (γ .fst , (γ .snd .fst , absorb-l (γ .snd .snd) i))
       (γ' .fst , (γ' .snd .fst , absorb-lᴰ (γ' .snd .snd) i))

  emb-idn-absorbᴰ
    : ∀ {x y} {f : hom x y} {x' y'} (f' : hom[ f ] x' y')
    → PathP (λ i → composite[ emb-idn-absorb f i ] x' y')
            (emb[ idn[ x' ] ] ▾ᴰ f') (emb[ f' ])
  emb-idn-absorbᴰ {x} {f = f} {x'} {y'} f' =
    comp-pathp₁ (λ t → composite[ t ] x' y')
      (interchange (idn x) f) (idn-▴ (emb f))
      (interchangeᴰ idn[ x' ] f') (idn-▴ᴰ (emb[ f' ]))
```

## The displayed image contraction

`ap emb (unitl f)` computes, in pure base theory, to the
`∙`-decomposition through `emb-comp-op (idn x) f` and the funext
absorption — `ap-fst-fiber` at the unitor's σ-line, the `∙ refl`
redexes of `nrm`/`●`/`↝` discharged by `Path.unitr`, and the
spine's 2-cell `coh→∙`. `sq-from-∙` packages the decomposition
as a square; the square bounds a line of displayed fibers from the
push fiber at the identity to the plain displayed image fiber, and
contractibility rides across.

```agda
  private
    unitl-ap
      : ∀ {x y} (f : hom x y)
      → ap emb (unitl f) ≡ emb-comp-op (idn x) f ∙ idn-▴ (emb f)
    unitl-ap {x} f =
        ap-fst-fiber κ₀
      ∙ Path.unitr (U .snd)
      ∙ ap (_∙ emb-idn-absorb f) (Path.unitr (emb-comp (idn x) f))
      ∙ Path.assoc (emb-comp (idn x) f) (interchange (idn x) f)
          (idn-▴ (emb f))
      ∙ ap (_∙ idn-▴ (emb f)) (coh→∙ (idn x) f)
      where
        U V : is-representable (emb f)
        U = (nrm (idn x) ● nrm f) ↝ emb-idn-absorb f
        V = nrm f

        κ₀ : U ≡ V
        κ₀ = unitl-σ● f

    -- the straightening square: top ap emb (unitl f), left
    -- emb-comp-op (idn x) f, bottom idn-▴, right constant
    unitl-sq : ∀ {x y} (f : hom x y) → (j i : I) → composite x y
    unitl-sq f j i = sq-from-∙ (unitl-ap f) i j

    -- the line of displayed fibers along unitl
    unitl-line
      : ∀ {x y} {f : hom x y} {x' y'} (f' : hom[ f ] x' y')
      → I → Type (o ⊔ h ⊔ o' ⊔ h')
    unitl-line {f = f} {x'} {y'} f' j =
      Σ k' ∶ hom[ unitl f j ] x' y' ,
        PathP (λ i → composite[ unitl-sq f j i ] x' y')
              (emb[ k' ]) (idn-▴ᴰ (emb[ f' ]) j)

  emb-image-contrᴰ
    : ∀ {x y} {f : hom x y} {x' y'} (f' : hom[ f ] x' y')
    → is-contr (is-representable[ nrm f ] (emb[ f' ]))
  emb-image-contrᴰ {x' = x'} f' =
    subst is-contr (λ j → unitl-line f' j)
      (hfiberᴰ.push-contrᴰ idn[ x' ] f')
```

## The displaced witness calculus

Contractibility over an arbitrary base witness needs no chains:
sliding an inhabitant's characterization along its own base line
connects the space to the plain displayed image fiber. `repr-σᴰ[_]`
is the displaced line over an arbitrary identification of base
witnesses: the base fiber is propositional, so every σ lifts —
contractibility transported along σ's connection, `is-prop→PathP`
threading any two inhabitants. It is opaque, so a consumer's family
projects neutrals, and it consumes its base line as a neutral
family, so instances at sealed σ-lines need no unfolding. `repr-σᴰ`
is its instance at the canonical propositionality path and
`repr-uniqueᴰ` that instance's hom component, the displaced
`repr-unique`. `_●ᴰ_` and `_↝ᴰ_` mirror `_●_` and `_↝_`
with `comp-pathp₁` in the role of `∙`. `●ᴰ-∙` glues witness lines
over composite fiber paths, with `comp-pathp₁-over` supplying the
characterization over the hom-level `comp-pathp₁`: the hom component
of the glue is the `comp-pathp₁` of the hom components by
construction — `hcom` at a Σ-type does not project componentwise, so
the pair is assembled, never projected.

```agda
  repr-contrᴰ
    : ∀ {x y} {α : composite x y} {x' y'}
        {U : is-representable α} {α' : composite[ α ] x' y'}
    → is-representable[ U ] α' → is-contr (is-representable[ U ] α')
  repr-contrᴰ {x' = x'} {y'} {U = m , p} (m' , P) =
    subst is-contr
      (λ j → Σ k' ∶ hom[ m ] x' y' ,
             PathP (λ i → composite[ p (j ∧ i) ] x' y') (emb[ k' ]) (P j))
      (emb-image-contrᴰ m')

  opaque
    repr-σᴰ[_]
      : ∀ {x y} {α : composite x y} {x' y'}
          {u₀ u₁ : is-representable α} (σ : u₀ ≡ u₁)
          {α' : composite[ α ] x' y'}
        (U' : is-representable[ u₀ ] α') (V' : is-representable[ u₁ ] α')
      → PathP (λ i → is-representable[ σ i ] α') U' V'
    repr-σᴰ[_] σ {α'} U' V' =
      is-prop→PathP
        (λ i → is-contr→is-prop
          (subst is-contr
            (λ k → is-representable[ σ (i ∧ k) ] α')
            (repr-contrᴰ U')))
        U' V'

  repr-σᴰ
    : ∀ {x y} {α : composite x y} {x' y'}
        {U V : is-representable α} {α' : composite[ α ] x' y'}
      (U' : is-representable[ U ] α') (V' : is-representable[ V ] α')
    → PathP (λ i → is-representable[ is-representable-prop α U V i ] α')
            U' V'
  repr-σᴰ {α = α} {U = U} {V} = repr-σᴰ[ is-representable-prop α U V ]

  repr-uniqueᴰ
    : ∀ {x y} {α : composite x y} {x' y'}
        {U V : is-representable α} {α' : composite[ α ] x' y'}
      (U' : is-representable[ U ] α') (V' : is-representable[ V ] α')
    → PathP (λ i → hom[ repr-unique U V i ] x' y') (U' .fst) (V' .fst)
  repr-uniqueᴰ U' V' i = repr-σᴰ U' V' i .fst

  _●ᴰ_
    : ∀ {x y z} {A : composite x y} {B : composite y z} {x' y' z'}
        {U : is-representable A} {V : is-representable B}
        {A' : composite[ A ] x' y'} {B' : composite[ B ] y' z'}
    → is-representable[ U ] A' → is-representable[ V ] B'
    → is-representable[ U ● V ] (A' ▿ᴰ B')
  _●ᴰ_ {x' = x'} {z' = z'} {U = m , p} {n , q} (m' , P) (n' , Q) =
    m' ⨾ᴰ n' ,
    comp-pathp₁ (λ t → composite[ t ] x' z')
      (emb-comp m n) (λ i → p i ▿ q i)
      (emb-compᴰ m' n') (λ i → P i ▿ᴰ Q i)
  infixr 40 _●ᴰ_

  _↝ᴰ_
    : ∀ {x y} {A B : composite x y} {x' y'}
        {U : is-representable A}
        {α' : composite[ A ] x' y'} {β' : composite[ B ] x' y'}
        {e : A ≡ B}
    → is-representable[ U ] α'
    → PathP (λ i → composite[ e i ] x' y') α' β'
    → is-representable[ U ↝ e ] β'
  _↝ᴰ_ {x' = x'} {y'} {U = m , p} {e = e} (m' , P) ê =
    m' , comp-pathp₁ (λ t → composite[ t ] x' y') p e P ê

  -- the displaced ↝-fill: the same slide one level up, with
  -- comp-pathp₁-fill in the role of cat.fill — the hom is constant,
  -- at m = i0 the slide is U' (the fil cap), at m = i1 the
  -- transport U' ↝ᴰ ê (the com), both definitional
  ↝ᴰ-fill
    : ∀ {x y} {A B : composite x y} {x' y'}
        {U : is-representable A}
        {α' : composite[ A ] x' y'} {β' : composite[ B ] x' y'}
        {e : A ≡ B}
      (U' : is-representable[ U ] α')
      (ê : PathP (λ i → composite[ e i ] x' y') α' β')
      (m : I)
    → is-representable[ ↝-fill U e m ] (ê m)
  ↝ᴰ-fill {x' = x'} {y'} {U = m₀ , p} {e = e} (m' , P) ê m =
    m' , comp-pathp₁-fill (λ t → composite[ t ] x' y') p e P ê m

  ●ᴰ-∙
    : ∀ {x y} {α : composite x y} {x' y'} {α' : composite[ α ] x' y'}
        {u₀ u₁ u₂ : is-representable α}
      (σa : u₀ ≡ u₁) (σb : u₁ ≡ u₂)
      {û₀ : is-representable[ u₀ ] α'} {û₁ : is-representable[ u₁ ] α'}
      {û₂ : is-representable[ u₂ ] α'}
    → PathP (λ i → is-representable[ σa i ] α') û₀ û₁
    → PathP (λ i → is-representable[ σb i ] α') û₁ û₂
    → PathP (λ i → is-representable[ (σa ∙ σb) i ] α') û₀ û₂
  ●ᴰ-∙ {x' = x'} {y'} {α' = α'} σa σb P̂ Q̂ i =
      comp-pathp₁ (λ u → hom[ u .fst ] x' y') σa σb
        (λ j → P̂ j .fst) (λ j → Q̂ j .fst) i
    , comp-pathp₁-over (λ u → hom[ u .fst ] x' y')
        (λ u σ → PathP (λ k → composite[ u .snd k ] x' y') (emb[ σ ]) α')
        σa σb
        (λ j → P̂ j .fst) (λ j → Q̂ j .fst)
        (λ j → P̂ j .snd) (λ j → Q̂ j .snd) i
```

## Associativity and the unit laws

Each displaced identity is the wit-calculus projection at normal
witnesses — the same construction its base mate names, one level up.
Naturality is the type: one `PathP` between the displayed composites
over the base identity.

```agda
  assoc-σ●ᴰ
    : ∀ {w x y z} {A : composite w x} {B : composite x y}
        {E : composite y z} {w' x' y' z'}
        {U : is-representable A} {V : is-representable B}
        {W : is-representable E}
        {A' : composite[ A ] w' x'} {B' : composite[ B ] x' y'}
        {E' : composite[ E ] y' z'}
      (U' : is-representable[ U ] A') (V' : is-representable[ V ] B')
      (W' : is-representable[ W ] E')
    → PathP (λ i → is-representable[ assoc-σ● U V W i ]
                     (A' ▿ᴰ (B' ▿ᴰ E')))
            (U' ●ᴰ (V' ●ᴰ W')) ((U' ●ᴰ V') ●ᴰ W')
  assoc-σ●ᴰ {U = U} {V} {W} U' V' W' =
    repr-σᴰ[ assoc-σ● U V W ] (U' ●ᴰ (V' ●ᴰ W')) ((U' ●ᴰ V') ●ᴰ W')

  assoc●ᴰ
    : ∀ {w x y z} {A : composite w x} {B : composite x y}
        {E : composite y z} {w' x' y' z'}
        {U : is-representable A} {V : is-representable B}
        {W : is-representable E}
        {A' : composite[ A ] w' x'} {B' : composite[ B ] x' y'}
        {E' : composite[ E ] y' z'}
      (U' : is-representable[ U ] A') (V' : is-representable[ V ] B')
      (W' : is-representable[ W ] E')
    → PathP (λ i → hom[ assoc● U V W i ] w' z')
            ((U' ●ᴰ (V' ●ᴰ W')) .fst) (((U' ●ᴰ V') ●ᴰ W') .fst)
  assoc●ᴰ U' V' W' i = assoc-σ●ᴰ U' V' W' i .fst

  assocᴰ
    : ∀ {w x y z} {f : hom w x} {g : hom x y} {k : hom y z}
        {w' x' y' z'} (f' : hom[ f ] w' x') (g' : hom[ g ] x' y')
        (k' : hom[ k ] y' z')
    → PathP (λ i → hom[ assoc f g k i ] w' z')
            (f' ⨾ᴰ (g' ⨾ᴰ k')) ((f' ⨾ᴰ g') ⨾ᴰ k')
  assocᴰ f' g' k' = assoc●ᴰ nrm[ f' ] nrm[ g' ] nrm[ k' ]

  unitr-σ●ᴰ
    : ∀ {x y} {f : hom x y} {x' y'} (f' : hom[ f ] x' y')
    → PathP (λ i → is-representable[ unitr-σ● f i ] (emb[ f' ]))
            ((nrm[ f' ] ●ᴰ nrm[ idn[ y' ] ]) ↝ᴰ ▾-idnᴰ (emb[ f' ]))
            nrm[ f' ]
  unitr-σ●ᴰ {f = f} {y' = y'} f' =
    repr-σᴰ[ unitr-σ● f ]
      ((nrm[ f' ] ●ᴰ nrm[ idn[ y' ] ]) ↝ᴰ ▾-idnᴰ (emb[ f' ]))
      nrm[ f' ]

  unitl-σ●ᴰ
    : ∀ {x y} {f : hom x y} {x' y'} (f' : hom[ f ] x' y')
    → PathP (λ i → is-representable[ unitl-σ● f i ] (emb[ f' ]))
            ((nrm[ idn[ x' ] ] ●ᴰ nrm[ f' ]) ↝ᴰ emb-idn-absorbᴰ f')
            nrm[ f' ]
  unitl-σ●ᴰ {f = f} {x' = x'} f' =
    repr-σᴰ[ unitl-σ● f ]
      ((nrm[ idn[ x' ] ] ●ᴰ nrm[ f' ]) ↝ᴰ emb-idn-absorbᴰ f')
      nrm[ f' ]

  unitrᴰ
    : ∀ {x y} {f : hom x y} {x' y'} (f' : hom[ f ] x' y')
    → PathP (λ i → hom[ unitr f i ] x' y') (f' ⨾ᴰ idn[ y' ]) f'
  unitrᴰ f' i = unitr-σ●ᴰ f' i .fst

  unitlᴰ
    : ∀ {x y} {f : hom x y} {x' y'} (f' : hom[ f ] x' y')
    → PathP (λ i → hom[ unitl f i ] x' y') (idn[ x' ] ⨾ᴰ f') f'
  unitlᴰ f' i = unitl-σ●ᴰ f' i .fst
```

## Cartesianness and fibrations

The CPS form makes the cartesianness condition a single `emb[_]`
application: no composite is formed. Over `comp-eq-post a f`, the
displaced comp-eq identifies `post[ f' ] a'` with `a' ⨾ᴰ f'`, so
this is the classical condition. Displayed identities are cartesian
for free — `post[ idn[ x' ] ]` is identified with the identity along
`absorb-rᴰ`, so equivalence transports in from `id-equiv`; this is
the general form of demoting a unit's `is-equiv` fields to theorems.

Note that `cartesian-lift f y'` is not contractible in general:
lifts are unique only up to the expected identification, and
contractibility of the lift type is a displayed-univalence condition
on `D`, not a theorem. `is-cartesian` is a proposition (a Π of
`is-equiv`s), but `is-fibration` as stated is structure. The
house discipline of "a canonical type is contractible" applies to
spines, not to lifts.

```agda
module cartesian {o h o' h'} {C : category o h} (D : categoryᴰ C o' h') where
  open category C
  open theory C
  open categoryᴰ D
  open theoryᴰ D

  is-cartesian
    : ∀ {x y} {f : hom x y} {x' y'} → hom[ f ] x' y'
    → Type (o ⊔ h ⊔ o' ⊔ h')
  is-cartesian {x = x} {x' = x'} f' =
    ∀ {w} (a : hom w x) {w' : ob[ w ]}
    → is-equiv (λ (a' : hom[ a ] w' x') → post[ f' ] a')

  is-cocartesian
    : ∀ {x y} {f : hom x y} {x' y'} → hom[ f ] x' y'
    → Type (o ⊔ h ⊔ o' ⊔ h')
  is-cocartesian {y = y} {y' = y'} f' =
    ∀ {v} (b : hom y v) {v' : ob[ v ]}
    → is-equiv (λ (b' : hom[ b ] y' v') → pre[ f' ] b')

  idn-cartesian : ∀ {x} (x' : ob[ x ]) → is-cartesian idn[ x' ]
  idn-cartesian x' a {w'} =
    transport
      (λ i → is-equiv (λ (a' : hom[ a ] w' x') → absorb-rᴰ a' (~ i)))
      id-equiv

  cartesian-lift : ∀ {x y} (f : hom x y) (y' : ob[ y ]) → Type (o ⊔ h ⊔ o' ⊔ h')
  cartesian-lift {x = x} f y' = Σ x' ∶ ob[ x ] , Σ f' ∶ hom[ f ] x' y' , is-cartesian f'

  is-fibration : Type (o ⊔ h ⊔ o' ⊔ h')
  is-fibration = ∀ {x y} (f : hom x y) (y' : ob[ y ]) → cartesian-lift f y'
```
