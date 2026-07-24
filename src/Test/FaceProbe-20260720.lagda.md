Probe: the displayed unitor-face cost asymmetry. `face-σ̂r` (830 ms)
vs `face-σ̂l` (194 ms) vs monoidal mates (≤134 ms). Isolates the
whisker lines from the `is-prop→SquareP` fills, with a control fill
whose bottom is a `repr-σᴰ[_]`-instance at the whisker base path
instead of the whisker term.

```agda
{-# OPTIONS --safe --erased-cubical --no-guardedness #-}

module Test.FaceProbe-20260720 where

open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Kan
open import Core.Transport.Properties using (is-prop→SquareP)
open import Core.Transport.J using (subst)

open import Cat.Depreciated.Type
open import Cat.Depreciated.Base
open import Cat.Depreciated.Coherence
open import Cat.Depreciated.Displayed
open import Cat.Depreciated.Displayed.Base

module _ {o h o' h'} {C : category o h} (D : categoryᴰ C o' h') where
  open category C
  open theory C
  open categoryᴰ D
  open theoryᴰ D

  module _ {x y z} {f : hom x y} {g : hom y z} {x' y' z'}
    (φ : hom[ f ] x' y') (ψ : hom[ g ] y' z')
    where

    private module T = triangle C f g

    ι' : hom[ idn y ] y' y'
    ι' = idn[ y' ]

    Ûf : is-representable[ T.Uf ] (emb[ φ ])
    Ûf = (nrm[ φ ] ●ᴰ nrm[ ι' ]) ↝ᴰ ▾-idnᴰ (emb[ φ ])

    V̂g : is-representable[ T.Vg ] (emb[ ψ ])
    V̂g = (nrm[ ι' ] ●ᴰ nrm[ ψ ]) ↝ᴰ emb-idn-absorbᴰ ψ

    ŝ₀ : is-representable[ T.s₀ ] (emb[ φ ] ▿ᴰ emb[ ψ ])
    ŝ₀ = nrm[ φ ] ●ᴰ nrm[ ψ ]

    ŝl : is-representable[ T.sl ] (emb[ φ ] ▿ᴰ emb[ ψ ])
    ŝl = nrm[ φ ] ●ᴰ V̂g

    ŝr : is-representable[ T.sr ] (emb[ φ ] ▿ᴰ emb[ ψ ])
    ŝr = Ûf ●ᴰ nrm[ ψ ]

    -- the whisker lines alone
    right-line
      : PathP (λ i → is-representable[ unitr-σ● f i ● nrm g ]
                       (emb[ φ ] ▿ᴰ emb[ ψ ]))
              ŝr ŝ₀
    right-line i = unitr-σ●ᴰ φ i ●ᴰ nrm[ ψ ]

    left-line
      : PathP (λ i → is-representable[ nrm f ● unitl-σ● g i ]
                       (emb[ φ ] ▿ᴰ emb[ ψ ]))
              ŝl ŝ₀
    left-line i = nrm[ φ ] ●ᴰ unitl-σ●ᴰ ψ i

    -- the σ̂ tops
    σ̂ᵣ₀ : PathP (λ i → is-representable[ T.σᵣ₀ i ]
                         (emb[ φ ] ▿ᴰ emb[ ψ ]))
                ŝr ŝ₀
    σ̂ᵣ₀ = repr-σᴰ[ T.σᵣ₀ ] ŝr ŝ₀

    σ̂ₗ₀ : PathP (λ i → is-representable[ T.σₗ₀ i ]
                         (emb[ φ ] ▿ᴰ emb[ ψ ]))
                ŝl ŝ₀
    σ̂ₗ₀ = repr-σᴰ[ T.σₗ₀ ] ŝl ŝ₀

    private
      wit-prop-r
        : (m i : I)
        → is-prop (is-representable[ T.face-σr m i ]
                     (emb[ φ ] ▿ᴰ emb[ ψ ]))
      wit-prop-r m i =
        is-contr→is-prop
          (subst is-contr
            (λ k → is-representable[ T.face-σr (m ∧ k) (i ∧ k) ]
                     (emb[ φ ] ▿ᴰ emb[ ψ ]))
            (repr-contrᴰ ŝr))

      wit-prop-l
        : (m i : I)
        → is-prop (is-representable[ T.face-σl m i ]
                     (emb[ φ ] ▿ᴰ emb[ ψ ]))
      wit-prop-l m i =
        is-contr→is-prop
          (subst is-contr
            (λ k → is-representable[ T.face-σl (m ∧ k) (i ∧ k) ]
                     (emb[ φ ] ▿ᴰ emb[ ψ ]))
            (repr-contrᴰ ŝl))

    -- the fills at the whisker bottoms (face-σ̂r/face-σ̂l verbatim)
    sq-r
      : PathP (λ m → PathP (λ i → is-representable[ T.face-σr m i ]
                                    (emb[ φ ] ▿ᴰ emb[ ψ ]))
                     ŝr ŝ₀)
              σ̂ᵣ₀ right-line
    sq-r = is-prop→SquareP wit-prop-r σ̂ᵣ₀ refl right-line refl

    sq-l
      : PathP (λ m → PathP (λ i → is-representable[ T.face-σl m i ]
                                    (emb[ φ ] ▿ᴰ emb[ ψ ]))
                     ŝl ŝ₀)
              σ̂ₗ₀ left-line
    sq-l = is-prop→SquareP wit-prop-l σ̂ₗ₀ refl left-line refl

    -- control: the same fill with a σ[_]-instance bottom in place
    -- of the whisker term
    ctrl-bottom
      : PathP (λ i → is-representable[ unitr-σ● f i ● nrm g ]
                       (emb[ φ ] ▿ᴰ emb[ ψ ]))
              ŝr ŝ₀
    ctrl-bottom = repr-σᴰ[ (λ i → unitr-σ● f i ● nrm g) ] ŝr ŝ₀

    sq-ctrl
      : PathP (λ m → PathP (λ i → is-representable[ T.face-σr m i ]
                                    (emb[ φ ] ▿ᴰ emb[ ψ ]))
                     ŝr ŝ₀)
              σ̂ᵣ₀ ctrl-bottom
    sq-ctrl = is-prop→SquareP wit-prop-r σ̂ᵣ₀ refl ctrl-bottom refl

    -- the inline form, verbatim as in triangleᴰ.face-σ̂r
    sq-r-inline
      : PathP (λ m → PathP (λ i → is-representable[ T.face-σr m i ]
                                    (emb[ φ ] ▿ᴰ emb[ ψ ]))
                     ŝr ŝ₀)
              σ̂ᵣ₀
              (λ i → unitr-σ●ᴰ φ i ●ᴰ nrm[ ψ ])
    sq-r-inline =
      is-prop→SquareP wit-prop-r
        σ̂ᵣ₀ refl
        (λ i → unitr-σ●ᴰ φ i ●ᴰ nrm[ ψ ]) refl

    -- the inline left form, verbatim as in triangleᴰ.face-σ̂l
    sq-l-inline
      : PathP (λ m → PathP (λ i → is-representable[ T.face-σl m i ]
                                    (emb[ φ ] ▿ᴰ emb[ ψ ]))
                     ŝl ŝ₀)
              σ̂ₗ₀
              (λ i → nrm[ φ ] ●ᴰ unitl-σ●ᴰ ψ i)
    sq-l-inline =
      is-prop→SquareP wit-prop-l
        σ̂ₗ₀ refl
        (λ i → nrm[ φ ] ●ᴰ unitl-σ●ᴰ ψ i) refl
```
