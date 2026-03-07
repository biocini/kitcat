Equivalence properties: symmetry, composition, Sigma equivalences,
bi-invertible maps, half-adjoint equivalences, and the three-for-two
property.

```agda

{-# OPTIONS --safe --erased-cubical --no-guardedness --no-sized-types #-}

module Core.Equiv.Properties where

open import Core.Equiv.Base public
open import Core.Transport.Base
open import Core.Transport.J
open import Core.Transport.Properties
  using (is-contr→loop-is-refl; transport⁻-transport;
        is-contr-is-prop; is-contr-×; weak-funext)
open import Core.Type
open import Core.Base
open import Core.Data.Sigma
open import Core.Data.Empty
open import Core.Kan
open import Core.Sub

esym : ∀ {u v} {A : Type u} {B : Type v} -> A ≃ B -> B ≃ A
esym e = iso→equiv E.inv E.fwd E.counit E.unit where module E = Equiv e

sym-equiv : ∀ {u v} {A : Type u} {B : Type v} {f : A -> B}
          -> (e : is-equiv f) -> is-equiv (eqvtoinv (f , e))
sym-equiv {f} e = esym (f , e) .snd

_∙e_
  : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
  -> A ≃ B -> B ≃ C -> A ≃ C
_∙e_ {A = A} {B} {C} e f = iso→equiv fwd bwd sec retr where
  module E = Equiv e
  module F = Equiv f

  fwd : A -> C
  fwd a = F.fwd (E.fwd a)

  bwd : C -> A
  bwd c = E.inv (F.inv c)

  sec : (a : A) -> bwd (fwd a) ≡ a
  sec a = ap E.inv (F.unit (E.fwd a)) ∙ E.unit a

  retr : (c : C) -> fwd (bwd c) ≡ c
  retr c = ap F.fwd (E.counit (F.inv c)) ∙ F.counit c

infixr 9 _∙e_

comp-equiv
  : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w} {f : A -> B} {g : B -> C}
  -> is-equiv f -> is-equiv g -> is-equiv (g ∘ f)
comp-equiv {f} {g} e d = ((f , e) ∙e (g , d)) .snd

Σ-×-swap
  : ∀ {u v w z} {A : Type u} {B : Type v} {P : A -> Type w} {Q : B -> Type z}
  -> (Σ (s₁ , s₂) ∶ A × B , P s₁ × Q s₂) ≃ ((Σ P) × (Σ Q))
Σ-×-swap {A = A} {B} {P} {Q} = iso→equiv fwd bwd (λ _ -> refl) (λ _ -> refl) where
  fwd : (Σ (s₁ , s₂) ∶ A × B , P s₁ × Q s₂) -> (Σ P) × (Σ Q)
  fwd ((s₁ , s₂) , (p , q)) = (s₁ , p) , (s₂ , q)

  bwd : (Σ P) × (Σ Q) -> (Σ (s₁ , s₂) ∶ A × B , P s₁ × Q s₂)
  bwd ((s₁ , p) , (s₂ , q)) = (s₁ , s₂) , (p , q)

×-Σ-swap
  : ∀ {u v w z} {A : Type u} {B : Type v} {P : A -> Type w} {Q : B -> Type z}
  -> ((Σ P) × (Σ Q)) ≃ (Σ (s₁ , s₂) ∶ A × B , P s₁ × Q s₂)
×-Σ-swap {A = A} {B} {P} {Q} = iso→equiv fwd bwd (λ _ -> refl) (λ _ -> refl) where
  fwd : (Σ P) × (Σ Q) -> (Σ (s₁ , s₂) ∶ A × B , P s₁ × Q s₂)
  fwd ((s₁ , p) , (s₂ , q)) = (s₁ , s₂) , (p , q)

  bwd : (Σ (s₁ , s₂) ∶ A × B , P s₁ × Q s₂) -> (Σ P) × (Σ Q)
  bwd ((s₁ , s₂) , (p , q)) = (s₁ , p) , (s₂ , q)

Σ-equiv-snd
  : ∀ {u v w} {A : Type u} {P : A -> Type v} {Q : A -> Type w}
  -> (∀ a -> P a ≃ Q a) -> Σ P ≃ Σ Q
Σ-equiv-snd {A = A} {P} {Q} e = iso→equiv fwd bwd sec retr where
  fwd : Σ P -> Σ Q
  fwd (a , p) = a , e a .fst p

  bwd : Σ Q -> Σ P
  bwd (a , q) = a , Equiv.inv (e a) q

  sec : (x : Σ P) -> bwd (fwd x) ≡ x
  sec (a , p) = ap (a ,_) (Equiv.unit (e a) p)

  retr : (x : Σ Q) -> fwd (bwd x) ≡ x
  retr (a , q) = ap (a ,_) (Equiv.counit (e a) q)

×-path-equiv
  : ∀ {u v} {A : Type u} {B : Type v} {x y : A × B}
  -> (x ≡ y) ≃ ((x .fst ≡ y .fst) × (x .snd ≡ y .snd))
×-path-equiv {x = x} {y} = iso→equiv fwd bwd (λ _ -> refl) (λ _ -> refl) where
  fwd : x ≡ y -> (x .fst ≡ y .fst) × (x .snd ≡ y .snd)
  fwd p = ap fst p , ap snd p

  bwd : (x .fst ≡ y .fst) × (x .snd ≡ y .snd) -> x ≡ y
  bwd (p , q) i = p i , q i

Σ-fiber-swap
  : ∀ {u v w z} {A : Type u} {B : Type v} {C : Type w} {D : Type z}
    {f : A -> C} {g : B -> D} {α : C} {α' : D}
  -> (Σ (β , β') ∶ A × B , (f β , g β') ≡ (α , α'))
    ≃ ((Σ β ∶ A , f β ≡ α) × (Σ β' ∶ B , g β' ≡ α'))
Σ-fiber-swap = Σ-equiv-snd (λ _ -> ×-path-equiv) ∙e Σ-×-swap

Σ-assoc
  : ∀ {u v w} {A : Type u} {B : A -> Type v} {C : (a : A) -> B a -> Type w}
  -> (Σ a ∶ A , Σ b ∶ B a , C a b) ≃ (Σ ab ∶ (Σ B) , C (ab .fst) (ab .snd))
Σ-assoc = iso→equiv (λ (a , b , c) -> (a , b) , c)
                    (λ ((a , b) , c) -> a , b , c)
                    (λ _ -> refl) (λ _ -> refl)

-- Product commutativity - not needed for the idem-is-prop proof
-- (kept for reference but not exported)

contr-equiv-⊤ : ∀ {u} {A : Type u} -> is-contr A -> A ≃ ⊤
contr-equiv-⊤ c = iso→equiv (λ _ -> tt) (λ _ -> c .center)
                            (λ a -> c .paths a) (λ { tt -> refl })

Σ-⊤-≃ : ∀ {v} {B : ⊤ -> Type v} -> Σ B ≃ B tt
Σ-⊤-≃ = iso→equiv (λ { (tt , b) -> b }) (λ b -> tt , b) (λ _ -> refl) (λ _ -> refl)

Σ-contr-fst : ∀ {u v} {A : Type u} {B : A -> Type v}
            -> (c : is-contr A) -> Σ B ≃ B (c .center)
Σ-contr-fst {B = B} c = iso→equiv fwd bwd sec retr
  where
    fwd : Σ B -> B (c .center)
    fwd (a , b) = subst B (sym (c .paths a)) b
    bwd : B (c .center) -> Σ B
    bwd b = c .center , b
    sec : (x : Σ B) -> bwd (fwd x) ≡ x
    sec (a , b) i = c .paths a i , q i
      where
        q : PathP (λ i -> B (c .paths a i)) (subst B (sym (c .paths a)) b) b
        q = Path-over.to-pathp (transport⁻-transport (ap B (c .paths a)) b)
    retr : (y : B (c .center)) -> fwd (bwd y) ≡ y
    retr y =
      ap (λ p -> subst B (sym p) y) (is-contr→loop-is-refl c) ∙ transport-refl y

path-equiv-r : ∀ {u} {A : Type u} {x y z : A}
             -> y ≡ z -> (x ≡ y) ≃ (x ≡ z)
path-equiv-r {x = x} {y} {z} p = iso→equiv fwd bwd sec retr
  where
    fwd : x ≡ y -> x ≡ z
    fwd q = q ∙ p

    bwd : x ≡ z -> x ≡ y
    bwd q = q ∙ sym p

    sec : (q : x ≡ y) -> bwd (fwd q) ≡ q
    sec q = pcom (Path.assoc q p (sym p)) (ap (q ∙_) (Path.invr p)) (Path.unitr q)

    retr : (q : x ≡ z) -> fwd (bwd q) ≡ q
    retr q = pcom (Path.assoc q (sym p) p) (ap (q ∙_) (Path.invl p)) (Path.unitr q)

path-sym-equiv : ∀ {u} {A : Type u} {x y : A} -> (x ≡ y) ≃ (y ≡ x)
path-sym-equiv = iso→equiv sym sym (λ _ -> refl) (λ _ -> refl)

has-section : ∀ {u v} {A : Type u} {B : Type v} -> (A -> B) -> Type (u ⊔ v)
has-section {A = A} {B = B} f = Σ g ∶ (B -> A) , ((b : B) -> f (g b) ≡ b)

has-retraction : ∀ {u v} {A : Type u} {B : Type v} -> (A -> B) -> Type (u ⊔ v)
has-retraction {A = A} {B = B} f = Σ h ∶ (B -> A) , ((a : A) -> h (f a) ≡ a)

is-bi-inv : ∀ {u v} {A : Type u} {B : Type v} -> (A -> B) -> Type (u ⊔ v)
is-bi-inv f = has-section f × has-retraction f

```

## Bi-invertible maps and equivalences

Following Rijke, we show that bi-invertible maps are equivalent to our
notion of equivalence (contractible fibers). Having both a section and
retraction is logically equivalent to being a quasi-inverse, which in
turn implies having contractible fibers.

```agda


qinv→bi-inv : ∀ {u v} {A : Type u} {B : Type v} {f : A -> B}
            -> is-qinv f -> is-bi-inv f
qinv→bi-inv {f = f} q = (g , ε) , (g , η)
  where
  open is-qinv q renaming (sec to η; retr to ε)
  g = is-qinv.inv q


bi-inv→qinv : ∀ {u v} {A : Type u} {B : Type v} {f : A -> B}
            -> is-bi-inv f -> is-qinv f
bi-inv→qinv {f = f} ((g , ε) , (h , η)) = qi
  where
  g' : _ -> _
  g' = h ∘ f ∘ g

  sec' : ∀ x -> g' (f x) ≡ x
  sec' x = ap h (ε (f x)) ∙ η x

  retr' : ∀ y -> f (g' y) ≡ y
  retr' y = ap f (η (g y)) ∙ ε y

  qi : is-qinv f
  qi .is-qinv.inv = g'
  qi .is-qinv.sec = sec'
  qi .is-qinv.retr = retr'


bi-inv→equiv : ∀ {u v} {A : Type u} {B : Type v} {f : A -> B}
             -> is-bi-inv f -> is-equiv f
bi-inv→equiv bi = qinv.to-equiv (bi-inv→qinv bi)


equiv→bi-inv : ∀ {u v} {A : Type u} {B : Type v} {f : A -> B}
             -> is-equiv f -> is-bi-inv f
equiv→bi-inv {f = f} e = (g , counit) , (g , unit)
  where
  module E = Equiv (_ , e)
  g = E.inv
  unit = E.unit
  counit = E.counit



has-section-is-contr
  : ∀ {u v} {A : Type u} {B : Type v} {f : A -> B}
  -> is-equiv f -> is-contr (has-section f)
has-section-is-contr {f = f} e = is-contr-equiv section≃Π-fiber Π-fiber-contr
  where
  section≃Π-fiber : has-section f ≃ ((y : _) -> fiber f y)
  section≃Π-fiber = iso→equiv fwd bwd (λ _ -> refl) (λ _ -> refl)
    where
    fwd : has-section f -> (y : _) -> fiber f y
    fwd (g , ε) y = g y , ε y

    bwd : ((y : _) -> fiber f y) -> has-section f
    bwd h = (λ y -> h y .fst) , (λ y -> h y .snd)

  Π-fiber-contr : is-contr ((y : _) -> fiber f y)
  Π-fiber-contr = weak-funext (λ y -> e .eqv-fibers y)


private
  precomp-right : ∀ {u v} {A : Type u} {B : Type v}
                -> (f : A -> B) -> (B -> A) -> (A -> A)
  precomp-right f h = h ∘ f

precomp-right-is-equiv
  : ∀ {u v} {A : Type u} {B : Type v}
  -> (e : A ≃ B) -> is-equiv (precomp-right (e .fst))
precomp-right-is-equiv {A = A} {B} e = bi-inv→equiv bi
  where
  module E = Equiv e

  preinv : (A -> A) -> (B -> A)
  preinv g = g ∘ E.inv

  sec : (g : A -> A) -> precomp-right E.fwd (preinv g) ≡ g
  sec g = funext λ a -> ap g (E.unit a)

  retr : (h : B -> A) -> preinv (precomp-right E.fwd h) ≡ h
  retr h = funext λ b -> ap h (E.counit b)

  bi : is-bi-inv (precomp-right E.fwd)
  bi = (preinv , sec) , (preinv , retr)

private
  has-retraction-equiv-fiber
    : ∀ {u v} {A : Type u} {B : Type v} {f : A -> B}
    -> has-retraction f ≃ fiber (precomp-right f) id
  has-retraction-equiv-fiber {f = f} = iso→equiv fwd bwd sec retr
    where
    fwd : has-retraction f -> fiber (precomp-right f) id
    fwd (h , η) = h , funext η

    bwd : fiber (precomp-right f) id -> has-retraction f
    bwd (h , p) = h , happly p

    sec : (x : has-retraction f) -> bwd (fwd x) ≡ x
    sec (h , η) = refl

    retr : (x : fiber (precomp-right f) id) -> fwd (bwd x) ≡ x
    retr (h , p) = refl

-- Credit: 1lab
has-retraction-is-contr
  : ∀ {u v} {A : Type u} {B : Type v} {f : A -> B}
  -> is-equiv f -> is-contr (has-retraction f)
has-retraction-is-contr {f = f} e =
  is-contr-equiv has-retraction-equiv-fiber
                  (precomp-right-is-equiv (f , e) .eqv-fibers id)


is-bi-inv-is-contr
  : ∀ {u v} {A : Type u} {B : Type v} {f : A -> B}
  -> is-equiv f -> is-contr (is-bi-inv f)
is-bi-inv-is-contr e = is-contr-× (has-section-is-contr e) (has-retraction-is-contr e)

is-bi-inv-is-prop
  : ∀ {u v} {A : Type u} {B : Type v} {f : A -> B}
  -> is-equiv f -> is-prop (is-bi-inv f)
is-bi-inv-is-prop e = is-contr→is-prop (is-bi-inv-is-contr e)


is-equiv-is-prop : ∀ {u v} {A : Type u} {B : Type v} (f : A -> B)
                 -> is-prop (is-equiv f)
is-equiv-is-prop f e1 e2 i .eqv-fibers y =
  is-contr-is-prop _ (e1 .eqv-fibers y) (e2 .eqv-fibers y) i

equiv-path
  : ∀ {u v} {A : Type u} {B : Type v}
  -> (e f : A ≃ B) -> e .fst ≡ f .fst -> e ≡ f
equiv-path e f p i .fst = p i
equiv-path e f p i .snd = is-prop→PathP (λ i -> is-equiv-is-prop (p i))
  (e .snd) (f .snd) i

∙e-unitl : ∀ {u v} {A : Type u} {B : Type v} (e : A ≃ B) -> aut ∙e e ≡ e
∙e-unitl e i .fst = e .fst
∙e-unitl e i .snd = is-prop→PathP (λ i -> is-equiv-is-prop (e .fst))
                                  ((aut ∙e e) .snd) (e .snd) i

∙e-unitr : ∀ {u v} {A : Type u} {B : Type v} (e : A ≃ B) -> e ∙e aut ≡ e
∙e-unitr e i .fst = e .fst
∙e-unitr e i .snd = is-prop→PathP (λ i -> is-equiv-is-prop (e .fst))
                                  ((e ∙e aut ) .snd) (e .snd) i

is-bi-inv≃is-equiv : ∀ {u v} {A : Type u} {B : Type v} {f : A -> B}
                   -> is-bi-inv f ≃ is-equiv f
is-bi-inv≃is-equiv {f = f} = iso→equiv fwd bwd fwd-bwd bwd-fwd
  where
  fwd : is-bi-inv f -> is-equiv f
  fwd = bi-inv→equiv

  bwd : is-equiv f -> is-bi-inv f
  bwd = equiv→bi-inv

  fwd-bwd : ∀ bi -> bwd (fwd bi) ≡ bi
  fwd-bwd bi = is-bi-inv-is-prop (fwd bi) _ _

  bwd-fwd : ∀ e -> fwd (bwd e) ≡ e
  bwd-fwd e = is-equiv-is-prop f _ _

-- From 1lab: this helper is for functions f, g that cancel each other, up to
-- definitional equality, without any case analysis on the argument:
strict-fibers
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A -> B}
  -> (g : B -> A) (b : B)
  -> Σ f0 ∶ fiber f (f (g b))
    , ((f1 : fiber f b)
      -> Path (fiber f (f (g b))) f0 (g (f (f1 .fst)) , ap (f ∘ g) (f1 .snd)))
strict-fibers {f = f} g b .fst = (g b , refl)
strict-fibers {f = f} g b .snd (a , p) i =
  (g (p (~ i)) , λ j -> f (g (p (~ i ∨ j))))

```

## Equivalence algebra

Following Rijke, we develop the algebra of equivalences: half-adjoint
equivalences, the three-for-two properties, and the fiber characterization
of the total space map.

### Half-adjoint equivalences

A half-adjoint equivalence is a quasi-inverse equipped with the coherence
condition that the section and retraction homotopies are related by the
action of `f`. This is the data that naturally arises from contractible fibers.

```agda

record is-half-adj {u v} {A : Type u} {B : Type v} (f : A -> B) : Type (u ⊔ v) where
  no-eta-equality
  field
    inv : B -> A
    sec : (x : A) -> inv (f x) ≡ x
    retr : (y : B) -> f (inv y) ≡ y
    adj : (x : A) -> ap f (sec x) ≡ retr (f x)

open is-half-adj
{-# INLINE is-half-adj.constructor #-}


-- Credit: 1lab
is-equiv→is-half-adj
  : ∀ {u v} {A : Type u} {B : Type v} {f : A -> B}
  -> is-equiv f -> is-half-adj f
is-equiv→is-half-adj {f = f} e = ha where
  q : is-qinv f
  q = bi-inv→qinv (equiv→bi-inv e)

  g = q .is-qinv.inv
  ε = q .is-qinv.retr

  ha : is-half-adj f
  ha .inv = g
  ha .sec x = qinv.unit q (x , refl)
  ha .retr = ε
  ha .adj x = qinv.adj q (x , refl)


is-half-adj→is-equiv
  : ∀ {u v} {A : Type u} {B : Type v} {f : A -> B}
  -> is-half-adj f -> is-equiv f
is-half-adj→is-equiv h = qinv.to-equiv (qinv _ (h .inv) (h .sec) (h .retr))

```

### Three-for-two properties

The three-for-two property states: given composable maps f and g, if any
two of {f, g, g ∘ f} are equivalences, then so is the third.

We have closure under composition already via `_∙e_`. The remaining two
properties are:

- If g and g ∘ f are equivalences, then f is an equivalence
- If f and g ∘ f are equivalences, then g is an equivalence

```agda

-- Credit: Rijke, Theorem 10.1.1
3-for-2-left
  : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
  -> {f : A -> B} {g : B -> C}
  -> is-equiv g -> is-equiv (g ∘ f) -> is-equiv f
3-for-2-left {f = f} {g} eg egf = fwd-equiv .snd
  where
  module G = Equiv (g , eg)
  module GF = Equiv (g ∘ f , egf)

  fwd-equiv : _ ≃ _
  fwd-equiv = iso→equiv f (GF.inv ∘ g) GF.unit retr'
    where
    retr' : (y : _) -> f (GF.inv (g y)) ≡ y
    retr' y = sym (G.unit (f (GF.inv (g y)))) ∙ ap G.inv (GF.counit (g y)) ∙ G.unit y


-- Credit: Rijke, Theorem 10.1.1
3-for-2-right
  : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
  -> {f : A -> B} {g : B -> C}
  -> is-equiv f -> is-equiv (g ∘ f) -> is-equiv g
3-for-2-right {f = f} {g} ef egf = fwd-equiv .snd
  where
  module F = Equiv (f , ef)
  module GF = Equiv (g ∘ f , egf)

  fwd-equiv : _ ≃ _
  fwd-equiv = iso→equiv g (f ∘ GF.inv) sec' GF.counit
    where
    sec' : (y : _) -> f (GF.inv (g y)) ≡ y
    sec' y = ap f (ap GF.inv (ap g (sym (F.counit y))) ∙ GF.unit (F.inv y)) ∙ F.counit y

```

### Fiber of the total space map

Given a fiberwise function `f : (x : A) -> B x -> C x`, the total space map
`tot f : Σ A B -> Σ A C` applies `f` on each fiber. Fibers of `tot f` are
equivalent to fibers of `f a` at each point.

The `tot` function is defined in Core.Data.Sigma for module organization.

```agda

-- Fiber of tot f at (a, c) is equivalent to fiber of f a at c.
-- Following Rijke, Lemma 10.1.2
-- Credit: 1lab (Equiv.Fibrewise)
--
-- NOTE: This proof is deferred - the full construction requires careful
-- handling of dependent paths. See 1lab's Equiv.Fibrewise for the complete proof.

```
