{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.Gluing — the third Mahadevan pillar: sheaf gluing of
-- independent mechanisms, made rigorous.
--
-- Mahadevan's TCM paper (arXiv:2508.08295, §6) PROMISES that
-- "local functions can be collated together to yield a unique
-- global function" via sheaf theory, but states it only as prose
-- — no theorem, and the Grothendieck-topology vocabulary it
-- introduces is never instantiated.  In a presheaf topos the
-- collation is in fact a LIMIT, computed pointwise; no topology or
-- sheafification is needed.
--
-- Here we give the limit form precisely: the PULLBACK of two
-- mechanisms p : X ⇒ Z, q : Y ⇒ Z — local data on X and on Y that
-- AGREE on the shared overlap Z — together with its universal
-- property: any cone (two mechanisms agreeing on Z) factors
-- through a UNIQUE global mechanism into the pullback.  This is the
-- "agree on overlap ⟹ unique glued section" content of gluing,
-- holding in the bare presheaf topos.
-- ============================================================

module Topos.Gluing where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSetΣ; isSet×)
open import Cubical.Data.Sigma
  using (Σ-syntax; _,_; fst; snd; _×_; ΣPathP)

open import Topos.Cat
open import Topos.PSh

module _ {ℓo ℓh} {C : Precategory ℓo ℓh} where
  open Precategory C
  open PSh

  module _ {ℓX ℓY ℓZ} {X : PSh C ℓX} {Y : PSh C ℓY} {Z : PSh C ℓZ}
           (p : Nat X Z) (q : Nat Y Z) where

    -- agreement on the overlap Z (a proposition, since F₀ Z c is a set)
    Agree : (c : Ob) → F₀ X c → F₀ Y c → Type ℓZ
    Agree c x y = fst p c x ≡ fst q c y

    PB₀ : Ob → Type (ℓ-max (ℓ-max ℓX ℓY) ℓZ)
    PB₀ c = Σ[ xy ∈ (F₀ X c × F₀ Y c) ] Agree c (fst xy) (snd xy)

    -- restriction preserves agreement, using naturality of p and q
    PB₁ : {c' c : Ob} → Hom c' c → PB₀ c → PB₀ c'
    PB₁ f ((x , y) , e) =
      (F₁ X f x , F₁ Y f y) ,
      ( snd p _ _ f x ∙ cong (F₁ Z f) e ∙ sym (snd q _ _ f y) )

    -- the pullback presheaf X ×_Z Y
    Pullback : PSh C (ℓ-max (ℓ-max ℓX ℓY) ℓZ)
    Pullback = record
      { F₀ = PB₀
      ; F₁ = PB₁
      ; F-id = λ w → ΣPathP
          ( (λ i → (F-id X (fst (fst w)) i , F-id Y (snd (fst w)) i))
          , isProp→PathP (λ i → isSetF₀ Z _ _ _) _ _ )
      ; F-comp = λ f g w → ΣPathP
          ( (λ i → (F-comp X f g (fst (fst w)) i , F-comp Y f g (snd (fst w)) i))
          , isProp→PathP (λ i → isSetF₀ Z _ _ _) _ _ )
      ; isSetF₀ = λ c → isSetΣ (isSet× (isSetF₀ X c) (isSetF₀ Y c))
                                (λ xy → isProp→isSet (isSetF₀ Z c _ _))
      }

    -- the two projections (the legs of the pullback cone)
    π₁ : Nat Pullback X
    π₁ = (λ c w → fst (fst w)) , (λ x y f w → refl)

    π₂ : Nat Pullback Y
    π₂ = (λ c w → snd (fst w)) , (λ x y f w → refl)

    -- the pullback square commutes: p ∘ π₁ = q ∘ π₂ (pointwise),
    -- which is exactly the stored agreement witness.
    square : (c : Ob) (w : PB₀ c)
           → fst p c (fst π₁ c w) ≡ fst q c (fst π₂ c w)
    square c w = snd w

    -- ----------------------------------------------------------
    -- Universal property.  A cone over (p,q) is a context A with
    -- two mechanisms a : A ⇒ X, b : A ⇒ Y agreeing on Z.  It
    -- collates to a UNIQUE global mechanism A ⇒ Pullback.
    -- ----------------------------------------------------------
    module _ {ℓA} {A : PSh C ℓA} (a : Nat A X) (b : Nat A Y)
             (comm : (c : Ob) (z : F₀ A c)
                   → fst p c (fst a c z) ≡ fst q c (fst b c z)) where

      -- existence: the mediating (glued) mechanism
      glue : Nat A Pullback
      glue =
        (λ c z → (fst a c z , fst b c z) , comm c z) ,
        (λ x y f z → ΣPathP
          ( (λ i → (snd a x y f z i , snd b x y f z i))
          , isProp→PathP (λ i → isSetF₀ Z _ _ _) _ _ ))

      -- glue recovers the two local mechanisms (the cone factors)
      glue-π₁ : (c : Ob) (z : F₀ A c) → fst π₁ c (fst glue c z) ≡ fst a c z
      glue-π₁ c z = refl

      glue-π₂ : (c : Ob) (z : F₀ A c) → fst π₂ c (fst glue c z) ≡ fst b c z
      glue-π₂ c z = refl

      -- uniqueness: any mechanism whose projections are a and b IS glue
      glue-uniq : (u : Nat A Pullback)
                → ((c : Ob) (z : F₀ A c) → fst π₁ c (fst u c z) ≡ fst a c z)
                → ((c : Ob) (z : F₀ A c) → fst π₂ c (fst u c z) ≡ fst b c z)
                → u ≡ glue
      glue-uniq u u₁ u₂ =
        Nat≡ {X = A} {Y = Pullback} u glue
          (λ c z → ΣPathP
            ( (λ i → (u₁ c z i , u₂ c z i))
            , isProp→PathP (λ i → isSetF₀ Z c _ _) _ _ ))
