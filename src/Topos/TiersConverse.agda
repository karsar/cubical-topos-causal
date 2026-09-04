{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.TiersConverse — the converse directions of the tier
-- characterization.  With Topos.AbstractionTiers this closes
-- the iff, constructively:
--
--   BackCond∥  ⇒  φB Heyting  ⇒  φB injective  ⇒  BackCond∥
--   ReflectAt c  ⇔  φB surjective at c
--
-- Hypotheses, direction by direction:
--   heyting⇒inj    : none.  Commuting with implication forces
--                    injectivity for EVERY base functor,
--                    because φB reflects ⊤ through App-id.
--   inj⇒back∥      : D thin and antisymmetric.  Injectivity
--                    identifies the principal sieve at h with
--                    its image-generated part; evaluating at h
--                    yields a mere lift.
--   surj⇒reflect   : C and D thin.  Surjectivity onto the
--                    principal fine sieve at gy turns a coarse
--                    arrow into a fine one.
--
-- The lift in inj⇒back∥ is merely-existent, and that is the
-- constructive content: the converse holds with no choice and
-- no excluded middle, and BackCond∥ is exactly what Tier 1
-- consumes.
-- ============================================================

module Topos.TiersConverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)

open import Topos.Cat
open import Topos.Omega
open import Topos.BaseChange
open import Topos.AbstractionTiers using (ReflectAt)
open import Topos.DoubleNegation using (_⇒S_)

-- ------------------------------------------------------------
-- Sieve lemmas over any square-level base.
-- ------------------------------------------------------------
private
  module SieveLemmas {ℓ} (E : Precategory ℓ ℓ) where
    private module Ec = Precategory E

    -- A sieve containing the identity is maximal.
    idn-maximal : {w : Ec.Ob} (S : Sieve {C = E} w)
                → fst (fst S w Ec.idn) → S ≡ maximal {C = E} w
    idn-maximal {w} S s = Sieve≡ {C = E} S (maximal {C = E} w)
      (funExt λ b → funExt λ u → ⇔toPath (λ _ → tt*)
        (λ _ → subst (λ v → fst (fst S b v)) (Ec.⋆-idR u)
                     (snd S w b u Ec.idn s)))

    -- Self-implication is maximal.
    refl-⇒-maximal : {w : Ec.Ob} (X : Sieve {C = E} w)
                   → _⇒S_ {C = E} {c = w} X X ≡ maximal {C = E} w
    refl-⇒-maximal {w} X = Sieve≡ {C = E} _ _
      (funExt λ b → funExt λ u →
        ⇔toPath (λ _ → tt*) (λ _ e g m → m))

    -- A maximal implication gives pointwise entailment.
    ⇒max→≤ : {w : Ec.Ob} (S T : Sieve {C = E} w)
           → _⇒S_ {C = E} {c = w} S T ≡ maximal {C = E} w
           → (b : Ec.Ob) (u : Ec.Hom b w)
           → fst (fst S b u) → fst (fst T b u)
    ⇒max→≤ {w} S T q b u m =
      subst (λ v → fst (fst T b v)) (Ec.⋆-idL u)
        (imp b Ec.idn
          (subst (λ v → fst (fst S b v)) (sym (Ec.⋆-idL u)) m))
      where
      imp : (e : Ec.Ob) (g : Ec.Hom e b)
          → fst (fst S e (g Ec.⋆ u)) → fst (fst T e (g Ec.⋆ u))
      imp = transport (λ i → fst (fst (q (~ i)) b u)) tt*

module _ {ℓ} {C D : Precategory ℓ ℓ} (F : BaseFunctor C D) where
  private
    module Cc = Precategory C
    module Dc = Precategory D
    module LC = SieveLemmas C
    module LD = SieveLemmas D
  open BaseFunctor F

  -- ----------------------------------------------------------
  -- φB reflects ⊤: forcing reads the identity, and App-id
  -- matches the identities.
  -- ----------------------------------------------------------
  φB-⊤-reflect : (c : Cc.Ob) (S : Sieve {C = D} (App₀ c))
               → φB F c S ≡ maximal {C = C} c
               → S ≡ maximal {C = D} (App₀ c)
  φB-⊤-reflect c S p = LD.idn-maximal S
    (subst (λ v → fst (fst S (App₀ c) v)) (App-id c)
      (transport (λ i → fst (fst (p (~ i)) c Cc.idn)) tt*))

  -- ----------------------------------------------------------
  -- CONVERSE 1.  Commuting with implication forces injectivity.
  -- No hypothesis on F or on the bases.
  -- ----------------------------------------------------------
  heyting⇒inj : (c : Cc.Ob)
    → ((S T : Sieve {C = D} (App₀ c))
        → φB F c (_⇒S_ {C = D} {c = App₀ c} S T)
        ≡ _⇒S_ {C = C} {c = c} (φB F c S) (φB F c T))
    → (S T : Sieve {C = D} (App₀ c)) → φB F c S ≡ φB F c T → S ≡ T
  heyting⇒inj c hey S T p = Sieve≡ {C = D} S T
      (funExt λ b → funExt λ u → ⇔toPath
        (LD.⇒max→≤ S T ST-max b u)
        (LD.⇒max→≤ T S TS-max b u))
    where
    ST-max : _⇒S_ {C = D} {c = App₀ c} S T ≡ maximal {C = D} (App₀ c)
    ST-max = φB-⊤-reflect c _
      (hey S T
       ∙ cong (λ Z → _⇒S_ {C = C} {c = c} Z (φB F c T)) p
       ∙ LC.refl-⇒-maximal (φB F c T))
    TS-max : _⇒S_ {C = D} {c = App₀ c} T S ≡ maximal {C = D} (App₀ c)
    TS-max = φB-⊤-reflect c _
      (hey T S
       ∙ cong (λ Z → _⇒S_ {C = C} {c = c} (φB F c T) Z) p
       ∙ LC.refl-⇒-maximal (φB F c T))

  -- ----------------------------------------------------------
  -- CONVERSE 2.  Injectivity yields mere lifts, over a thin
  -- antisymmetric D.
  -- ----------------------------------------------------------
  module _ (thinD : (x y : Dc.Ob) → isProp (Dc.Hom x y))
           (antisymD : (x y : Dc.Ob) → Dc.Hom x y → Dc.Hom y x → x ≡ y) where

    inj⇒back∥ : (c : Cc.Ob)
      → ((S T : Sieve {C = D} (App₀ c)) → φB F c S ≡ φB F c T → S ≡ T)
      → (d' : Dc.Ob) (h : Dc.Hom d' (App₀ c))
      → ∥ Σ[ e' ∈ Cc.Ob ] Σ[ k ∈ Cc.Hom e' c ] (App₀ e' ≡ d') ∥₁
    inj⇒back∥ c inj d' h =
      PT.map (λ { (e'' , g'' , m₁ , m₂) → e'' , g'' , antisymD _ _ m₂ m₁ })
             (transport (λ i → fst (fst (inj P Q φP≡φQ i) d' h)) Dc.idn)
      where
      -- The principal sieve at h.  Thinness makes the
      -- membership independent of the arrow.
      P : Sieve {C = D} (App₀ c)
      P = (λ b u → Dc.Hom b d' , thinD b d')
        , (λ b e k u m → k Dc.⋆ m)
      -- Its image-generated part.
      Q : Sieve {C = D} (App₀ c)
      Q = (λ b u → ∥ Σ[ e'' ∈ Cc.Ob ] Σ[ g'' ∈ Cc.Hom e'' c ]
                      (Dc.Hom b (App₀ e'') × Dc.Hom (App₀ e'') d') ∥₁
                 , squash₁)
        , (λ b e k u → PT.map λ { (e'' , g'' , m₁ , m₂) →
                       e'' , g'' , (k Dc.⋆ m₁) , m₂ })
      -- P and Q always have the same preimage.
      φP≡φQ : φB F c P ≡ φB F c Q
      φP≡φQ = Sieve≡ {C = C} _ _ (funExt λ e' → funExt λ g' → ⇔toPath
        (λ m → ∣ e' , g' , Dc.idn , m ∣₁)
        (PT.rec (thinD (App₀ e') d')
                (λ { (e'' , g'' , m₁ , m₂) → m₁ Dc.⋆ m₂ })))

  -- ----------------------------------------------------------
  -- CONVERSE 3.  Surjectivity yields anchored reflection, over
  -- thin bases.
  -- ----------------------------------------------------------
  module _ (thinC : (x y : Cc.Ob) → isProp (Cc.Hom x y))
           (thinD : (x y : Dc.Ob) → isProp (Dc.Hom x y)) where

    surj⇒reflect : (c : Cc.Ob)
      → ((T : Sieve {C = C} c) → Σ[ S ∈ Sieve {C = D} (App₀ c) ] (φB F c S ≡ T))
      → ReflectAt F c
    surj⇒reflect c surj {x} {y} gx gy m = final
      where
      -- The principal fine sieve at gy.
      T : Sieve {C = C} c
      T = (λ e g → Cc.Hom e y , thinC e y)
        , (λ e e' k g w → k Cc.⋆ w)
      S = fst (surj T)
      p = snd (surj T)
      sy : fst (fst S (App₀ y) (App₁ gy))
      sy = transport (λ i → fst (fst (p (~ i)) y gy)) Cc.idn
      sx : fst (fst S (App₀ x) (App₁ gx))
      sx = subst (λ v → fst (fst S (App₀ x) v))
                 (thinD (App₀ x) (App₀ c) (m Dc.⋆ App₁ gy) (App₁ gx))
                 (snd S (App₀ y) (App₀ x) m (App₁ gy) sy)
      final : Cc.Hom x y
      final = transport (λ i → fst (fst (p i) x gx)) sx
