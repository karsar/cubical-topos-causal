{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.MediatorObstruction — dependence is not a sieve either.
--
-- Topos.ColliderObstruction proves that conditional
-- INDEPENDENCE is not closed under restriction: conditioning on
-- a common effect opens the path between its causes.  This
-- module proves the dual.  Conditioning on a mediator closes the
-- path between the ends of a chain, so DEPENDENCE is not closed
-- under restriction either.
--
-- The base is the one Topos.ColliderObstruction builds, and the
-- supports are the same.  Only the restriction changes:
--     cond --r--> marg
-- where marg is the marginal regime and cond is the regime that
-- conditions on the middle variable of a chain X -> M -> Y.
-- Restriction along r keeps the fibre where the mediator takes
-- one value.
--
-- Together the two modules give a two-sided no-go.  A truth
-- value in the internal logic is a sieve, and a sieve is closed
-- under precomposition.  Independence fails that closure at a
-- collider and dependence fails it at a mediator, so NEITHER
-- side of the causal question is a truth value once refinement
-- may condition.  The internal logic carries persistence, and a
-- causal claim of either polarity is not persistent.
--
-- Results:
--   chain-dependent   the marginal support is not a product.
--   fibre-product     its restriction to the mediator fibre is.
--   dep-not-closed    so dependence is NOT closed under
--                     restriction on this base.
--   dep-no-sieve      hence it defines no sieve, at any context.
--
-- The practical reading matches Topos.ColliderObstruction: if
-- the refinement relation between regimes may condition on an
-- intermediate variable, a dependence claim has no internal
-- truth value, and the sieve machinery is silent about it.  The
-- condition is checkable from the study design.
-- ============================================================

module Topos.MediatorObstruction where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_; isProp¬)
open import Cubical.Data.Empty as E using (⊥; isProp⊥)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega

-- The base, the supports and the notion of a product support are
-- exactly the collider module's.  Reusing them is the point: one
-- site, two restrictions, two failures.
open import Topos.ColliderObstruction
  using ( _&&_; notB; &&-l; &&-r
        ; BObj; marg; cond; BHom; idm; idc; r; isPropBHom; idB; _⋆B_; Bv
        ; Supp; isSetSupp; IsProduct )

-- ------------------------------------------------------------
-- Equality of booleans.  The chain X -> M -> Y with both links
-- deterministic copies makes the ends agree, so the marginal
-- support is the diagonal.
-- ------------------------------------------------------------
eqB : Bool → Bool → Bool
eqB true  b = b
eqB false b = notB b

-- ------------------------------------------------------------
-- Restriction: conditioning on the mediator.  The mediator
-- copies X, so fixing it at true keeps the x = true fibre.
-- ------------------------------------------------------------
restrM : {d c : BObj} → BHom d c → Supp → Supp
restrM idm S = S
restrM idc S = S
restrM r   S = λ x y → S x y && x

SuppM : PSh Bv ℓ-zero
SuppM = record
  { F₀ = λ _ → Supp ; F₁ = restrM
  ; F-id = λ {x} S → lemId x S
  ; F-comp = λ f g S → lemComp f g S
  ; isSetF₀ = λ _ → isSetSupp }
  where
    lemId : (x : BObj) (S : Supp) → restrM (idB {x}) S ≡ S
    lemId marg S = refl
    lemId cond S = refl
    lemComp : {x y z : BObj} (f : BHom x y) (g : BHom y z) (S : Supp)
            → restrM (f ⋆B g) S ≡ restrM f (restrM g S)
    lemComp idm idm S = refl
    lemComp idc idc S = refl
    lemComp idc r   S = refl
    lemComp r   idm S = refl

-- ------------------------------------------------------------
-- Dependence: the support is NOT a product.  This is the
-- negation of the predicate Topos.ColliderObstruction tests, so
-- the two modules test the two polarities of one question.
-- ------------------------------------------------------------
Dep : (c : BObj) → Supp → hProp ℓ-zero
Dep _ S = (¬ ∥ IsProduct S ∥₁) , isProp¬ _

-- ------------------------------------------------------------
-- The marginal support of the chain: the two ends agree.
-- ------------------------------------------------------------
diagS : Supp
diagS = eqB

diag-tt : diagS true true ≡ true
diag-tt = refl

diag-tf : diagS true false ≡ false
diag-tf = refl

diag-ff : diagS false false ≡ true
diag-ff = refl

-- The agreeing cells force both factors true; the mixed cell is
-- then forced true, and it is false.
chain-not-product : ¬ (IsProduct diagS)
chain-not-product (f , g , eq) = true≢false (sym step)
  where
    ftrue : f true ≡ true
    ftrue = &&-l (f true) (g true) (sym (eq true true))
    gfalse : g false ≡ true
    gfalse = &&-r (f false) (g false) (sym (eq false false))
    step : false ≡ true
    step = eq true false ∙ cong₂ _&&_ ftrue gfalse

chain-dependent : fst (Dep marg diagS)
chain-dependent h = PT.rec isProp⊥ chain-not-product h

-- ------------------------------------------------------------
-- Its restriction is the mediator fibre, and that IS a product.
-- Conditioning has closed the path.
-- ------------------------------------------------------------
fibre : Supp
fibre = restrM r diagS

fibre-cells : (x y : Bool) → fibre x y ≡ (x && y)
fibre-cells true  true  = refl
fibre-cells true  false = refl
fibre-cells false true  = refl
fibre-cells false false = refl

fibre-product : IsProduct fibre
fibre-product = (λ x → x) , (λ y → y) , fibre-cells

not-dep-cond : ¬ (fst (Dep cond fibre))
not-dep-cond nd = nd ∣ fibre-product ∣₁

-- ------------------------------------------------------------
-- THE OBSTRUCTION.  Dependence is not closed under restriction,
-- so it is not the predicate of any sieve.
-- ------------------------------------------------------------
dep-not-closed
  : ¬ ( (d e : BObj) (k : BHom e d) (S : Supp)
      → fst (Dep d S) → fst (Dep e (restrM k S)) )
dep-not-closed cl = not-dep-cond (cl marg cond r diagS chain-dependent)

dep-no-sieve
  : ¬ ( (d e : BObj) (k : BHom e d) (S : Supp)
      → fst (Dep d S) → fst (Dep e (restrM k S)) )
dep-no-sieve = dep-not-closed
