{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.ColliderObstruction — conditional independence is not a
-- sieve when refinement includes conditioning on a collider.
--
-- Topos.CIObject builds a contingent independence as an internal
-- truth value, and records in a comment that this works only
-- where refinement preserves the independence.  For a collider
-- it does not: conditioning on a common effect opens the path
-- between its causes.  This module turns that comment into a
-- theorem.
--
-- A truth value in the internal logic is a sieve, and a sieve is
-- closed under precomposition: what holds at a stage holds at
-- every refinement of it.  So a predicate that a refinement can
-- falsify is not a truth value at all, and none of the sieve
-- machinery applies to it.
--
-- The base has two contexts and one proper arrow:
--     cond --r--> marg
-- reading marg as the marginal regime and cond as the regime
-- that conditions on the collider.  The object at each context
-- is the support of the joint over two causes, and restriction
-- along r keeps the outcomes the collider admits.
--
-- Independence is taken at the level of supports: a support is
-- independent when it is a product of a set of X-values with a
-- set of Y-values.  This is the possibilistic reading the
-- contextuality development already uses, and it is enough,
-- because a counterexample here is a counterexample for any
-- finer notion that refines it.
--
-- Results:
--   full-indep      the marginal support is a product.
--   xor-not-indep   its restriction to the collider fibre is not.
--   not-closed      so independence is NOT closed under
--                   restriction on this base.
--   no-sieve        hence it defines no sieve, at any context.
--
-- The practical reading: if the refinement relation between your
-- regimes includes conditioning on a common effect, a
-- conditional-independence claim has no internal truth value,
-- and every sieve-based result in this development is silent
-- about it.  The condition is checkable from the study design.
-- ============================================================

module Topos.ColliderObstruction where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Empty as E using (⊥; isProp⊥)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega

-- ------------------------------------------------------------
-- Boolean helpers.  The collider is the exclusive or of its two
-- causes, which is the sharpest case: conditioning on it makes
-- each cause a function of the other.
-- ------------------------------------------------------------
_&&_ : Bool → Bool → Bool
true  && b = b
false && _ = false

notB : Bool → Bool
notB true  = false
notB false = true

xor : Bool → Bool → Bool
xor true  b = notB b
xor false b = b

-- ------------------------------------------------------------
-- The base: conditioning refines the marginal regime.
-- ------------------------------------------------------------
data BObj : Type where
  marg cond : BObj

data BHom : BObj → BObj → Type where
  idm : BHom marg marg
  idc : BHom cond cond
  r   : BHom cond marg

isPropBHom : (x y : BObj) → isProp (BHom x y)
isPropBHom marg marg idm idm = refl
isPropBHom cond cond idc idc = refl
isPropBHom cond marg r r = refl
isPropBHom marg cond ()

idB : ∀ {x} → BHom x x
idB {marg} = idm
idB {cond} = idc

_⋆B_ : ∀ {x y z} → BHom x y → BHom y z → BHom x z
idm ⋆B g = g
idc ⋆B g = g
r   ⋆B idm = r

Bv : Precategory ℓ-zero ℓ-zero
Bv = record
  { Ob = BObj ; Hom = BHom ; idn = idB ; _⋆_ = _⋆B_
  ; ⋆-idL = λ f → isPropBHom _ _ (idB ⋆B f) f
  ; ⋆-idR = λ f → isPropBHom _ _ (f ⋆B idB) f
  ; ⋆-assoc = λ f g h → isPropBHom _ _ ((f ⋆B g) ⋆B h) (f ⋆B (g ⋆B h))
  ; isSetHom = λ {x} {y} → isProp→isSet (isPropBHom x y) }

-- ------------------------------------------------------------
-- Supports of a joint over the two causes, and restriction to
-- the fibre the collider admits.
-- ------------------------------------------------------------
Supp : Type
Supp = Bool → Bool → Bool

isSetSupp : isSet Supp
isSetSupp = isSetΠ λ _ → isSetΠ λ _ → isSetBool

restr : {d c : BObj} → BHom d c → Supp → Supp
restr idm S = S
restr idc S = S
restr r   S = λ x y → S x y && xor x y

SuppP : PSh Bv ℓ-zero
SuppP = record
  { F₀ = λ _ → Supp ; F₁ = restr
  ; F-id = λ {x} S → lemId x S
  ; F-comp = λ f g S → lemComp f g S
  ; isSetF₀ = λ _ → isSetSupp }
  where
    lemId : (x : BObj) (S : Supp) → restr (idB {x}) S ≡ S
    lemId marg S = refl
    lemId cond S = refl
    lemComp : {x y z : BObj} (f : BHom x y) (g : BHom y z) (S : Supp)
            → restr (f ⋆B g) S ≡ restr f (restr g S)
    lemComp idm idm S = refl
    lemComp idc idc S = refl
    lemComp idc r   S = refl
    lemComp r   idm S = refl

-- ------------------------------------------------------------
-- Independence, possibilistically: the support is a product.
-- ------------------------------------------------------------
IsProduct : Supp → Type
IsProduct S = Σ[ f ∈ (Bool → Bool) ] Σ[ g ∈ (Bool → Bool) ]
              ((x y : Bool) → S x y ≡ f x && g y)

Indep : (c : BObj) → Supp → hProp ℓ-zero
Indep _ S = ∥ IsProduct S ∥₁ , squash₁

-- ------------------------------------------------------------
-- The marginal support is a product: everything is possible.
-- ------------------------------------------------------------
full : Supp
full _ _ = true

full-indep : fst (Indep marg full)
full-indep = ∣ (λ _ → true) , (λ _ → true) , (λ x y → refl) ∣₁

-- ------------------------------------------------------------
-- Its restriction along r is the collider fibre, and that is
-- not a product.  Conditioning has opened the path.
-- ------------------------------------------------------------
diag : Supp
diag = restr r full

diag-tt : diag true true ≡ false
diag-tt = refl

diag-tf : diag true false ≡ true
diag-tf = refl

diag-ft : diag false true ≡ true
diag-ft = refl

-- If a conjunction is true, both sides are.
&&-l : (a b : Bool) → (a && b) ≡ true → a ≡ true
&&-l true  b p = refl
&&-l false b p = E.rec (true≢false (sym p))

&&-r : (a b : Bool) → (a && b) ≡ true → b ≡ true
&&-r true  b p = p
&&-r false b p = E.rec (true≢false (sym p))

-- The mixed cells force both factors true; the agreeing cell is
-- then forced true, and it is false.
xor-not-indep : ¬ (IsProduct diag)
xor-not-indep (f , g , eq) = true≢false (sym step)
  where
    ftrue : f true ≡ true
    ftrue = &&-l (f true) (g false) (sym (eq true false))
    gtrue : g true ≡ true
    gtrue = &&-r (f false) (g true) (sym (eq false true))
    step : false ≡ true
    step = eq true true ∙ cong₂ _&&_ ftrue gtrue

not-indep-cond : ¬ (fst (Indep cond diag))
not-indep-cond h = PT.rec isProp⊥ xor-not-indep h

-- ------------------------------------------------------------
-- THE OBSTRUCTION.  Independence is not closed under
-- restriction, so it is not the predicate of any sieve.
-- ------------------------------------------------------------
not-closed
  : ¬ ( (d e : BObj) (k : BHom e d) (S : Supp)
      → fst (Indep d S) → fst (Indep e (restr k S)) )
not-closed cl = not-indep-cond (cl marg cond r full full-indep)

-- And therefore the universal property of Ω does not apply:
-- the hypothesis Topos.Classifier requires is exactly the one
-- refuted above, so there is no characteristic map to build.
no-sieve
  : ¬ ( (d e : BObj) (k : BHom e d) (S : Supp)
      → fst (Indep d S) → fst (Indep e (restr k S)) )
no-sieve = not-closed
