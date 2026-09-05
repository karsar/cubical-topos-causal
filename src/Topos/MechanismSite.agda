{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.MechanismSite — the mechanism classifier on a base with
-- a genuine refinement.
--
-- Topos.MechanismSeparation works over one context.  That is
-- enough to show the classifier discriminates, but it leaves the
-- reply that the base was discrete.  This module runs the same
-- classifier over the intervention site of
-- Topos.InterventionSite, where obs has two incomparable
-- refinements, and gets a stronger result.
--
-- The value presheaf is chosen so that the fixed value is
-- forced at do0 and free at do1:
--     Val obs = Bool,  Val do0 = Unit,  Val do1 = Bool,
-- with restriction along e0 collapsing to the point.  So a
-- mechanism is automatically admissible over do0, whatever it
-- does, and admissible over do1 only if it returns the fixed
-- value there.
--
-- Results:
--   const-⊤        the do-mechanism is classified ⊤.
--   copy-at-e0     the copying mechanism IS admissible over do0.
--   copy-not-e1    it is NOT admissible over do1.
--   copy-non-max   so its classifying sieve is neither ⊤ nor ⊥.
--
-- The classifier therefore takes a truth value strictly between
-- the two on this site, and that value is the sieve {e0}: the
-- same discriminating truth value that carries the internal-
-- versus-stagewise gap of Topos.Classicality.  Whether a
-- mechanism is an intervention is, on this base, a graded
-- question rather than a yes or no.
-- ============================================================

module Topos.MechanismSite where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit using (Unit; tt; isSetUnit)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Empty as E using (⊥)

open import FDist-Convex using (FDist; pure; mapF; trunc; 𝔼)
open import WeightQ using (Weight; w0; w1; w0≢w1)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.InternalDist
open import Topos.Exponential
open import Topos.InterventionSite
open import Topos.MechanismObject

-- ------------------------------------------------------------
-- Parents: Bool at every context, restriction the identity.
-- ------------------------------------------------------------
ParI : PSh Iv ℓ-zero
ParI = record
  { F₀ = λ _ → Bool ; F₁ = λ _ b → b
  ; F-id = λ _ → refl ; F-comp = λ _ _ _ → refl ; isSetF₀ = λ _ → isSetBool }

-- ------------------------------------------------------------
-- Values: two at obs and at do1, one at do0.  Restricting to
-- do0 forgets the value; restricting to do1 keeps it.
-- ------------------------------------------------------------
ValI-Ob : IObj → Type
ValI-Ob obs = Bool
ValI-Ob do0 = Unit
ValI-Ob do1 = Bool

ValI-restr : {d c : IObj} → IHom d c → ValI-Ob c → ValI-Ob d
ValI-restr idₒ v = v
ValI-restr id₀ v = v
ValI-restr id₁ v = v
ValI-restr e0  _ = tt
ValI-restr e1  v = v

ValI-isSet : (c : IObj) → isSet (ValI-Ob c)
ValI-isSet obs = isSetBool
ValI-isSet do0 = isSetUnit
ValI-isSet do1 = isSetBool

ValI : PSh Iv ℓ-zero
ValI = record
  { F₀ = ValI-Ob ; F₁ = ValI-restr
  ; F-id = λ {x} v → lemId x v
  ; F-comp = λ {x} {y} {z} f g v → lemComp f g v
  ; isSetF₀ = ValI-isSet }
  where
    lemId : (x : IObj) (v : ValI-Ob x) → ValI-restr (idI {x}) v ≡ v
    lemId obs v = refl
    lemId do0 v = refl
    lemId do1 v = refl
    lemComp : {x y z : IObj} (f : IHom x y) (g : IHom y z) (v : ValI-Ob z)
            → ValI-restr (f ⋆I g) v ≡ ValI-restr f (ValI-restr g v)
    lemComp idₒ idₒ v = refl
    lemComp id₀ id₀ v = refl
    lemComp id₁ id₁ v = refl
    lemComp e0  idₒ v = refl
    lemComp e1  idₒ v = refl
    lemComp id₀ e0  v = refl
    lemComp id₁ e1  v = refl

-- The fixed value: true at obs, hence true at do1 and the point
-- at do0.
x₀I : Section {C = Iv} ValI
x₀I = pt' , nat'
  where
    pt' : (c : IObj) → Unit → ValI-Ob c
    pt' obs _ = true
    pt' do0 _ = tt
    pt' do1 _ = true
    nat' : IsNat {C = Iv} (𝟙 {C = Iv}) ValI pt'
    nat' obs obs idₒ _ = refl
    nat' do0 do0 id₀ _ = refl
    nat' do1 do1 id₁ _ = refl
    nat' do0 obs e0  _ = refl
    nat' do1 obs e1  _ = refl

-- ------------------------------------------------------------
-- Two mechanisms at obs.
-- ------------------------------------------------------------
MechI : PSh Iv ℓ-zero
MechI = Mech ParI ValI x₀I

-- The do-mechanism: return the fixed value at every stage.
constI : PSh.F₀ MechI obs
constI = app , nat
  where
    app : (d : IObj) → IHom d obs → Bool → FDist (ValI-Ob d)
    app obs idₒ _ = pure true
    app do0 e0  _ = pure tt
    app do1 e1  _ = pure true
    nat : ExpNat {C = Iv} ParI (Dist_E {C = Iv} ValI) obs app
    nat obs obs idₒ idₒ a = refl
    nat do0 do0 id₀ e0  a = refl
    nat do1 do1 id₁ e1  a = refl
    nat do0 obs e0  idₒ a = refl
    nat do1 obs e1  idₒ a = refl

-- The copying mechanism: read the parent.  Over do0 the value
-- type is a point, so copying and fixing agree there.
copyI : PSh.F₀ MechI obs
copyI = app , nat
  where
    app : (d : IObj) → IHom d obs → Bool → FDist (ValI-Ob d)
    app obs idₒ b = pure b
    app do0 e0  _ = pure tt
    app do1 e1  b = pure b
    nat : ExpNat {C = Iv} ParI (Dist_E {C = Iv} ValI) obs app
    nat obs obs idₒ idₒ a = refl
    nat do0 do0 id₀ e0  a = refl
    nat do1 do1 id₁ e1  a = refl
    nat do0 obs e0  idₒ a = refl
    nat do1 obs e1  idₒ a = refl

-- ------------------------------------------------------------
-- The classifier on this site.
-- ------------------------------------------------------------
-- The do-mechanism is admissible, hence classified ⊤.
const-adm : fst (Adm ParI ValI x₀I obs constI)
const-adm obs idₒ _ = refl
const-adm do0 e0  _ = refl
const-adm do1 e1  _ = refl

const-⊤ : χ-do-sieve ParI ValI x₀I obs constI ≡ maximal {C = Iv} obs
const-⊤ = fst (χ-do-classifies ParI ValI x₀I obs constI) const-adm

-- The copying mechanism is admissible OVER do0: the value type
-- there is a point, so reading the parent changes nothing.
copy-at-e0 : fst (fst (χ-do-sieve ParI ValI x₀I obs copyI) do0 e0)
copy-at-e0 do0 id₀ _ = refl

-- It is NOT admissible over do1: at the parent value false it
-- returns the point mass at false, not at true.  The two are
-- separated in the weight algebra.
indTrue : Bool → Weight
indTrue true  = w1
indTrue false = w0

copy-not-e1 : ¬ (fst (fst (χ-do-sieve ParI ValI x₀I obs copyI) do1 e1))
copy-not-e1 h = w0≢w1 (cong (λ d → 𝔼 d indTrue) (h do1 id₁ false))

-- ------------------------------------------------------------
-- So the classifying sieve is strictly between ⊥ and ⊤.
-- ------------------------------------------------------------
copy-not-⊤ : ¬ (χ-do-sieve ParI ValI x₀I obs copyI ≡ maximal {C = Iv} obs)
copy-not-⊤ p = copy-not-e1 (transport (λ i → fst (fst (p (~ i)) do1 e1)) _)

copy-non-max : ( fst (fst (χ-do-sieve ParI ValI x₀I obs copyI) do0 e0) )
             × ( ¬ (fst (fst (χ-do-sieve ParI ValI x₀I obs copyI) do1 e1)) )
copy-non-max = copy-at-e0 , copy-not-e1
