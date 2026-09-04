{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.CoarseSite — the coarse intervention poset.
--
-- The site has two objects:  cDo → cObs.
-- cObs is the observational context.  cDo is a single merged
-- intervention context.  The coarse site records that an
-- intervention occurred, but not which value was set.
--
-- The family {cDo} covers cObs.  jC is the induced closure.
-- It mirrors jS from Topos.InterventionModality.
--
-- Ω at cObs has three truth values: ∅, {ce}, ⊤.  The fine Ω
-- at obs has five.  The two extra values {e0} and {e1}
-- distinguish the interventions.  Topos.MergeAbstraction shows
-- neither is the preimage of a coarse truth value.
-- ============================================================

module Topos.CoarseSite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Prelude using (isProp→isSet)
open import Cubical.Foundations.HLevels using (isProp×; hProp)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Data.Empty as E using (⊥; isProp⊥)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)

open import Topos.Cat
open import Topos.Omega

-- ------------------------------------------------------------
-- Objects and morphisms of the coarse poset.
-- ------------------------------------------------------------
data CObj : Type where
  cObs cDo : CObj

data CHom : CObj → CObj → Type where
  idc : CHom cObs cObs
  idd : CHom cDo cDo
  ce  : CHom cDo cObs      -- cDo ≤ cObs

-- Thin: every hom-set is a proposition.
isPropCHom : (x y : CObj) → isProp (CHom x y)
isPropCHom cObs cObs idc idc = refl
isPropCHom cDo cDo idd idd = refl
isPropCHom cDo cObs ce ce = refl
isPropCHom cObs cDo ()

-- Identities and composition.  The poset is thin, so both are
-- determined.
idCv : ∀ {x} → CHom x x
idCv {cObs} = idc
idCv {cDo}  = idd

_⋆C_ : ∀ {x y z} → CHom x y → CHom y z → CHom x z
idc ⋆C g = g
idd ⋆C g = g
ce  ⋆C idc = ce

-- ------------------------------------------------------------
-- The coarse poset as a Precategory.
-- ------------------------------------------------------------
Cv : Precategory ℓ-zero ℓ-zero
Cv = record
  { Ob       = CObj
  ; Hom      = CHom
  ; idn      = idCv
  ; _⋆_      = _⋆C_
  ; ⋆-idL    = λ f → isPropCHom _ _ (idCv ⋆C f) f
  ; ⋆-idR    = λ f → isPropCHom _ _ (f ⋆C idCv) f
  ; ⋆-assoc  = λ f g h → isPropCHom _ _ ((f ⋆C g) ⋆C h) (f ⋆C (g ⋆C h))
  ; isSetHom = λ {x} {y} → isProp→isSet (isPropCHom x y)
  }

-- Truth values.
⊤hpC : hProp ℓ-zero
⊤hpC = Unit* , isPropUnit*
⊥hpC : hProp ℓ-zero
⊥hpC = ⊥ , isProp⊥

-- ------------------------------------------------------------
-- ci-c = {ce}: the claim holds under the merged intervention
-- and not observationally.  Its preimage under the merge
-- functor is {e0, e1}, the fine claim that holds under both
-- interventions.
-- ------------------------------------------------------------
ci-c : Sieve {C = Cv} cObs
ci-c = mem , clo
  where
    mem : (d : CObj) → CHom d cObs → hProp ℓ-zero
    mem cObs idc = ⊥hpC
    mem cDo ce   = ⊤hpC
    clo : Closure {C = Cv} cObs mem
    clo cDo cDo idd ce   pf = tt*
    clo cObs cObs idc idc pf = E.rec pf
    clo cObs cDo ce  idc pf = E.rec pf

-- ------------------------------------------------------------
-- jC is the covering closure on sieves over cObs.  The cover
-- is {cDo}.
--   jC S contains ce  iff S contains ce.
--   jC S contains idc iff S contains ce.
-- ------------------------------------------------------------
jC : Sieve {C = Cv} cObs → Sieve {C = Cv} cObs
jC S = mem , clo
  where
    ce∈ = fst S cDo ce
    mem : (d : CObj) → CHom d cObs → hProp ℓ-zero
    mem cObs idc = ce∈
    mem cDo ce   = ce∈
    clo : Closure {C = Cv} cObs mem
    clo cObs cObs idc idc pf = pf
    clo cObs cDo ce  idc pf = pf
    clo cDo cDo idd ce   pf = pf
