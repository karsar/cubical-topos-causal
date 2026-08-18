{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.InterventionLT — the intervention coverage as a genuine
-- Lawvere-Tierney topology on Ω.
--
-- Topos.InterventionModality computes a closure operator `jS` at
-- the single object `obs` of the intervention poset, and shows it
-- is discriminating there.  That is not enough to reach any of the
-- modal theorems: `do-j-stable`, `modal-rule1`--`modal-rule3`, the
-- reflector of Topos.Modality and the transport results are all
-- quantified over `J : LawvereTierney`, and `jS` is a bare
-- endofunction on the sieves over one object, not a map Ω ⇒ Ω.
-- Until now the record had exactly two inhabitants, `trivialLT`
-- (vacuous) and `¬¬LT` (the Boolean localisation), so the general
-- theory did not apply to the one coverage doing causal work.
--
-- This module supplies the missing instance.  The closure extends
-- to the whole poset by the identity at `do0` and `do1`, whose
-- only arrow in is the identity, and the four requirements then
-- hold: naturality and idempotence are refl, truth-preservation
-- and meet-preservation need one reshuffle each at `obs`.
--
-- With `interventionLT` in hand every modal theorem instantiates
-- at the intervention coverage.
-- ============================================================

module Topos.InterventionLT where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp; isProp×)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Functions.Logic using (⇔toPath)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.LawvereTierney
open import Topos.InterventionSite
open import Topos.InterventionModality using (jS)

open Precategory Iv
open LawvereTierney

-- ------------------------------------------------------------
-- The closure, everywhere.  At obs it is the coverage closure; at
-- each intervention it is the identity, the only arrow in being
-- the identity, so nothing there is covered by anything smaller.
-- ------------------------------------------------------------
jopI : (c : IObj) → Sieve {C = Iv} c → Sieve {C = Iv} c
jopI obs S = jS S
jopI do0 S = S
jopI do1 S = S

-- ------------------------------------------------------------
-- Naturality: jopI commutes with restriction, so it is a map of
-- presheaves Ω ⇒ Ω and not merely a family of operations.
-- ------------------------------------------------------------
jnatI : IsNat {C = Iv} (Ω {C = Iv}) (Ω {C = Iv}) jopI
jnatI obs obs idₒ S = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → goO d g)
  where
    goO : (d : IObj) (g : IHom d obs)
        → fst (jopI obs (pull {C = Iv} idₒ S)) d g
        ≡ fst (pull {C = Iv} idₒ (jopI obs S)) d g
    goO obs idₒ = refl
    goO do0 e0  = refl
    goO do1 e1  = refl
jnatI do0 obs e0 S = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → go0 d g)
  where
    go0 : (d : IObj) (g : IHom d do0)
        → fst (jopI do0 (pull {C = Iv} e0 S)) d g
        ≡ fst (pull {C = Iv} e0 (jopI obs S)) d g
    go0 do0 id₀ = refl
jnatI do1 obs e1 S = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → go1 d g)
  where
    go1 : (d : IObj) (g : IHom d do1)
        → fst (jopI do1 (pull {C = Iv} e1 S)) d g
        ≡ fst (pull {C = Iv} e1 (jopI obs S)) d g
    go1 do1 id₁ = refl
jnatI do0 do0 id₀ S = refl
jnatI do1 do1 id₁ S = refl

-- ------------------------------------------------------------
-- Truth is covered.
-- ------------------------------------------------------------
j-⊤I : (c : IObj) → jopI c (maximal {C = Iv} c) ≡ maximal {C = Iv} c
j-⊤I obs = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → go d g)
  where
    go : (d : IObj) (g : IHom d obs)
       → fst (jopI obs (maximal {C = Iv} obs)) d g
       ≡ fst (maximal {C = Iv} obs) d g
    go obs idₒ = ⇔toPath (λ _ → tt*) (λ _ → tt* , tt*)
    go do0 e0  = refl
    go do1 e1  = refl
j-⊤I do0 = refl
j-⊤I do1 = refl

-- ------------------------------------------------------------
-- Idempotence: closing twice at obs asks for the same two
-- memberships, so it is already an equality of terms.
-- ------------------------------------------------------------
j-idemI : (c : IObj) (S : Sieve {C = Iv} c) → jopI c (jopI c S) ≡ jopI c S
j-idemI obs S = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → go d g)
  where
    go : (d : IObj) (g : IHom d obs)
       → fst (jopI obs (jopI obs S)) d g ≡ fst (jopI obs S) d g
    go obs idₒ = refl
    go do0 e0  = refl
    go do1 e1  = refl
j-idemI do0 S = refl
j-idemI do1 S = refl

-- ------------------------------------------------------------
-- Meets: at obs both sides ask for the same four memberships, in
-- a different order.
-- ------------------------------------------------------------
j-∧I : (c : IObj) (S T : Sieve {C = Iv} c)
     → jopI c (_∧S_ {C = Iv} S T) ≡ _∧S_ {C = Iv} (jopI c S) (jopI c T)
j-∧I obs S T = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → go d g)
  where
    go : (d : IObj) (g : IHom d obs)
       → fst (jopI obs (_∧S_ {C = Iv} S T)) d g
       ≡ fst (_∧S_ {C = Iv} (jopI obs S) (jopI obs T)) d g
    go obs idₒ = ⇔toPath (λ p → (fst (fst p) , fst (snd p)) , (snd (fst p) , snd (snd p)))
                         (λ q → (fst (fst q) , fst (snd q)) , (snd (fst q) , snd (snd q)))
    go do0 e0  = refl
    go do1 e1  = refl
j-∧I do0 S T = refl
j-∧I do1 S T = refl

-- ------------------------------------------------------------
-- The instance the record was waiting for.
-- ------------------------------------------------------------
interventionLT : LawvereTierney {C = Iv}
interventionLT = record
  { jop    = jopI
  ; jnat   = jnatI
  ; j-⊤    = j-⊤I
  ; j-idem = j-idemI
  ; j-∧    = j-∧I
  }

-- ------------------------------------------------------------
-- The instance is not vacuous, and it selects.
--
-- `trivialLT` fixes everything and `¬¬LT` is the identity on the
-- two-regime site of Topos.ContingentCI, so neither witnesses a
-- modality that moves a truth value for a causal reason.  This one
-- does: it fixes the claim holding under one intervention and
-- sends the claim holding under both up to ⊤.
-- ------------------------------------------------------------
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Empty as E using (⊥)
open import Topos.InterventionModality
  using (ci-one; ci-both; j-both-collapses; j-one-survives)

-- a claim holding under only one intervention is already closed
ci-one-closed : is-j-closed {C = Iv} interventionLT obs ci-one
ci-one-closed = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → go d g)
  where
    go : (d : IObj) (g : IHom d obs)
       → fst (jopI obs ci-one) d g ≡ fst ci-one d g
    go obs idₒ = ⇔toPath (λ p → snd p) (λ q → E.rec q , q)
    go do0 e0  = refl
    go do1 e1  = refl

-- a claim holding under both is not closed: the modality moves it,
-- and moves it all the way to ⊤
ci-both≢⊤ : ¬ (ci-both ≡ maximal {C = Iv} obs)
ci-both≢⊤ q = transport (λ i → fst (fst (q (~ i)) obs idₒ)) tt*

ci-both-not-closed : ¬ (is-j-closed {C = Iv} interventionLT obs ci-both)
ci-both-not-closed p = ci-both≢⊤ (sym p ∙ j-both-collapses)
