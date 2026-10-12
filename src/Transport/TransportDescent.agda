{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Transport.TransportDescent: the descent condition for forcing.
--
-- For any base, any Lawvere-Tierney topology J, any context c and
-- any sieve S on c:
--     c ⊩ S   ⟺   S is J-closed  AND  c ⊩ jop J c S.
-- Forcing S means S = ⊤, and j ⊤ = ⊤.  So the proof is short.
-- Closedness alone does not give truth: the second conjunct is
-- needed.
--
-- A second form quantifies over topologies: c ⊩ S exactly when S
-- is closed for EVERY topology.  The converse uses the maximal
-- topology, so this form restates S = ⊤.  It does not select
-- causal claims.
--
-- Results:
--   forced→closed       forcing gives closedness.
--   forcing→descent     forcing gives both conjuncts.
--   descent→forcing     both conjuncts give forcing.
--   maximalLT           the maximal topology, with its axioms.
--   forced→all-closed   forcing gives closedness for every J.
--   all-closed→forced   the converse.
-- ============================================================

module Transport.TransportDescent where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Unit using (tt*)
open import Cubical.Functions.Logic using (⇔toPath)
open import Topos.Cat
open import Topos.Omega
open import Topos.Forcing
open import Topos.Classifier using (idn∈→maximal)
open import Topos.LawvereTierney
open LawvereTierney

module _ {ℓ} {C : Precategory ℓ ℓ} (J : LawvereTierney {C = C})
         (c : Precategory.Ob C) (S : Sieve {C = C} c) where

  forced→closed : _⊩_ {C = C} c S → is-j-closed J c S
  forced→closed h = subst (is-j-closed J c)
    (sym (idn∈→maximal {C = C} S h)) (⊤-j-closed J c)

  forcing→descent : _⊩_ {C = C} c S → is-j-closed J c S × (_⊩_ {C = C} c (jop J c S))
  forcing→descent h = forced→closed h ,
    subst (λ T → _⊩_ {C = C} c T) (sym (forced→closed h)) h

  descent→forcing : is-j-closed J c S × (_⊩_ {C = C} c (jop J c S)) → _⊩_ {C = C} c S
  descent→forcing (closed , local) = subst (λ T → _⊩_ {C = C} c T) closed local

-- ------------------------------------------------------------
-- The second form.  The maximal topology sends every sieve to ⊤.
-- ------------------------------------------------------------
module _ {ℓ} {C : Precategory ℓ ℓ} where

  maximalLT : LawvereTierney {C = C}
  maximalLT = record
    { jop = λ c S → maximal {C = C} c
    ; jnat = λ x y f S → Sieve≡ {C = C} _ _
        (funExt λ d → funExt λ g → refl)
    ; j-⊤ = λ c → refl
    ; j-idem = λ c S → refl
    ; j-∧ = λ c S T → Sieve≡ {C = C} _ _
        (funExt λ d → funExt λ g → ⇔toPath
          (λ _ → tt* , tt*) (λ _ → tt*)) }

  forced→all-closed : (c : Precategory.Ob C) (S : Sieve {C = C} c)
    → _⊩_ {C = C} c S → (J : LawvereTierney {C = C}) → is-j-closed J c S
  forced→all-closed c S h J = forced→closed J c S h

  all-closed→forced : (c : Precategory.Ob C) (S : Sieve {C = C} c)
    → ((J : LawvereTierney {C = C}) → is-j-closed J c S) → _⊩_ {C = C} c S
  all-closed→forced c S all =
    subst (λ T → _⊩_ {C = C} c T) (all maximalLT) tt*
