{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.Modality — Stage 2 (b): the lex modality ◯ as a
-- reflective modality, at the propositional (subobject) level.
--
-- A Lawvere–Tierney topology J gives a closure operator
--     ◯ = jop J : Ω → Ω
-- with unit η (= inflationarity j-infl), idempotence (◯S modal),
-- and the REFLECTOR universal property:
--     T modal  ⟹  ( S ≤ T  ⇔  ◯S ≤ T ).
-- So the j-closed sieves form a reflective sub-poset of Ω, with ◯
-- the reflector and η the unit — the (−1)-truncated / subobject
-- shadow of sheafification.  "◯-modal" is now a property one can
-- state and discharge directly (is-j-closed), which is what (b)
-- asked for.
--
-- SCOPE: this is the modality on PROPOSITIONS (truth values).  The
-- full TYPE-level reflector — sheafification of arbitrary
-- presheaves, with descent — is the ∞-categorical part and remains
-- paper-only (it needs the modal/Cat machinery outside current
-- cubical Agda).  Monotonicity of ◯ is DERIVED here
-- from meet-preservation, not assumed.
-- ============================================================

module Topos.Modality where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.Data.Sigma using (_,_; fst; snd)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.LawvereTierney
open LawvereTierney

module _ {ℓ} {C : Precategory ℓ ℓ} (J : LawvereTierney {C = C}) where
  open Precategory C
  open PSh

  -- ----------------------------------------------------------
  -- Sieve order and meet (C-pinned, as the bare operators leave
  -- their {C} a metavariable).
  -- ----------------------------------------------------------
  _≤S_ : {c : Ob} → Sieve {C = C} c → Sieve {C = C} c → Type ℓ
  _≤S_ {c} S T = (d : Ob) (f : Hom d c) → fst (fst S d f) → fst (fst T d f)

  _∩_ : {c : Ob} → Sieve {C = C} c → Sieve {C = C} c → Sieve {C = C} c
  _∩_ {c} S T = _∧S_ {C = C} {c = c} S T

  ≤-refl : {c : Ob} (S : Sieve {C = C} c) → S ≤S S
  ≤-refl S d f x = x

  ≤-antisym : {c : Ob} (S T : Sieve {C = C} c) → S ≤S T → T ≤S S → S ≡ T
  ≤-antisym {c} S T p q =
    Sieve≡ {C = C} S T (funExt λ d → funExt λ f → ⇔toPath (p d f) (q d f))

  ∩≤L : {c : Ob} (S T : Sieve {C = C} c) → (S ∩ T) ≤S S
  ∩≤L S T d f x = fst x
  ≤∩ : {c : Ob} (R S T : Sieve {C = C} c) → R ≤S S → R ≤S T → R ≤S (S ∩ T)
  ≤∩ R S T p q d f x = (p d f x , q d f x)

  -- from A ≡ A ∩ B extract A ≤ B (take the second meet component)
  ≤-of-meet-eq : {c : Ob} (A B : Sieve {C = C} c) → A ≡ (A ∩ B) → A ≤S B
  ≤-of-meet-eq A B eq d f x =
    snd (transport (cong (λ Sv → fst (fst Sv d f)) eq) x)

  -- ----------------------------------------------------------
  -- The modality ◯ and its unit.
  -- ----------------------------------------------------------
  ◯ : (c : Ob) → Sieve {C = C} c → Sieve {C = C} c
  ◯ c = jop J c

  -- unit η : S → ◯S  (inflationarity)
  η : (c : Ob) (S : Sieve {C = C} c) → S ≤S ◯ c S
  η c S = j-infl J c S

  -- ◯S is modal (idempotence)
  ◯-modal : (c : Ob) (S : Sieve {C = C} c) → is-j-closed J c (◯ c S)
  ◯-modal c S = j-idem J c S

  -- ----------------------------------------------------------
  -- Monotonicity of ◯, derived from meet-preservation:
  --   S ≤ T  ⟹  S ≡ S∩T  ⟹  ◯S ≡ ◯S ∩ ◯T  ⟹  ◯S ≤ ◯T.
  -- ----------------------------------------------------------
  ◯-mono : (c : Ob) (S T : Sieve {C = C} c) → S ≤S T → ◯ c S ≤S ◯ c T
  ◯-mono c S T h = ≤-of-meet-eq (◯ c S) (◯ c T) ◯S≡◯S∩◯T
    where
      S≡S∩T : S ≡ (S ∩ T)
      S≡S∩T = ≤-antisym S (S ∩ T) (≤∩ S S T (≤-refl S) h) (∩≤L S T)
      ◯S≡◯S∩◯T : ◯ c S ≡ (◯ c S ∩ ◯ c T)
      ◯S≡◯S∩◯T = cong (◯ c) S≡S∩T ∙ j-∧ J c S T

  -- ----------------------------------------------------------
  -- The reflector universal property:  for modal T,
  --     S ≤ T   ⇔   ◯S ≤ T.
  -- ----------------------------------------------------------
  ◯-rec : (c : Ob) (S T : Sieve {C = C} c)
        → is-j-closed J c T → S ≤S T → ◯ c S ≤S T
  ◯-rec c S T modal h d f x =
    transport (cong (λ Sv → fst (fst Sv d f)) modal) (◯-mono c S T h d f x)

  ◯-rec-inv : (c : Ob) (S T : Sieve {C = C} c)
            → ◯ c S ≤S T → S ≤S T
  ◯-rec-inv c S T g d f x = g d f (η c S d f x)
