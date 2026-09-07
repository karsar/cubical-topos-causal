{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.IdentificationSieve — the identification type as a
-- morphism 𝟙 ⇒ Ω over the intervention site.
--
-- Identifiability is a restriction-closed predicate on the
-- terminal presheaf, so the classification theorem gives a
-- unique χ-ident : 𝟙 ⇒ Ω whose ⊤-fibre is exactly the
-- identifiable contexts.
--
-- The resulting sieve on obs is {e0, e1}, the same non-maximal
-- sieve that carries the internal-versus-stagewise gap.
-- ============================================================

module Topos.IdentificationSieve where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Unit using (Unit; Unit*; tt; tt*; isPropUnit*)
open import Cubical.Data.Empty as E using (⊥; isProp⊥)
open import Cubical.Data.Sigma using (_,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Functions.Logic using (⇔toPath)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.InterventionSite

-- ------------------------------------------------------------
-- Abbreviations.
-- ------------------------------------------------------------
⊤hp : hProp ℓ-zero
⊤hp = Unit* , isPropUnit*
⊥hp : hProp ℓ-zero
⊥hp = ⊥ , isProp⊥

-- ------------------------------------------------------------
-- The identifiability predicate.
-- At an interventional context the effect is directly observed.
-- At obs the effect is not identifiable (no valid adjustment set).
-- ------------------------------------------------------------
IdentPred : IObj → hProp ℓ-zero
IdentPred obs = ⊥hp
IdentPred do0 = ⊤hp
IdentPred do1 = ⊤hp

IdentPred-closed : (c d : IObj) → IHom d c → fst (IdentPred c) → fst (IdentPred d)
IdentPred-closed obs obs idₒ pf = E.rec pf
IdentPred-closed obs do0 e0  pf = E.rec pf
IdentPred-closed obs do1 e1  pf = E.rec pf
IdentPred-closed do0 do0 id₀ pf = pf
IdentPred-closed do1 do1 id₁ pf = pf

-- ------------------------------------------------------------
-- The classifying sieve.
-- χ-ident-sieve c = the sieve of arrows f : d → c along which
-- the effect becomes identifiable.
-- ------------------------------------------------------------
χ-ident-sieve : (c : IObj) → Sieve {C = Iv} c
χ-ident-sieve c = mem , clo
  where
    mem : (d : IObj) → IHom d c → hProp ℓ-zero
    mem d _ = IdentPred d

    clo : Closure {C = Iv} c mem
    clo d e k f pf = IdentPred-closed d e k pf

-- The classifying map is natural.
χ-ident-nat : (x y : IObj) (f : IHom x y) (b : Unit)
            → χ-ident-sieve x ≡ pull {C = Iv} f (χ-ident-sieve y)
χ-ident-nat x y f _ =
  Sieve≡ {C = Iv} (χ-ident-sieve x) (pull {C = Iv} f (χ-ident-sieve y))
    (funExt λ d → funExt λ g →
      ⇔toPath {P = IdentPred d} {Q = IdentPred d}
        (λ h → h) (λ h → h))

-- The classifying map χ-ident : 𝟙 ⇒ Ω.
χ-ident : Nat {C = Iv} (𝟙 {C = Iv}) (Ω {C = Iv})
χ-ident = (λ c _ → χ-ident-sieve c) ,
          (λ x y f b → χ-ident-nat x y f b)

-- ------------------------------------------------------------
-- The ⊤-fibre of χ-ident is exactly the identifiable contexts.
-- ------------------------------------------------------------
ident-classified-do0 : χ-ident-sieve do0 ≡ maximal {C = Iv} do0
ident-classified-do0 =
  Sieve≡ {C = Iv} (χ-ident-sieve do0) (maximal {C = Iv} do0)
    (funExt λ d → funExt λ f →
      ⇔toPath {P = IdentPred d} {Q = ⊤hp}
        (λ _ → tt*)
        (λ _ → IdentPred-closed do0 d f tt*))

ident-classified-do1 : χ-ident-sieve do1 ≡ maximal {C = Iv} do1
ident-classified-do1 =
  Sieve≡ {C = Iv} (χ-ident-sieve do1) (maximal {C = Iv} do1)
    (funExt λ d → funExt λ f →
      ⇔toPath {P = IdentPred d} {Q = ⊤hp}
        (λ _ → tt*)
        (λ _ → IdentPred-closed do1 d f tt*))

ident-not-classified-obs : ¬ (χ-ident-sieve obs ≡ maximal {C = Iv} obs)
ident-not-classified-obs p =
  transport (λ i → fst (fst (p (~ i)) obs idₒ)) tt*

-- ------------------------------------------------------------
-- Membership witnesses: the sieve at obs is {e0, e1}.
-- ------------------------------------------------------------
ident-mem-e0 : fst (fst (χ-ident-sieve obs) do0 e0)
ident-mem-e0 = tt*

ident-mem-e1 : fst (fst (χ-ident-sieve obs) do1 e1)
ident-mem-e1 = tt*

ident-not-mem-idₒ : ¬ fst (fst (χ-ident-sieve obs) obs idₒ)
ident-not-mem-idₒ pf = pf
