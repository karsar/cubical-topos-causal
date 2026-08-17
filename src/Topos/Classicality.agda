{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.Classicality — internal validity versus stagewise validity
-- on the intervention site Iv (do0 → obs ← do1).
--
-- Forcing at a stage, c ⊩ S, is INTERNAL validity: the identity of c
-- lies in S.  "Stagewise" validity is the classical, context-by-
-- context reading: the claim holds under do(X:=0) and under
-- do(X:=1), with no demand that it hold observationally.
--
-- Two facts, and a third that names the gap between them:
--
--  (1) SOUND.  Internal validity implies stagewise validity —
--      forcing is stable under restriction (sieves are downward
--      closed).  So the topos reading never proves more.
--
--  (2) STRICT.  The converse FAILS.  The excluded-middle instance
--      for a one-intervention claim, ci-one ∨ ¬ ci-one, is forced
--      at do0 and at do1 but NOT at obs.  So on this base the topos
--      reading forces strictly FEWER causal statements than the
--      stagewise one.  Internal validity is the stricter criterion,
--      and the set of statements meeting it is smaller.  We check
--      this base only; we do not prove it of every base carrying a
--      non-trivial refinement.
--
--  (3) WHAT j SUPPLIES.  Stagewise validity of S is, definitionally,
--      internal validity of its covering closure: `obs ⊩ jS S` and
--      `stagewise S` are the same type.  The Lawvere-Tierney
--      modality is therefore exactly the transfer from stagewise to
--      internal validity, and it repairs the deficit in (2) —
--      jS (ci-one ∨ ¬ ci-one) ≡ ⊤ while ci-one ∨ ¬ ci-one ≢ ⊤.
--
-- The failure in (2) comes from the base having a non-trivial
-- refinement, not from any undecidability in the ambient logic:
-- every membership here is ⊤ or ⊥.  On a DISCRETE base the only
-- arrow into c is the identity, stagewise and internal validity
-- coincide, and the modal layer carries no information — which is
-- the degeneracy Topos.ContingentCI and Topos.ModalCI exhibit.
-- ============================================================

module Topos.Classicality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isProp×; hProp)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Data.Empty as E using (⊥; ⊥*; isProp⊥; isProp⊥*)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Functions.Logic using (_⊔_; inl; inr; ⊔-elim; ⇔toPath)

open import Topos.Cat
open import Topos.Omega
open import Topos.DoubleNegation using (¬S; ⊥S; _⇒S_)
open import Topos.Forcing using (_∨S_; _⊩_; ⊩-mono)
open import Topos.InterventionSite
open import Topos.InterventionModality

private
  ⊥*hp : hProp ℓ-zero
  ⊥*hp = ⊥* , isProp⊥*

-- ------------------------------------------------------------
-- Stagewise validity: the claim holds under BOTH interventions.
-- This is the classical, context-by-context reading — exactly the
-- membership of `jS S` at the identity of `obs`, by definition of
-- the covering closure.
-- ------------------------------------------------------------
stagewise : Sieve {C = Iv} obs → Type
stagewise S = fst (fst S do0 e0) × fst (fst S do1 e1)

-- (3a) Stagewise validity IS internal validity of the closure.
-- Both sides are the same type; the equivalence is the identity.
stagewise→⊩j : (S : Sieve {C = Iv} obs) → stagewise S → _⊩_ {C = Iv} obs (jS S)
stagewise→⊩j S p = p

⊩j→stagewise : (S : Sieve {C = Iv} obs) → _⊩_ {C = Iv} obs (jS S) → stagewise S
⊩j→stagewise S p = p

-- (1) SOUNDNESS: internal validity implies stagewise validity.
-- A sieve containing the identity of obs contains every arrow into
-- obs, by downward closure.
⊩→stagewise : (S : Sieve {C = Iv} obs) → _⊩_ {C = Iv} obs S → stagewise S
⊩→stagewise S p =
    snd S obs do0 e0 idₒ p
  , snd S obs do1 e1 idₒ p

-- ------------------------------------------------------------
-- (2) STRICTNESS: the converse fails.
--
-- Take the excluded-middle instance for `ci-one`, the claim that
-- holds under do(X:=0) only.  Classically the claim is decided at
-- each intervention context — it holds at do0, its negation holds
-- at do1 — but the disjunction is not forced observationally.
-- ------------------------------------------------------------
em : Sieve {C = Iv} obs
em = _∨S_ {C = Iv} {c = obs} ci-one (¬S {C = Iv} {c = obs} ci-one)

-- The negation of ci-one holds at do1: the only arrow into do1 is
-- the identity, and ci-one does not contain e1.
¬ci-one-at-do1 : fst (fst (¬S {C = Iv} {c = obs} ci-one) do1 e1)
¬ci-one-at-do1 do1 id₁ x = E.rec x

-- ci-one itself holds at do0, so the disjunction does.
em-at-do0 : fst (fst em do0 e0)
em-at-do0 = inl tt*

-- the right disjunct holds at do1.
em-at-do1 : fst (fst em do1 e1)
em-at-do1 = inr ¬ci-one-at-do1

-- Excluded middle for ci-one is stagewise valid.
em-stagewise : stagewise em
em-stagewise = em-at-do0 , em-at-do1

-- But it is NOT forced at obs.  Neither disjunct is available
-- there: ci-one omits the identity, and ¬ ci-one cannot hold at the
-- identity because its restriction along e0 lands in ci-one.
em-not-forced : ¬ (_⊩_ {C = Iv} obs em)
em-not-forced x = E.rec* (⊔-elim (fst ci-one obs idₒ)
                                 (fst (¬S {C = Iv} {c = obs} ci-one) obs idₒ)
                                 (λ _ → ⊥*hp)
                                 (λ p  → E.rec p)
                                 (λ nc → nc do0 e0 tt*)
                                 x)

-- The theorem: stagewise validity does not imply internal validity.
-- Internal (topos) validity is STRICTLY stronger than the classical
-- context-by-context reading on this site.
internal-strictly-stronger
  : Σ[ S ∈ Sieve {C = Iv} obs ] (stagewise S × (¬ (_⊩_ {C = Iv} obs S)))
internal-strictly-stronger = em , em-stagewise , em-not-forced

-- ------------------------------------------------------------
-- (3b) What the modality supplies: the covering closure repairs
-- exactly this gap.
-- ------------------------------------------------------------
em-covered : jS em ≡ maximal {C = Iv} obs
em-covered = Sieve≡ {C = Iv} (jS em) (maximal {C = Iv} obs)
  (funExt λ d → funExt λ f → go d f)
  where
    go : (d : IObj) (f : IHom d obs)
       → fst (jS em) d f ≡ fst (maximal {C = Iv} obs) d f
    go obs idₒ = ⇔toPath (λ _ → tt*) (λ _ → em-at-do0 , em-at-do1)
    go do0 e0  = ⇔toPath (λ _ → tt*) (λ _ → em-at-do0)
    go do1 e1  = ⇔toPath (λ _ → tt*) (λ _ → em-at-do1)
