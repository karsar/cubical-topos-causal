{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.TopologyComparison: the two concrete topologies on the
-- intervention site, compared.
--
-- An earlier version of the paper claimed that the double
-- negation topology is dense and the intervention coverage is
-- not.  It concluded that the two are of different kinds.  That
-- contrast is false.  This module records the correction.
--
-- Density does not separate them.  A topology is dense when it
-- sends the empty sieve to the empty sieve.  The intervention
-- coverage does this, so it is dense too.
--
-- The two also agree on the verdicts the coverage section runs
-- on.  Double negation collapses the sieve that holds under both
-- interventions and leaves the sieve that holds under one of
-- them short of maximal.  Those are the analogues of
-- j-both-collapses and j-one-survives in Topos.InterventionModality.
--
-- The two operators are equal on every stable sieve.  A sieve is
-- stable when each membership P satisfies ¬ ¬ P → P.  Every
-- decidable sieve is stable, so the sieves of the coverage
-- section are covered.  Equality on all sieves is equivalent to
-- double-negation elimination in the metatheory.  So a
-- constructive metatheory cannot prove that the two operators
-- are equal.  The difference is in the logic of the
-- memberships.  The site does not cause it.
--
-- Results:
--   j-int-dense         the intervention coverage is dense
--   nn-both-collapses   double negation collapses the both-sieve
--   nn-one-survives     double negation leaves the one-sieve short
--   nn-is-intervention-on-stable
--                       the two operators agree on stable sieves
--   nn-is-intervention-on-decidable
--                       the two operators agree on decidable sieves
--   agree→DNE, DNE→agree
--                       agreement on all sieves is equivalent to
--                       double-negation elimination
-- ============================================================

module Topos.TopologyComparison where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp; isProp×)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Data.Empty as E using (⊥; ⊥*)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import Cubical.Functions.Logic using (⇔toPath)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.DoubleNegation
open import Topos.InterventionSite
open import Topos.InterventionModality using (jS; ci-one; ci-both)
open import Topos.InterventionLT using (jopI)
open import Topos.Omega using (Closure)

open Precategory Iv

-- (A) The INTERVENTION topology is itself DENSE: j(⊥) = ⊥.
--     An earlier version of the paper used density to set ¬¬ apart.
j-int-dense : jopI obs (⊥S {C = Iv} obs) ≡ ⊥S {C = Iv} obs
j-int-dense = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ f → go d f)
  where
    go : (d : IObj) (f : IHom d obs)
       → fst (jopI obs (⊥S {C = Iv} obs)) d f ≡ fst (⊥S {C = Iv} obs) d f
    go obs idₒ = ⇔toPath fst (λ x → E.rec* x)
    go do0 e0  = refl
    go do1 e1  = refl

-- (B) ¬¬ lifts ci-both to contain the identity.  This is the same
--     verdict that the paper displays as  j (ci-both) ≡ ⊤.
nn-both-has-id : fst (fst (¬¬S {C = Iv} {c = obs} ci-both) obs idₒ)
nn-both-has-id obs idₒ h = h do0 e0  tt*
nn-both-has-id do0 e0  h = h do0 id₀ tt*
nn-both-has-id do1 e1  h = h do1 id₁ tt*

-- (C) ¬¬ does NOT lift ci-one to contain the identity.  This is the
--     same verdict that the paper displays as  ¬ (j (ci-one) ≡ ⊤).
neg-at-e1 : (e : IObj) (g : IHom e do1) → fst (fst ci-one e (g ⋆I e1)) → ⊥* {ℓ-zero}
neg-at-e1 obs ()
neg-at-e1 do0 ()
neg-at-e1 do1 id₁ x = E.rec x

nn-one-misses-id : ¬ (fst (fst (¬¬S {C = Iv} {c = obs} ci-one) obs idₒ))
nn-one-misses-id p = E.rec* (p do1 e1 neg-at-e1)

-- (D) The SHARP form: ¬¬ collapses ci-both to the maximal sieve,
--     which matches the paper's `j-both-collapses` for jopI.
nn-both-all : (d : IObj) (f : IHom d obs)
            → fst (fst (¬¬S {C = Iv} {c = obs} ci-both) d f)
nn-both-all obs idₒ obs idₒ h = h do0 e0  tt*
nn-both-all obs idₒ do0 e0  h = h do0 id₀ tt*
nn-both-all obs idₒ do1 e1  h = h do1 id₁ tt*
nn-both-all do0 e0  do0 id₀ h = h do0 id₀ tt*
nn-both-all do1 e1  do1 id₁ h = h do1 id₁ tt*

nn-both-collapses : ¬¬S {C = Iv} {c = obs} ci-both ≡ maximal {C = Iv} obs
nn-both-collapses = Sieve≡ {C = Iv} _ _
  (funExt λ d → funExt λ f → ⇔toPath (λ _ → tt*) (λ _ → nn-both-all d f))

-- (E) ¬¬ does NOT collapse ci-one.  This matches `j-one-survives` for jopI.
nn-one-survives : ¬ (¬¬S {C = Iv} {c = obs} ci-one ≡ maximal {C = Iv} obs)
nn-one-survives p = nn-one-misses-id
  (transport (λ i → fst (fst (p (~ i)) obs idₒ)) tt*)

-- ------------------------------------------------------------
-- (F) When the two operators are equal.
--
-- A proposition P is stable when ¬ ¬ P implies P.  A sieve is
-- stable when each of its memberships is stable.  A sieve with
-- decidable memberships is stable.
--
-- On stable sieves, ¬¬ and the intervention topology are equal.
-- At obs, both contain idₒ exactly when the sieve contains e0
-- and e1.  At each intervention, ¬¬ keeps a stable membership
-- and jopI is the identity.
--
-- Equality on all sieves is equivalent to double-negation
-- elimination for all propositions.  The atom sieve on do0 shows
-- this.  Its one membership is an arbitrary proposition P.  At
-- do0, jopI does not change it, but ¬¬ sends it to ¬ ¬ P.  So a
-- constructive metatheory cannot prove that the two operators are
-- equal.  It proves that they agree on stable sieves.  With
-- excluded middle in the metatheory, they are the same topology.
-- ------------------------------------------------------------

Stable : hProp ℓ-zero → Type
Stable P = ¬ ¬ fst P → fst P

StableSieve : {c : IObj} → Sieve {C = Iv} c → Type
StableSieve {c} S = (d : IObj) (f : IHom d c) → Stable (fst S d f)

DNE : Type₁
DNE = (P : hProp ℓ-zero) → Stable P

dec→stable : (P : hProp ℓ-zero) → Dec (fst P) → Stable P
dec→stable P (yes p) _  = p
dec→stable P (no np) nn = E.rec (nn np)

-- The memberships of ¬¬S use ⊥*.  These two maps move between
-- that form of double negation and the form with ⊥.
private
  dn*→dn : {P : Type} → ((P → ⊥* {ℓ-zero}) → ⊥* {ℓ-zero}) → ¬ ¬ P
  dn*→dn k np = lower (k (λ p → lift (np p)))

-- Pointwise: membership in ¬¬S and in jopI S agree on a stable
-- sieve.  The cases run over every arrow of the poset.
nn→j : (c : IObj) (S : Sieve {C = Iv} c) → StableSieve S
     → (d : IObj) (f : IHom d c)
     → fst (fst (¬¬S {C = Iv} {c = c} S) d f) → fst (fst (jopI c S) d f)
nn→j obs S st obs idₒ n =
    st do0 e0 (dn*→dn λ k → n do0 e0 (at0 k))
  , st do1 e1 (dn*→dn λ k → n do1 e1 (at1 k))
  where
    at0 : _ → (e' : IObj) (g' : IHom e' do0) → fst (fst S e' (g' ⋆I e0)) → ⊥*
    at0 k do0 id₀ x = k x
    at1 : _ → (e' : IObj) (g' : IHom e' do1) → fst (fst S e' (g' ⋆I e1)) → ⊥*
    at1 k do1 id₁ x = k x
nn→j obs S st do0 e0 n = st do0 e0 (dn*→dn λ k → n do0 id₀ (at0 k))
  where
    at0 : _ → (e' : IObj) (g' : IHom e' do0) → fst (fst S e' (g' ⋆I e0)) → ⊥*
    at0 k do0 id₀ x = k x
nn→j obs S st do1 e1 n = st do1 e1 (dn*→dn λ k → n do1 id₁ (at1 k))
  where
    at1 : _ → (e' : IObj) (g' : IHom e' do1) → fst (fst S e' (g' ⋆I e1)) → ⊥*
    at1 k do1 id₁ x = k x
nn→j do0 S st do0 id₀ n = st do0 id₀ (dn*→dn λ k → n do0 id₀ (at0 k))
  where
    at0 : _ → (e' : IObj) (g' : IHom e' do0) → fst (fst S e' (g' ⋆I id₀)) → ⊥*
    at0 k do0 id₀ x = k x
nn→j do1 S st do1 id₁ n = st do1 id₁ (dn*→dn λ k → n do1 id₁ (at1 k))
  where
    at1 : _ → (e' : IObj) (g' : IHom e' do1) → fst (fst S e' (g' ⋆I id₁)) → ⊥*
    at1 k do1 id₁ x = k x

-- The other direction needs no stability.
j→nn : (c : IObj) (S : Sieve {C = Iv} c)
     → (d : IObj) (f : IHom d c)
     → fst (fst (jopI c S) d f) → fst (fst (¬¬S {C = Iv} {c = c} S) d f)
j→nn obs S obs idₒ (x0 , x1) obs idₒ h = h do0 e0  x0
j→nn obs S obs idₒ (x0 , x1) do0 e0  h = h do0 id₀ x0
j→nn obs S obs idₒ (x0 , x1) do1 e1  h = h do1 id₁ x1
j→nn obs S do0 e0  x do0 id₀ h = h do0 id₀ x
j→nn obs S do1 e1  x do1 id₁ h = h do1 id₁ x
j→nn do0 S do0 id₀ x do0 id₀ h = h do0 id₀ x
j→nn do1 S do1 id₁ x do1 id₁ h = h do1 id₁ x

nn-is-intervention-on-stable : (c : IObj) (S : Sieve {C = Iv} c) → StableSieve S
                             → ¬¬S {C = Iv} {c = c} S ≡ jopI c S
nn-is-intervention-on-stable c S st = Sieve≡ {C = Iv} _ _
  (funExt λ d → funExt λ f → ⇔toPath (nn→j c S st d f) (j→nn c S d f))

nn-is-intervention-on-decidable :
    (c : IObj) (S : Sieve {C = Iv} c)
  → ((d : IObj) (f : IHom d c) → Dec (fst (fst S d f)))
  → ¬¬S {C = Iv} {c = c} S ≡ jopI c S
nn-is-intervention-on-decidable c S dec =
  nn-is-intervention-on-stable c S λ d f → dec→stable (fst S d f) (dec d f)

-- The atom sieve on do0.  Its one membership is P.
atom : hProp ℓ-zero → Sieve {C = Iv} do0
atom P = mem , clo
  where
    mem : (d : IObj) → IHom d do0 → hProp ℓ-zero
    mem do0 id₀ = P
    clo : Closure {C = Iv} do0 mem
    clo do0 do0 id₀ id₀ p = p

-- Equality of the two operators on every sieve gives
-- double-negation elimination.
agree→DNE : ((c : IObj) (S : Sieve {C = Iv} c) → ¬¬S {C = Iv} {c = c} S ≡ jopI c S)
          → DNE
agree→DNE agree P nnp =
  transport (λ i → fst (fst (agree do0 (atom P) i) do0 id₀)) inNN
  where
    inNN : fst (fst (¬¬S {C = Iv} {c = do0} (atom P)) do0 id₀)
    inNN do0 id₀ h = lift (nnp λ p → lower (h do0 id₀ p))

-- Double-negation elimination makes every sieve stable, so the
-- two operators are then equal on every sieve.
DNE→agree : DNE → (c : IObj) (S : Sieve {C = Iv} c) → ¬¬S {C = Iv} {c = c} S ≡ jopI c S
DNE→agree dne c S = nn-is-intervention-on-stable c S λ d f → dne (fst S d f)
