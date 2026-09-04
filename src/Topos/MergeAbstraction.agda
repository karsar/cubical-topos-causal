{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.MergeAbstraction — the merge abstraction and its
-- comparison map on truth values.
--
-- F : Iv → Cv is the base functor.  F sends obs to cObs and
-- sends both do0 and do1 to cDo.  The image records that an
-- intervention occurred, but not which value was set.
--
-- φ is the comparison map at obs.  It sends a coarse sieve to
-- its preimage.  It is the component at obs of the canonical
-- map F*Ω_Cv ⇒ Ω_Iv.
--
-- The module proves three facts:
--  (1) EMBEDDING.  φ is injective.  Forcing transfers both
--      ways (φ-⊩, φ-⊩-reflect).  The coarse gap pulls back to
--      a fine gap (merge-transfers-gap).
--  (2) NOT ISO.  φ is not surjective.  The truth value
--      ci-one = {e0} is not in its image.  So F* is not
--      logical.
--  (3) CAUSAL READING.  {e0} and {e1} state that a claim
--      holds under one intervention and fails under the other.
--      F sends e0 and e1 to the same arrow, so no coarse truth
--      value can make that distinction.
-- ============================================================

module Topos.MergeAbstraction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Data.Empty as E using (⊥; isProp⊥)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation as PT using ()

open import Topos.Cat
open import Topos.Omega
open import Topos.Forcing using (_⊩_)
open import Topos.InterventionSite
open import Topos.InterventionModality using (ci-one; ci-both)
open import Topos.Classicality using (stagewise)
open import Topos.BaseChange using (BaseFunctor; φB)
open import Topos.AbstractionTiers
  using (BackCond; BackCond∥; ∣back∣; ReflectAt; φB-⇒; φB-¬)
open import Topos.DoubleNegation using (_⇒S_; ¬S)
open import Topos.CoarseSite
open import Topos.CoarseClassicality using (em-C; em-C-at-cDo; em-C-not-forced)

-- ------------------------------------------------------------
-- The merge abstraction F : Iv → Cv.
-- ------------------------------------------------------------
F₀m : IObj → CObj
F₀m obs = cObs
F₀m do0 = cDo
F₀m do1 = cDo

F₁m : ∀ {x y} → IHom x y → CHom (F₀m x) (F₀m y)
F₁m idₒ = idc
F₁m id₀ = idd
F₁m id₁ = idd
F₁m e0  = ce
F₁m e1  = ce

-- Functoriality.  F preserves identities by definition.  The
-- composition law is an equality in a propositional hom-set.
F₁m-id : (x : IObj) → F₁m (idI {x}) ≡ idCv {F₀m x}
F₁m-id obs = refl
F₁m-id do0 = refl
F₁m-id do1 = refl

F₁m-⋆ : ∀ {x y z} (f : IHom x y) (g : IHom y z)
      → F₁m (f ⋆I g) ≡ F₁m f ⋆C F₁m g
F₁m-⋆ f g = isPropCHom _ _ (F₁m (f ⋆I g)) (F₁m f ⋆C F₁m g)

-- ------------------------------------------------------------
-- The merge functor as a BaseFunctor, for Topos.BaseChange.
-- ------------------------------------------------------------
mergeF : BaseFunctor Iv Cv
mergeF = record { App₀ = F₀m ; App₁ = F₁m ; App-id = F₁m-id ; App-⋆ = F₁m-⋆ }

-- ------------------------------------------------------------
-- The comparison map φ at obs.  φ S is the preimage of S.
-- Closure is closure of S, transported along functoriality.
-- ------------------------------------------------------------
φ : Sieve {C = Cv} cObs → Sieve {C = Iv} obs
φ S = mem , clo
  where
    mem : (d : IObj) → IHom d obs → _
    mem d f = fst S (F₀m d) (F₁m f)
    clo : Closure {C = Iv} obs mem
    clo d e k f pf =
      subst (λ h → fst (fst S (F₀m e) h))
            (sym (F₁m-⋆ k f))
            (snd S (F₀m d) (F₀m e) (F₁m k) (F₁m f) pf)

-- ------------------------------------------------------------
-- φ is the general comparison map of Topos.BaseChange at the
-- merge functor.  The memberships agree by definition.
-- ------------------------------------------------------------
φ-is-φB : (S : Sieve {C = Cv} cObs) → φ S ≡ φB mergeF obs S
φ-is-φB S = Sieve≡ {C = Iv} (φ S) (φB mergeF obs S)
  (funExt λ d → funExt λ f → refl)

-- ------------------------------------------------------------
-- (1a) Forcing transfers both ways, by definition.  The types
-- obs ⊩ φ S and cObs ⊩ S are equal because F₁m idₒ = idc.
-- ------------------------------------------------------------
φ-⊩ : (S : Sieve {C = Cv} cObs) → _⊩_ {C = Cv} cObs S → _⊩_ {C = Iv} obs (φ S)
φ-⊩ S p = p

φ-⊩-reflect : (S : Sieve {C = Cv} cObs) → _⊩_ {C = Iv} obs (φ S) → _⊩_ {C = Cv} cObs S
φ-⊩-reflect S p = p

-- ------------------------------------------------------------
-- (1b) EMBEDDING.  φ is injective.  The preimage determines the
-- coarse sieve: read idc at (obs, idₒ) and ce at (do0, e0).
-- This works because every arrow into cObs is the image of an
-- arrow into obs.
-- ------------------------------------------------------------
φ-injective : (S T : Sieve {C = Cv} cObs) → φ S ≡ φ T → S ≡ T
φ-injective S T p = Sieve≡ {C = Cv} S T
  (funExt λ d → funExt λ f → go d f)
  where
    go : (d : CObj) (f : CHom d cObs) → fst S d f ≡ fst T d f
    go cObs idc = cong (λ Q → fst Q obs idₒ) p
    go cDo ce   = cong (λ Q → fst Q do0 e0) p

-- ------------------------------------------------------------
-- (2a) φ S gives e0 and e1 the same membership, by definition
-- of F₁m.  The equality is refl.
-- ------------------------------------------------------------
φ-conflates : (S : Sieve {C = Cv} cObs)
            → fst (φ S) do0 e0 ≡ fst (φ S) do1 e1
φ-conflates S = refl

-- ------------------------------------------------------------
-- (2b) NOT ISO.  ci-one = {e0} is not in the image of φ.
-- Suppose φ S ≡ ci-one.  Then fst S cDo ce is the (do0, e0)
-- membership of ci-one, which is inhabited.  It is also the
-- (do1, e1) membership, which is empty.  Contradiction.
-- ------------------------------------------------------------
φ-not-surjective : (S : Sieve {C = Cv} cObs) → ¬ (φ S ≡ ci-one)
φ-not-surjective S p =
  subst (λ Q → fst (fst Q do1 e1)) p
        (subst (λ Q → fst (fst Q do0 e0)) (sym p) tt*)

-- ------------------------------------------------------------
-- (2c) φ sends ci-c to ci-both.  Together with φ-not-surjective
-- this locates the image at the concrete claims: the
-- both-interventions claim is reached, the one-intervention
-- claims are not.
-- ------------------------------------------------------------
φ-ci-c : φ ci-c ≡ ci-both
φ-ci-c = Sieve≡ {C = Iv} (φ ci-c) ci-both
  (funExt λ d → funExt λ f → go d f)
  where
    go : (d : IObj) (f : IHom d obs) → fst (φ ci-c) d f ≡ fst ci-both d f
    go obs idₒ = refl
    go do0 e0  = refl
    go do1 e1  = refl

-- ------------------------------------------------------------
-- (1c) TRANSFER.  The coarse gap pulls back to a fine gap.
-- φ em-C is stagewise valid on the fine cover {do0, do1}: both
-- components are em-C's membership at ce, by definition.  It is
-- not forced at obs, because forcing reflects.
--
-- The two witnesses differ in content.  The fine witness em of
-- Topos.Classicality separates the two interventions.  The
-- pulled-back witness φ em-C separates intervention from
-- observation.  φ-not-surjective shows that a witness of the
-- first kind has no coarse preimage.
-- ------------------------------------------------------------
merge-transfers-gap
  : Σ[ S ∈ Sieve {C = Cv} cObs ]
      (stagewise (φ S) × (¬ (_⊩_ {C = Iv} obs (φ S))))
merge-transfers-gap =
  em-C , (em-C-at-cDo , em-C-at-cDo) , em-C-not-forced

-- ------------------------------------------------------------
-- (1d) TIER 1 AT THE MERGE.  The merge satisfies the back
-- condition: every coarse refinement of the image of a fine
-- context lifts.  cObs lifts to obs, cDo lifts to do0 over obs
-- and to the context itself over do0 and do1.
-- ------------------------------------------------------------
merge-back : BackCond mergeF
merge-back obs cObs h = obs , idₒ , refl
merge-back obs cDo  h = do0 , e0  , refl
merge-back do0 cDo  h = do0 , id₀ , refl
merge-back do0 cObs ()
merge-back do1 cDo  h = do1 , id₁ , refl
merge-back do1 cObs ()

merge-back∥ : BackCond∥ mergeF
merge-back∥ = ∣back∣ mergeF merge-back

-- So Tier 1 applies: the comparison map commutes with Heyting
-- implication, hence with negation.  With the ⊤,⊥,∧,∨ facts of
-- Topos.BaseChange this makes it a morphism of Heyting algebras.
merge-heyting : (c : IObj) (S T : Sieve {C = Cv} (F₀m c))
              → φB mergeF c (_⇒S_ {C = Cv} S T)
              ≡ _⇒S_ {C = Iv} (φB mergeF c S) (φB mergeF c T)
merge-heyting = φB-⇒ mergeF isPropCHom merge-back∥

merge-negation : (c : IObj) (S : Sieve {C = Cv} (F₀m c))
               → φB mergeF c (¬S {C = Cv} S) ≡ ¬S {C = Iv} (φB mergeF c S)
merge-negation = φB-¬ mergeF isPropCHom merge-back∥

-- ------------------------------------------------------------
-- (2d) TIER 2 FAILS.  Order-reflection fails at obs: idd is a
-- coarse arrow between the images of do0 and do1, and there is
-- no fine arrow do0 → do1.
-- ------------------------------------------------------------
merge-no-reflect : ¬ (ReflectAt mergeF obs)
merge-no-reflect r with r {do0} {do1} e0 e1 idd
... | ()

-- ------------------------------------------------------------
-- (2e) The mirror of ci-one: {e1}, the claim holding under
-- do(X:=1) only.  It has no preimage either, by the same
-- argument with the two interventions exchanged.
-- ------------------------------------------------------------
ci-one₁ : Sieve {C = Iv} obs
ci-one₁ = mem , clo
  where
    mem : (d : IObj) → IHom d obs → _
    mem obs idₒ = ⊥ , isProp⊥
    mem do0 e0  = ⊥ , isProp⊥
    mem do1 e1  = Unit* , isPropUnit*
    clo : Closure {C = Iv} obs mem
    clo do1 do1 id₁ e1  pf = tt*
    clo do0 do0 id₀ e0  pf = E.rec pf
    clo obs obs idₒ idₒ pf = E.rec pf
    clo obs do0 e0  idₒ pf = E.rec pf
    clo obs do1 e1  idₒ pf = E.rec pf

φ-not-surjective-e1 : (S : Sieve {C = Cv} cObs) → ¬ (φ S ≡ ci-one₁)
φ-not-surjective-e1 S p =
  subst (λ Q → fst (fst Q do0 e0)) p
        (subst (λ Q → fst (fst Q do1 e1)) (sym p) tt*)
