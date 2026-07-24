{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.DoubleNegation — Stage 2 (a): a NON-TRIVIAL Lawvere–
-- Tierney topology, j = ¬¬.
--
-- The trivial topology (Topos.LawvereTierney.trivialLT) makes the
-- modal results (do-j-stable, modal-rule1) hold but vacuously.
-- The double-negation topology is the canonical non-degenerate
-- example: its sheaves are the ¬¬-separated objects, and it is the
-- modality whose internal logic is Boolean.  Instantiating
-- do-j-stable / modal-rule1 at ¬¬ says interventions and Rule 1
-- survive the double-negation (Boolean) localization.
--
-- We first build the Heyting structure on sieves that this needs
-- (bottom ⊥, implication ⇒, negation ¬), then prove ¬¬ satisfies
-- the three Lawvere–Tierney axioms.  Everything is at a single
-- level ℓ so the ∀-quantified implication membership stays in
-- hProp ℓ (= the hom level).
-- ============================================================

module Topos.DoubleNegation where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.Data.Sigma using (_,_; fst; snd)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Data.Empty using (⊥*; isProp⊥*)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.LawvereTierney
open LawvereTierney

module _ {ℓ} {C : Precategory ℓ ℓ} where
  open Precategory C
  open PSh

  -- ----------------------------------------------------------
  -- Heyting structure on sieves.
  -- ----------------------------------------------------------

  -- bottom: the empty sieve (membership is always ⊥)
  ⊥S : (c : Ob) → Sieve {C = C} c
  ⊥S c = (λ d f → ⊥* , isProp⊥*) , (λ d e k f x → x)

  -- Heyting implication: f ∈ (S ⇒ T) iff every restriction of f
  -- that lands in S also lands in T.
  _⇒S_ : {c : Ob} → Sieve {C = C} c → Sieve {C = C} c → Sieve {C = C} c
  _⇒S_ {c} S T =
    (λ d f →
      ( (e : Ob) (g : Hom e d) → fst (fst S e (g ⋆ f)) → fst (fst T e (g ⋆ f)) )
      , isPropΠ λ e → isPropΠ λ g → isPropΠ λ _ → snd (fst T e (g ⋆ f))) ,
    (λ d e k f pf e'' g sm →
      subst (λ h → fst (fst T e'' h)) (⋆-assoc g k f)
        (pf e'' (g ⋆ k)
          (subst (λ h → fst (fst S e'' h)) (sym (⋆-assoc g k f)) sm)))

  -- negation and double negation
  ¬S : {c : Ob} → Sieve {C = C} c → Sieve {C = C} c
  ¬S {c} S = _⇒S_ {c} S (⊥S c)

  ¬¬S : {c : Ob} → Sieve {C = C} c → Sieve {C = C} c
  ¬¬S {c} S = ¬S {c} (¬S {c} S)

  -- ----------------------------------------------------------
  -- ¬¬ satisfies the Lawvere–Tierney axioms.
  -- ----------------------------------------------------------

  -- j ⊤ = ⊤ : ¬¬⊤ = ⊤.  (¬⊤ is empty — apply the witness at idn —
  -- so ¬¬⊤ is inhabited everywhere.)
  j-⊤-¬¬ : (c : Ob) → ¬¬S {c} (maximal {C = C} c) ≡ maximal {C = C} c
  j-⊤-¬¬ c =
    Sieve≡ {C = C} (¬¬S {c} (maximal {C = C} c)) (maximal {C = C} c)
      (funExt λ d → funExt λ f →
        ⇔toPath {Q = Unit* , isPropUnit*}
          (λ _ → tt*)
          (λ _ e g q → q e idn tt*))

  -- ----------------------------------------------------------
  -- Order-theoretic infrastructure for the remaining axioms.
  -- ----------------------------------------------------------

  -- sieve inclusion (the Heyting order)
  _≤S_ : {c : Ob} → Sieve {C = C} c → Sieve {C = C} c → Type ℓ
  _≤S_ {c} S T = (d : Ob) (f : Hom d c) → fst (fst S d f) → fst (fst T d f)

  -- membership is prop-valued, so mutual inclusion is equality
  ≤-antisym : {c : Ob} (S T : Sieve {C = C} c)
            → S ≤S T → T ≤S S → S ≡ T
  ≤-antisym {c} S T p q =
    Sieve≡ {C = C} S T
      (funExt λ d → funExt λ f → ⇔toPath (p d f) (q d f))

  -- p ≤ ¬¬p
  dne-unit : {c : Ob} (S : Sieve {C = C} c) → S ≤S ¬¬S {c} S
  dne-unit {c} S d f s e g r =
    r e idn (subst (λ h → fst (fst S e h)) (sym (⋆-idL (g ⋆ f)))
                   (snd S d e g f s))

  -- negation is antitone: S ≤ T ⟹ ¬T ≤ ¬S
  ¬-anti : {c : Ob} (S T : Sieve {C = C} c)
         → S ≤S T → ¬S {c} T ≤S ¬S {c} S
  ¬-anti {c} S T leq d f nt e g s = nt e g (leq e (g ⋆ f) s)

  -- triple negation: ¬¬¬S = ¬S
  tnn : {c : Ob} (S : Sieve {C = C} c) → ¬S {c} (¬¬S {c} S) ≡ ¬S {c} S
  tnn {c} S =
    ≤-antisym (¬S (¬¬S S)) (¬S S)
      (¬-anti S (¬¬S S) (dne-unit S))   -- ¬¬¬S ≤ ¬S
      (dne-unit (¬S S))                  -- ¬S ≤ ¬¬(¬S) = ¬¬¬S

  -- j idempotent: ¬¬(¬¬S) = ¬¬S, i.e. ¬⁴S = ¬²S, by congruence on tnn
  j-idem-¬¬ : (c : Ob) (S : Sieve {C = C} c)
            → ¬¬S {c} (¬¬S {c} S) ≡ ¬¬S {c} S
  j-idem-¬¬ c S = cong (¬S {c}) (tnn S)

  -- ----------------------------------------------------------
  -- Meet preservation: ¬¬(S ∩ T) = ¬¬S ∩ ¬¬T.
  -- ----------------------------------------------------------

  -- C-pinned meet alias (the bare ∧S leaves its {C} a metavariable)
  _∩_ : {c : Ob} → Sieve {C = C} c → Sieve {C = C} c → Sieve {C = C} c
  _∩_ {c} S T = _∧S_ {C = C} {c = c} S T

  -- meet projections and pairing (∧ membership is a product)
  ∧S-≤L : {c : Ob} (S T : Sieve {C = C} c) → (S ∩ T) ≤S S
  ∧S-≤L S T d f pf = fst pf
  ∧S-≤R : {c : Ob} (S T : Sieve {C = C} c) → (S ∩ T) ≤S T
  ∧S-≤R S T d f pf = snd pf
  ≤-∧S : {c : Ob} (R S T : Sieve {C = C} c)
       → R ≤S S → R ≤S T → R ≤S (S ∩ T)
  ≤-∧S R S T p q d f r = (p d f r , q d f r)

  -- ¬¬ is monotone (two antitone steps)
  ¬¬-mono : {c : Ob} (S T : Sieve {C = C} c)
          → S ≤S T → ¬¬S {c} S ≤S ¬¬S {c} T
  ¬¬-mono S T leq = ¬-anti (¬S T) (¬S S) (¬-anti S T leq)

  -- forward: ¬¬(S∧T) ≤ ¬¬S ∩ ¬¬T  (monotonicity)
  ∧-fwd : {c : Ob} (S T : Sieve {C = C} c)
        → ¬¬S {c} (S ∩ T) ≤S (¬¬S {c} S ∩ ¬¬S {c} T)
  ∧-fwd S T = ≤-∧S (¬¬S (S ∩ T)) (¬¬S S) (¬¬S T)
                (¬¬-mono (S ∩ T) S (∧S-≤L S T))
                (¬¬-mono (S ∩ T) T (∧S-≤R S T))

  -- backward: ¬¬S ∩ ¬¬T ≤ ¬¬(S∧T).  Intuitionistically valid; the
  -- witness restricts both double-negations along the test arrow,
  -- then feeds the refutation r the required (S∧T)-membership built
  -- from an S-witness and a T-witness, reassociating composites.
  ∧-bwd : {c : Ob} (S T : Sieve {C = C} c)
        → (¬¬S {c} S ∩ ¬¬S {c} T) ≤S ¬¬S {c} (S ∩ T)
  ∧-bwd {c} S T d f pf e g r = nns' e idn nsf'
    where
      nns' : fst (fst (¬¬S S) e (g ⋆ f))
      nns' = snd (¬¬S S) d e g f (fst pf)
      nnt' : fst (fst (¬¬S T) e (g ⋆ f))
      nnt' = snd (¬¬S T) d e g f (snd pf)
      nsf : fst (fst (¬S S) e (g ⋆ f))
      nsf e' g' s = nnt' e' g' ntf
        where
          ntf : fst (fst (¬S T) e' (g' ⋆ (g ⋆ f)))
          ntf e'' g'' t =
            r e'' (g'' ⋆ g')
              ( subst (λ m → fst (fst S e'' m)) (sym (⋆-assoc g'' g' (g ⋆ f)))
                      (snd S e' e'' g'' (g' ⋆ (g ⋆ f)) s)
              , subst (λ m → fst (fst T e'' m)) (sym (⋆-assoc g'' g' (g ⋆ f))) t )
      nsf' : fst (fst (¬S S) e (idn ⋆ (g ⋆ f)))
      nsf' = subst (λ m → fst (fst (¬S S) e m)) (sym (⋆-idL (g ⋆ f))) nsf

  j-∧-¬¬ : (c : Ob) (S T : Sieve {C = C} c)
         → ¬¬S {c} (S ∩ T) ≡ (¬¬S {c} S ∩ ¬¬S {c} T)
  j-∧-¬¬ c S T =
    ≤-antisym (¬¬S (S ∩ T)) (¬¬S S ∩ ¬¬S T) (∧-fwd S T) (∧-bwd S T)

  -- ----------------------------------------------------------
  -- Naturality: ¬ (hence ¬¬) commutes with restriction (pullback),
  -- by reassociating the composite test arrows.
  -- ----------------------------------------------------------
  ¬-nat : (x y : Ob) (f : Hom x y) (S : Sieve {C = C} y)
        → ¬S {x} (pull {C = C} f S) ≡ pull {C = C} f (¬S {y} S)
  ¬-nat x y f S =
    Sieve≡ {C = C} (¬S (pull {C = C} f S)) (pull {C = C} f (¬S S))
      (funExt λ d → funExt λ g →
        ⇔toPath
          (λ p e h s → p e h (subst (λ m → fst (fst S e m))
                                    (sym (⋆-assoc h g f)) s))
          (λ q e h s → q e h (subst (λ m → fst (fst S e m))
                                    (⋆-assoc h g f) s)))

  -- ----------------------------------------------------------
  -- The double-negation topology, assembled.  (jnat is inlined so
  -- its expected type — the record field — pins C; ¬¬ commutes with
  -- pullback by applying ¬-nat twice.)
  -- ----------------------------------------------------------
  ¬¬LT : LawvereTierney {C = C}
  ¬¬LT = record
    { jop    = λ c S → ¬¬S {c} S
    ; jnat   = λ x y f S → cong (¬S {x}) (¬-nat x y f S) ∙ ¬-nat x y f (¬S {y} S)
    ; j-⊤    = j-⊤-¬¬
    ; j-idem = j-idem-¬¬
    ; j-∧    = j-∧-¬¬ }
