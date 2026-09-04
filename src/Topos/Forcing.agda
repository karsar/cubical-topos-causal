{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.Forcing — the internal language: Mitchell-Bénabou terms
-- and Kripke-Joyal forcing semantics (Mahadevan's pillar 3).
--
-- A predicate on a presheaf B is a morphism φ : B ⇒ Ω.  It is a
-- B-indexed family of truth values, equivalently a subobject of
-- B.  Kripke-Joyal semantics gives the forcing relation.  Read
-- c ⊩[φ] a as "stage c forces φ at the generalized element a".
-- The definition: the sieve φ_c(a) contains the identity at c.
-- Equivalently, a lies in the classified subobject at stage c.
--
-- The module proves two things:
--   * locality, also called monotonicity.  Forcing is stable
--     under restriction.  This is the defining Kripke property.
--   * the clauses for ⊤, ⊥, ∧, ⇒, ∨, and the clauses for the
--     quantifiers ∀ and ∃.  These follow Mac Lane–Moerdijk VI.6,
--     specialized to a presheaf topos.
--
-- Mahadevan's TCM invokes this layer.  It calls it the internal
-- Mitchell-Bénabou language with Kripke-Joyal semantics.  Here
-- the layer is machine-checked.  ∨ uses the sieve join, which is
-- pointwise union.  ∀_D and ∃_D are the quantifier objects for a
-- predicate on B ×ᴾ D.  ∃ is the local existential, that is, the
-- image in the presheaf sense.
-- ============================================================

module Topos.Forcing where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Functions.Logic using (_⊔_; inl; inr; ⊔-elim; ⇔toPath)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; rec; squash₁)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Unit using (tt*)
open import Cubical.Data.Empty using (⊥*)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.LawvereTierney using (_∧S_)
open import Topos.DoubleNegation using (_⇒S_; ¬S; ⊥S)

module _ {ℓ} {C : Precategory ℓ ℓ} where
  open Precategory C
  open PSh

  -- Meet and implication, pinned at C.  The bare operators leave
  -- {C} a metavariable.
  _∩_ : {c : Ob} → Sieve {C = C} c → Sieve {C = C} c → Sieve {C = C} c
  _∩_ {c} S T = _∧S_ {C = C} {c = c} S T
  _⊃_ : {c : Ob} → Sieve {C = C} c → Sieve {C = C} c → Sieve {C = C} c
  _⊃_ {c} S T = _⇒S_ {C = C} {c = c} S T

  -- ----------------------------------------------------------
  -- Forcing of a truth value at a stage.  c forces S when the
  -- identity at c lies in the sieve S.  The relation is
  -- prop-valued, because sieve membership is prop-valued.
  -- Equivalently, a ∈ the classified subobject.
  -- ----------------------------------------------------------
  _⊩_ : (c : Ob) → Sieve {C = C} c → Type ℓ
  c ⊩ S = fst (fst S c idn)

  -- ⊤ clause: every stage forces truth.
  ⊩-⊤ : (c : Ob) → c ⊩ maximal {C = C} c
  ⊩-⊤ c = tt*

  -- ⊥ clause: no stage forces falsity.
  ⊩-⊥ : (c : Ob) → c ⊩ ⊥S {C = C} c → ⊥*
  ⊩-⊥ c x = x

  -- ∧ clause: c ⊩ S∧T  ⇔  c ⊩ S and c ⊩ T.  The equivalence is
  -- definitional, because meet membership is a product.
  ⊩-∧-fwd : (c : Ob) (S T : Sieve {C = C} c)
          → c ⊩ (S ∩ T) → (c ⊩ S) × (c ⊩ T)
  ⊩-∧-fwd c S T x = x
  ⊩-∧-bwd : (c : Ob) (S T : Sieve {C = C} c)
          → (c ⊩ S) × (c ⊩ T) → c ⊩ (S ∩ T)
  ⊩-∧-bwd c S T x = x

  -- ----------------------------------------------------------
  -- Locality, also called monotonicity.  Forcing is stable under
  -- restriction.  If c ⊩ S then every restriction d → c forces
  -- the pullback of S.
  -- ----------------------------------------------------------
  ⊩-mono : {c : Ob} (S : Sieve {C = C} c) → c ⊩ S
         → {d : Ob} (f : Hom d c) → d ⊩ pull {C = C} f S
  ⊩-mono {c} S s {d} f =
    subst (λ h → fst (fst S d h)) (⋆-idR f ∙ sym (⋆-idL f))
          (snd S c d f idn s)

  -- ----------------------------------------------------------
  -- ⇒ clause:
  --   c ⊩ S⇒T  ⇔  for all f : d → c,  d ⊩ pull f S → d ⊩ pull f T.
  -- The clause quantifies over all restrictions f.  That is where
  -- Kripke-Joyal semantics departs from stagewise truth.
  -- ----------------------------------------------------------
  ⊩-⇒-fwd : (c : Ob) (S T : Sieve {C = C} c)
          → c ⊩ (S ⊃ T)
          → {d : Ob} (f : Hom d c) → d ⊩ pull {C = C} f S → d ⊩ pull {C = C} f T
  ⊩-⇒-fwd c S T H {d} f sf =
    subst (λ h → fst (fst T d h)) (⋆-idR f ∙ sym (⋆-idL f))
      (H d f (subst (λ h → fst (fst S d h)) (⋆-idL f ∙ sym (⋆-idR f)) sf))

  ⊩-⇒-bwd : (c : Ob) (S T : Sieve {C = C} c)
          → ({d : Ob} (f : Hom d c) → d ⊩ pull {C = C} f S → d ⊩ pull {C = C} f T)
          → c ⊩ (S ⊃ T)
  ⊩-⇒-bwd c S T R e g s =
    subst (λ h → fst (fst T e h)) (⋆-idL g ∙ sym (⋆-idR g))
      (R g (subst (λ h → fst (fst S e h)) (⋆-idR g ∙ sym (⋆-idL g)) s))

  -- ----------------------------------------------------------
  -- ∨ clause.  The sieve join is the pointwise union of
  -- membership.  Disjunction in a presheaf topos is local, so the
  -- clause carries a propositional truncation:
  --   c ⊩ S∨T  ⇔  ∥ c ⊩ S  ⊎  c ⊩ T ∥   (definitional).
  -- ----------------------------------------------------------
  _∨S_ : {c : Ob} → Sieve {C = C} c → Sieve {C = C} c → Sieve {C = C} c
  _∨S_ {c} S T =
    (λ d f → fst S d f ⊔ fst T d f) ,
    (λ d e k f → ⊔-elim (fst S d f) (fst T d f)
                   (λ _ → fst S e (k ⋆ f) ⊔ fst T e (k ⋆ f))
                   (λ s → inl (snd S d e k f s))
                   (λ t → inr (snd T d e k f t)))

  ⊩-∨-fwd : (c : Ob) (S T : Sieve {C = C} c)
          → c ⊩ (S ∨S T) → ∥ (c ⊩ S) ⊎ (c ⊩ T) ∥₁
  ⊩-∨-fwd c S T x = x
  ⊩-∨-bwd : (c : Ob) (S T : Sieve {C = C} c)
          → ∥ (c ⊩ S) ⊎ (c ⊩ T) ∥₁ → c ⊩ (S ∨S T)
  ⊩-∨-bwd c S T x = x

  -- ----------------------------------------------------------
  -- The Mitchell-Bénabou layer.  Here φ : B ⇒ Ω is a predicate
  -- and a is a generalized element of B.  The section defines
  -- forcing of φ at a, then proves locality for it.  This
  -- predicate form is the statement in the internal logic.
  -- ----------------------------------------------------------
  module _ {ℓB} {B : PSh C ℓB} (φ : Nat B Ω) where

    _⊩[_]  : (c : Ob) → F₀ B c → Type ℓ
    c ⊩[ a ] = c ⊩ fst φ c a

    -- Kripke locality for predicates.  If a satisfies φ at stage
    -- c, then every restriction of a satisfies φ as well.
    ⊩-pred-mono : {c : Ob} (a : F₀ B c) → c ⊩[ a ]
                → {d : Ob} (f : Hom d c) → d ⊩[ F₁ B f a ]
    ⊩-pred-mono {c} a h {d} f =
      subst (λ S → d ⊩ S) (sym (snd φ d c f a))
            (⊩-mono (fst φ c a) h f)

  -- ----------------------------------------------------------
  -- Quantifiers.  Let φ be a predicate on the product presheaf
  -- B ×ᴾ D.  Then ∀_D φ and ∃_D φ are predicates on B, with D
  -- quantified away.  The Kripke-Joyal clause for ∀ ranges over
  -- all restrictions and over all elements of D.  The clause for
  -- ∃ is the local existential of presheaf semantics.
  -- ----------------------------------------------------------
  module _ {ℓB} {B : PSh C ℓB} {D : PSh C ℓ}
           (φ : Nat (B ×ᴾ D) Ω) where

    -- Local forcing of φ at a (B,D)-pair, at a single stage.
    Φ : (e : Ob) → F₀ B e → F₀ D e → Type ℓ
    Φ e b t = e ⊩ fst φ e (b , t)

    -- ∀_D φ : B ⇒ Ω, the universal quantifier object.
    forAll : Nat B Ω
    forAll =
      (λ c a →
        (λ d f → ((e : Ob) (g : Hom e d) (t : F₀ D e) → Φ e (F₁ B (g ⋆ f) a) t)
               , isPropΠ λ e → isPropΠ λ g → isPropΠ λ t →
                   snd (fst (fst φ e (F₁ B (g ⋆ f) a , t)) e idn)) ,
        (λ d d' k f W e g t →
          subst (λ m → Φ e (F₁ B m a) t) (⋆-assoc g k f) (W e (g ⋆ k) t))) ,
      (λ x y h a →
        Sieve≡ {C = C} _ _
          (funExt λ d → funExt λ f → ⇔toPath
            (λ W e g t → subst (λ b → Φ e b t)
                           (sym (F-comp B (g ⋆ f) h a)
                            ∙ cong (λ m → F₁ B m a) (⋆-assoc g f h)) (W e g t))
            (λ W e g t → subst (λ b → Φ e b t)
                           (sym (sym (F-comp B (g ⋆ f) h a)
                            ∙ cong (λ m → F₁ B m a) (⋆-assoc g f h))) (W e g t))))

    -- ∀ clause: c ⊩ ∀_D φ at a  ⇔  for all f:d→c and all t∈D(d),
    --                                d ⊩ φ at (a·f , t).
    ⊩-∀-fwd : (c : Ob) (a : F₀ B c) → c ⊩ fst forAll c a
            → (d : Ob) (f : Hom d c) (t : F₀ D d) → d ⊩ fst φ d (F₁ B f a , t)
    ⊩-∀-fwd c a W d f t =
      subst (λ b → Φ d b t) (cong (λ m → F₁ B m a) (⋆-idR f)) (W d f t)

    ⊩-∀-bwd : (c : Ob) (a : F₀ B c)
            → ((d : Ob) (f : Hom d c) (t : F₀ D d) → d ⊩ fst φ d (F₁ B f a , t))
            → c ⊩ fst forAll c a
    ⊩-∀-bwd c a R e g t =
      subst (λ b → Φ e b t) (cong (λ m → F₁ B m a) (sym (⋆-idR g))) (R e g t)

    -- ∃_D φ : B ⇒ Ω, the existential quantifier object.  It is
    -- the image of the projection, taken in the local sense of
    -- presheaf semantics.
    exists : Nat B Ω
    exists =
      (λ c a →
        (λ d f → ∥ Σ[ t ∈ F₀ D d ] Φ d (F₁ B f a) t ∥₁ , squash₁) ,
        (λ d d' k f → rec squash₁ (λ (t , w) →
          ∣ (F₁ D k t
            , subst (λ b → Φ d' b (F₁ D k t)) (sym (F-comp B k f a))
                (⊩-pred-mono {B = B ×ᴾ D} φ (F₁ B f a , t) w k)) ∣₁))) ,
      (λ x y h a →
        Sieve≡ {C = C} _ _
          (funExt λ d → funExt λ f → ⇔toPath
            (rec squash₁ (λ (t , w) →
              ∣ (t , subst (λ b → Φ d b t) (sym (F-comp B f h a)) w) ∣₁))
            (rec squash₁ (λ (t , w) →
              ∣ (t , subst (λ b → Φ d b t) (F-comp B f h a) w) ∣₁))))

    -- ∃ clause: c ⊩ ∃_D φ at a  ⇔  ∥ Σ t∈D(c). c ⊩ φ at (a , t) ∥.
    ⊩-∃-fwd : (c : Ob) (a : F₀ B c) → c ⊩ fst exists c a
            → ∥ Σ[ t ∈ F₀ D c ] (c ⊩ fst φ c (a , t)) ∥₁
    ⊩-∃-fwd c a = rec squash₁ (λ (t , w) →
      ∣ (t , subst (λ b → Φ c b t) (F-id B a) w) ∣₁)

    ⊩-∃-bwd : (c : Ob) (a : F₀ B c)
            → ∥ Σ[ t ∈ F₀ D c ] (c ⊩ fst φ c (a , t)) ∥₁
            → c ⊩ fst exists c a
    ⊩-∃-bwd c a = rec squash₁ (λ (t , w) →
      ∣ (t , subst (λ b → Φ c b t) (sym (F-id B a)) w) ∣₁)
