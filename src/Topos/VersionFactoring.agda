{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.VersionFactoring — well-definedness of a causal effect
-- as an internal truth value.
--
-- Hernán and Taubman object that an observational study of body
-- mass index does not name the intervention: different means of
-- reaching the same BMI may give different mortality outcomes.
-- Pearl replies that do(X := x) is manipulation-neutral by
-- construction, and that indexing it by the means would be a
-- different operator.  The assumption that closes the gap is
-- VanderWeele and Hernán's TREATMENT VARIATION IRRELEVANCE: the
-- outcome under treatment value x is the same whichever version
-- of x occurred.
--
-- Formalised here, the two worlds differ in ONE object and share
-- the site.  Ver is the object of VERSIONS (Hernán), Val the
-- object of VALUES (Pearl), and p : Ver ⇒ Val is the coarsening.
-- A mechanism is an element of Exp Ver (Dist_E Out): the outcome
-- distribution as a function of the version.  Treatment variation
-- irrelevance is the statement that the mechanism FACTORS THROUGH
-- p, that is, that versions with the same value give the same
-- outcome.
--
-- Results:
--   SameVal-closed   "same value" is itself closed under
--                    restriction (this uses naturality of p).
--   Factors-closed   the HEREDITARY factoring predicate is closed
--                    under restriction, with NO condition on the
--                    site.  The proof is Adm-closed's, verbatim
--                    plus two instantiations.
--   χ-wd             hence the characteristic map Mech ⇒ Ω, with
--                    the classification theorem and uniqueness,
--                    from Topos.Classifier.
--   Here             the STAGEWISE reading: well-definedness at
--                    this regime only.  Factors→Here always.
--   Factors↔AllHere  Factors is exactly the hereditary closure of
--                    Here: "well defined here and in every
--                    refinement".  This is the Kripke-Joyal
--                    reading of the internal ∀, and it is why
--                    Factors, unlike Here, is a truth value.
--   Here→Factors     the converse of Factors→Here needs a
--                    condition on the site: LiftPairs, that every
--                    same-value pair at a refinement is the
--                    restriction of a same-value pair upstairs.
--                    That is "refinement adds no versions".
--   Here-closed      under LiftPairs the stagewise predicate is
--                    itself closed under restriction.  This is
--                    the exact form of the conjecture that
--                    factoring is down-closed when refinement
--                    narrows the available versions: it is TRUE
--                    of the stagewise reading, and VACUOUS for
--                    the hereditary one, which is down-closed
--                    with no condition at all.
--   ungraded         under LiftPairs the sieve is maximal exactly
--                    when the stagewise reading holds.  NOTE this
--                    does NOT make the truth value Boolean: the
--                    sieve can still be proper, because the
--                    stagewise property can vary from regime to
--                    regime.  LiftPairs removes one source of
--                    grading (the hereditary/stagewise gap), not
--                    the other (genuine regime-dependence).
--
-- The reading: well-definedness of a causal effect is a truth
-- value in Ω, not a Boolean.  Topos.VersionSite exhibits a site
-- on which it is a proper sieve.
-- ============================================================

module Topos.VersionFactoring where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁)
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Empty as E using (⊥; ⊥*; isProp⊥*)

open import FDist-Convex using (FDist; trunc)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.InternalDist
open import Topos.Exponential
open import Topos.BaseChange using (BaseFunctor)
open import Topos.DoubleNegation using (⊥S)
open import Topos.Classifier using (Classifies; χ; χ-sieve; χ-classifies; unique)

module _ {ℓ} {C : Precategory ℓ ℓ}
         (Ver Val : PSh C ℓ) (p : Nat {C = C} Ver Val) (Out : PSh C ℓ) where
  open Precategory C
  open PSh

  -- ----------------------------------------------------------
  -- The mechanism object of the FINE world.  Its input is the
  -- version, not the value; that is the whole of Hernán's point.
  -- ----------------------------------------------------------
  MechV : PSh C ℓ
  MechV = Exp {C = C} Ver (Dist_E {C = C} Out)

  -- ----------------------------------------------------------
  -- Two versions with the same value, at a stage.
  -- ----------------------------------------------------------
  SameVal : (d : Ob) → F₀ Ver d → F₀ Ver d → Type ℓ
  SameVal d a b = fst p d a ≡ fst p d b

  isPropSameVal : (d : Ob) (a b : F₀ Ver d) → isProp (SameVal d a b)
  isPropSameVal d a b = isSetF₀ Val d _ _

  -- Having the same value is closed under restriction.  This is
  -- the one place naturality of the coarsening is used: it makes
  -- the relation a subpresheaf of Ver ×ᴾ Ver.
  SameVal-closed : (d e : Ob) (k : Hom e d) (a b : F₀ Ver d)
                 → SameVal d a b → SameVal e (F₁ Ver k a) (F₁ Ver k b)
  SameVal-closed d e k a b q =
    snd p e d k a ∙ cong (F₁ Val k) q ∙ sym (snd p e d k b)

  -- ----------------------------------------------------------
  -- TREATMENT VARIATION IRRELEVANCE, hereditary form.  The
  -- mechanism factors through p at c and at every stage below c.
  -- The quantifier over arrows into c is the Kripke-Joyal reading
  -- of the internal ∀; it is what makes the predicate a sieve.
  -- ----------------------------------------------------------
  Factors : (c : Ob) → F₀ MechV c → hProp ℓ
  Factors c m =
    ( (d : Ob) (g : Hom d c) (a b : F₀ Ver d)
      → SameVal d a b → fst m d g a ≡ fst m d g b )
    , isPropΠ λ d → isPropΠ λ g → isPropΠ λ a → isPropΠ λ b →
      isPropΠ λ _ → trunc _ _

  -- ----------------------------------------------------------
  -- CLOSURE UNDER RESTRICTION, with no condition on the site.
  -- Restricting a mechanism precomposes its index arrow, so a
  -- witness at d is reused at e by composing.  This is exactly
  -- MechanismObject.Adm-closed, with the two extra version
  -- arguments carried along unchanged: at the stage d' the
  -- quantifier ranges over F₀ Ver d' whichever route reached d'.
  -- ----------------------------------------------------------
  Factors-closed : (d e : Ob) (k : Hom e d) (m : F₀ MechV d)
                 → fst (Factors d m) → fst (Factors e (F₁ MechV k m))
  Factors-closed d e k m h d' g a b q = h d' (g ⋆ k) a b q

  -- ----------------------------------------------------------
  -- The classifier of well-definedness.
  -- ----------------------------------------------------------
  χ-wd : Nat MechV (Ω {C = C})
  χ-wd = χ MechV Factors Factors-closed

  χ-wd-sieve : (c : Ob) → F₀ MechV c → Sieve {C = C} c
  χ-wd-sieve = χ-sieve MechV Factors Factors-closed

  χ-wd-classifies : Classifies MechV Factors Factors-closed (λ c m → χ-wd-sieve c m)
  χ-wd-classifies = χ-classifies MechV Factors Factors-closed

  χ-wd-unique : (χ' : Nat MechV (Ω {C = C}))
              → Classifies MechV Factors Factors-closed (fst χ') → χ' ≡ χ-wd
  χ-wd-unique = unique MechV Factors Factors-closed

  -- ----------------------------------------------------------
  -- THE STAGEWISE READING.  "The effect is well defined in this
  -- regime", with no reference to refinements.  This is how both
  -- Pearl and Hernán use the phrase.
  -- ----------------------------------------------------------
  Here : (c : Ob) → F₀ MechV c → Type ℓ
  Here c m = (a b : F₀ Ver c) → SameVal c a b → fst m c idn a ≡ fst m c idn b

  isPropHere : (c : Ob) (m : F₀ MechV c) → isProp (Here c m)
  isPropHere c m = isPropΠ λ a → isPropΠ λ b → isPropΠ λ _ → trunc _ _

  Factors→Here : (c : Ob) (m : F₀ MechV c) → fst (Factors c m) → Here c m
  Factors→Here c m h = h c idn

  -- ----------------------------------------------------------
  -- Factors IS the hereditary closure of Here.  Both directions
  -- are unconditional.  So the predicate the classifier sees is
  -- "well defined at this regime and at every refinement of it",
  -- which is the Kripke-Joyal semantics of the internal ∀ over
  -- refinements.  That is the whole reason it is restriction-
  -- stable, and it is what the stagewise reading lacks.
  -- ----------------------------------------------------------
  Factors→AllHere : (c : Ob) (m : F₀ MechV c) → fst (Factors c m)
                  → (d : Ob) (g : Hom d c) → Here d (F₁ MechV g m)
  Factors→AllHere c m h d g =
    Factors→Here d (F₁ MechV g m) (Factors-closed c d g m h)

  AllHere→Factors : (c : Ob) (m : F₀ MechV c)
                  → ((d : Ob) (g : Hom d c) → Here d (F₁ MechV g m))
                  → fst (Factors c m)
  AllHere→Factors c m hh d g a b q =
    subst (λ h → fst m d h a ≡ fst m d h b) (⋆-idL g) (hh d g a b q)

  -- ----------------------------------------------------------
  -- THE CONDITION ON THE SITE.  Every same-value pair at a stage
  -- below c is the restriction of a same-value pair at c.  In
  -- words: refinement makes no NEW versions available.  This is
  -- the author's hypothesis, in its sharp form; note it is a
  -- lifting condition on the version presheaf, not a mere
  -- inclusion of version sets.
  -- ----------------------------------------------------------
  LiftPairs : (c : Ob) → Type ℓ
  LiftPairs c =
    (d : Ob) (f : Hom d c) (a' b' : F₀ Ver d) → SameVal d a' b'
    → ∥ Σ[ a ∈ F₀ Ver c ] Σ[ b ∈ F₀ Ver c ]
          ( SameVal c a b × (F₁ Ver f a ≡ a') × (F₁ Ver f b ≡ b') ) ∥₁

  -- Under LiftPairs the stagewise reading implies the hereditary
  -- one.  The transport is naturality of the exponential: the
  -- mechanism at c restricts to the mechanism at d.
  Here→Factors : (c : Ob) → LiftPairs c → (m : F₀ MechV c)
               → Here c m → fst (Factors c m)
  Here→Factors c lp m hh d g a' b' q = PT.rec (trunc _ _) step (lp d g a' b' q)
    where
      key : (a : F₀ Ver c)
          → fst m d g (F₁ Ver g a) ≡ F₁ (Dist_E {C = C} Out) g (fst m c idn a)
      key a =
        subst (λ h → fst m d h (F₁ Ver g a)
                     ≡ F₁ (Dist_E {C = C} Out) g (fst m c idn a))
              (⋆-idR g)
              (snd m d c g idn a)
      step : Σ[ a ∈ F₀ Ver c ] Σ[ b ∈ F₀ Ver c ]
               ( SameVal c a b × (F₁ Ver g a ≡ a') × (F₁ Ver g b ≡ b') )
           → fst m d g a' ≡ fst m d g b'
      step (a , b , sv , ea , eb) =
          cong (fst m d g) (sym ea)
        ∙ key a
        ∙ cong (F₁ (Dist_E {C = C} Out) g) (hh a b sv)
        ∙ sym (key b)
        ∙ cong (fst m d g) eb

  -- The conjecture, in its true form.  When refinement adds no
  -- versions the stagewise predicate IS closed under restriction.
  -- The proof is Here→Factors, then Factors-closed, then
  -- Factors→Here: the hereditary predicate is the vehicle.
  Here-closed : (d e : Ob) (k : Hom e d) → LiftPairs d → (m : F₀ MechV d)
              → Here d m → Here e (F₁ MechV k m)
  Here-closed d e k lp m h =
    Factors→Here e (F₁ MechV k m)
      (Factors-closed d e k m (Here→Factors d lp m h))

  -- Under LiftPairs the two readings agree at c.  This does NOT
  -- say the sieve is ⊥ or ⊤; see the header.
  ungraded : (c : Ob) → LiftPairs c → (m : F₀ MechV c)
           → ( Here c m → χ-wd-sieve c m ≡ maximal {C = C} c )
           × ( χ-wd-sieve c m ≡ maximal {C = C} c → Here c m )
  ungraded c lp m =
    (λ h → fst (χ-wd-classifies c m) (Here→Factors c lp m h)) ,
    (λ eq → Factors→Here c m (snd (χ-wd-classifies c m) eq))

  -- ----------------------------------------------------------
  -- THE OTHER SOURCE OF GRADING, and how to switch it off.
  --
  -- An outcome presheaf is FAITHFUL when no refinement loses
  -- outcome information: restriction of outcome distributions is
  -- injective.  Topos.MechanismSite gets its non-maximal sieve by
  -- breaking exactly this — there the value type collapses to a
  -- point at do0, so anything is admissible there.  With faithful
  -- outcomes that route is closed.
  -- ----------------------------------------------------------
  OutFaithful : Type ℓ
  OutFaithful =
    (d e : Ob) (k : Hom e d) (u v : F₀ (Dist_E {C = C} Out) d)
    → F₁ (Dist_E {C = C} Out) k u ≡ F₁ (Dist_E {C = C} Out) k v → u ≡ v

  -- With faithful outcomes the stagewise reading REFLECTS along
  -- refinement: if the effect is well defined in a refinement it
  -- was already well defined upstairs.  No lifting condition is
  -- needed for this direction.
  Here-reflect : OutFaithful → (d e : Ob) (k : Hom e d) (m : F₀ MechV d)
               → Here e (F₁ MechV k m) → Here d m
  Here-reflect fa d e k m h a b q =
    fa d e k (fst m d idn a) (fst m d idn b) (sym (keyk a) ∙ hk ∙ keyk b)
    where
      keyk : (x : F₀ Ver d)
           → fst m e k (F₁ Ver k x) ≡ F₁ (Dist_E {C = C} Out) k (fst m d idn x)
      keyk x =
        subst (λ h' → fst m e h' (F₁ Ver k x)
                      ≡ F₁ (Dist_E {C = C} Out) k (fst m d idn x))
              (⋆-idR k) (snd m e d k idn x)
      hk : fst m e k (F₁ Ver k a) ≡ fst m e k (F₁ Ver k b)
      hk = subst (λ h' → fst m e h' (F₁ Ver k a) ≡ fst m e h' (F₁ Ver k b))
                 (⋆-idL k)
                 (h (F₁ Ver k a) (F₁ Ver k b) (SameVal-closed d e k a b q))

  -- So with faithful outcomes, failure of the stagewise reading
  -- at c empties the whole sieve.
  notHere→⊥ : OutFaithful → (c : Ob) (m : F₀ MechV c) → ¬ (Here c m)
            → χ-wd-sieve c m ≡ ⊥S {C = C} c
  notHere→⊥ fa c m nh =
    Sieve≡ {C = C} (χ-wd-sieve c m) (⊥S {C = C} c)
      (funExt λ d → funExt λ f →
        ⇔toPath {P = Factors d (F₁ MechV f m)} {Q = (⊥* , isProp⊥*)}
          (λ hf → E.rec (nh (Here-reflect fa c d f m
                              (Factors→Here d (F₁ MechV f m) hf))))
          E.rec*)

  -- ----------------------------------------------------------
  -- THE DICHOTOMY.  Under faithful outcomes AND LiftPairs the
  -- truth value is two-valued: a sieve that is not maximal is
  -- empty.  Contrapositively, a PROPER classifying sieve — a
  -- genuinely graded well-definedness — requires either that
  -- refinement adds versions, or that refinement loses outcome
  -- information.
  --
  -- This inverts the stated risk.  Refinement adding versions is
  -- not a threat to the construction; with faithful outcomes it
  -- is the ONLY thing that makes the truth value interesting.
  -- ----------------------------------------------------------
  two-valued : OutFaithful → (c : Ob) → LiftPairs c → (m : F₀ MechV c)
             → ¬ (χ-wd-sieve c m ≡ maximal {C = C} c)
             → χ-wd-sieve c m ≡ ⊥S {C = C} c
  two-valued fa c lp m nmax =
    notHere→⊥ fa c m (λ h → nmax (fst (ungraded c lp m) h))

-- ------------------------------------------------------------
-- Transfer along an abstraction of regimes.  Topos.MechanismGeometric
-- notes that admissibility, being an equation, survives every base
-- functor, while quantified statements are supposed to need a side
-- condition.  Factoring IS a quantified statement, and it survives
-- too.  The reason is that the quantifier over versions ranges over
-- a PULLED-BACK object, so no new elements appear; the side
-- condition of Topos.AbstractionTiers is about ⇒, where the
-- quantifier ranges over refinements the fine site may not see.
-- ------------------------------------------------------------
module _ {ℓ} {C D : Precategory ℓ ℓ} (F : BaseFunctor C D)
         (Ver Val : PSh D ℓ) (p : Nat {C = D} Ver Val) (Out : PSh D ℓ) where
  private
    module Cc = Precategory C
    module Dc = Precategory D
  open BaseFunctor F
  open PSh

  Factors-pullback :
      (c : Cc.Ob) (m : F₀ (MechV Ver Val p Out) (App₀ c))
    → fst (Factors Ver Val p Out (App₀ c) m)
    → (d : Cc.Ob) (g : Cc.Hom d c) (a b : F₀ Ver (App₀ d))
    → SameVal Ver Val p Out (App₀ d) a b
    → fst m (App₀ d) (App₁ g) a ≡ fst m (App₀ d) (App₁ g) b
  Factors-pullback c m h d g a b q = h (App₀ d) (App₁ g) a b q
