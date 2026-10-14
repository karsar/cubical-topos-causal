{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.SubModelArrow: over finite state spaces, a monic arrow
-- from the intervened model into its parent is an isomorphism.
--
-- The source reads an intervention as a sub-model: a monic
-- arrow M_x ↪ M.  We work in the arrow topos, the setting of
-- the source's own worked classifier.  There a causal model is
-- a function F : U → V from exogenous states to endogenous
-- states.  The source draws the arrow as a commuting square
-- whose two vertical maps are injective:
--
--          i
--     U ------> U
--     |         |
--  Fx |         | F
--     v         v
--     V ------> V
--          j
--
-- Pearl's M_x has the same variables and state spaces as M.
-- Only the equation for X changes.  So the square has the same
-- U and the same V at the top and at the bottom.
--
-- An injective map from a finite set to itself is a bijection.
-- This is the pigeonhole principle.  So i and j are bijections,
-- and the square is an isomorphism.  It presents M_x as M with
-- its states renamed.  As a subobject of M it is all of M, so
-- its characteristic map is constantly true.
--
-- Results:
--   fin-inj-surj        an injective map Fin n → Fin n hits
--                       every element.
--   finset-inj-equiv    an injective map from a finite set to
--                       itself is an equivalence.
--   i-equiv, j-equiv    in a sub-model square over the same
--                       finite state spaces, both vertical maps
--                       are equivalences.
--   covers-U, covers-V  the sub-model meets every state of M.
--                       So it is the whole of M.
--   relabel             Fx is F with its states renamed.
--   inverse-square      the inverse maps also form a square, so
--                       the square is an isomorphism.
--   unchanged-case      if i and j are identities, then Fx = F,
--                       and nothing is intervened on.
--
-- Example (perfect confounding, X := U, Y := U, do(X := true)):
--   confounded-square   a sub-model square from M_x into M
--                       exists.
--   intervention-changes-model   but M_x is not M.
--   confounded-whole    by the theorem, the square meets every
--                       state of M: it is the whole of M.
--   So the arrow exists only as a renaming of states.
--
--   conditioning-square the part of M where X = true is a
--                       proper sub-model, with a smaller U.
--   conditioning-fixes-Y on that part, Y is always true.
--   intervention-frees-Y under do(X := true), Y can be false.
--   So the proper sub-model describes conditioning, not
--   intervention.
-- ============================================================

module Topos.SubModelArrow where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding using (injEmbedding)
open import Cubical.Functions.Surjection
  using (isSurjection; isEmbedding×isSurjection→isEquiv)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∣_∣₁)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
  using (Bool; true; false; not; true≢false; isSetBool)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_; yes; no)

open import Cubical.Data.Fin.Base using (Fin; ¬Fin0; any?)
open import Cubical.Data.Fin.Properties
  using (discreteFin; pigeonhole-special)
open import Cubical.Data.Fin.LehmerCode
  using (punchOut; punchOut-injective)
open import Cubical.Data.SumFin.Properties using (SumFin≃Fin)
open import Cubical.Data.FinSet.Base using (isFinSet; isFinSet→isSet)
open import Cubical.Data.FinSet.Properties using (isFinSetBool)
open import Cubical.Data.FinSet.Constructors using (isFinSet×)

private
  variable
    ℓ ℓ' : Level

-- A map is injective when equal outputs come from equal inputs.
Injective : {A : Type ℓ} {B : Type ℓ'} → (A → B) → Type (ℓ-max ℓ ℓ')
Injective f = ∀ {a b} → f a ≡ f b → a ≡ b

-- ------------------------------------------------------------
-- Pigeonhole: an injective map Fin n → Fin n is surjective.
--
-- Suppose that f misses some y.  Then f maps the n elements of
-- Fin n into the n - 1 elements other than y.  The pigeonhole
-- principle gives two different inputs with the same output.
-- This contradicts injectivity.  Whether f hits y is decidable,
-- because Fin n is finite and has decidable equality.  So the
-- argument gives the preimage itself, not only its existence.
-- ------------------------------------------------------------
fin-inj-surj : {n : ℕ} (f : Fin n → Fin n) → Injective f
             → (y : Fin n) → fiber f y
fin-inj-surj {zero}  f inj y = ⊥.rec (¬Fin0 y)
fin-inj-surj {suc k} f inj y with any? (λ x → discreteFin (f x) y)
... | yes hit  = hit
... | no  miss = ⊥.rec (clash (pigeonhole-special squeeze))
  where
  -- Every output of f differs from y.
  avoids : (x : Fin (suc k)) → ¬ (y ≡ f x)
  avoids x p = miss (x , sym p)

  -- f, read as a map into the elements other than y.
  squeeze : Fin (suc k) → Fin k
  squeeze x = punchOut y (f x , avoids x)

  clash : Σ[ a ∈ Fin (suc k) ] Σ[ b ∈ Fin (suc k) ]
            (¬ a ≡ b) × (squeeze a ≡ squeeze b) → ⊥
  clash (a , b , a≢b , same) =
    a≢b (inj (cong fst (punchOut-injective y _ _ same)))

-- An equivalence is injective.
equiv-inj : {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) → Injective (equivFun e)
equiv-inj e {a} {b} p = sym (retEq e a) ∙ cong (invEq e) p ∙ retEq e b

-- ------------------------------------------------------------
-- The same for every finite set.
--
-- A finite set U comes with a merely given equivalence to some
-- Fin n.  We move u along that equivalence and apply the
-- pigeonhole lemma.  Being an equivalence is a proposition, so
-- the mere equivalence is enough.
-- ------------------------------------------------------------
module _ {U : Type ℓ} (finU : isFinSet U) (u : U → U) (inj : Injective u)
  where

  finset-inj-surj : isSurjection u
  finset-inj-surj y = PT.rec PT.isPropPropTrunc
    (λ e → ∣ from-fin (compEquiv e (SumFin≃Fin (finU .fst))) ∣₁)
    (finU .snd)
    where
    from-fin : U ≃ Fin (finU .fst) → fiber u y
    from-fin E = invEq E a , equiv-inj E (lemma ∙ hits)
      where
      f : Fin (finU .fst) → Fin (finU .fst)
      f k = equivFun E (u (invEq E k))

      f-inj : Injective f
      f-inj p = sym (secEq E _)
              ∙ cong (equivFun E) (inj (equiv-inj E p))
              ∙ secEq E _

      a : Fin (finU .fst)
      a = fin-inj-surj f f-inj (equivFun E y) .fst

      hits : f a ≡ equivFun E y
      hits = fin-inj-surj f f-inj (equivFun E y) .snd

      lemma : equivFun E (u (invEq E a)) ≡ f a
      lemma = refl

  finset-inj-equiv : isEquiv u
  finset-inj-equiv = isEmbedding×isSurjection→isEquiv
    (injEmbedding (isFinSet→isSet finU) inj , finset-inj-surj)

-- ------------------------------------------------------------
-- Monic arrows in the arrow category.
--
-- An object is a function g : U → V.  A monic arrow from
-- f : U' → V' into g is a commuting square whose two vertical
-- maps are injective.  This is the form in which the source
-- draws a sub-model.
-- ------------------------------------------------------------
record ArrowMono {U' V' U V : Type ℓ}
                 (f : U' → V') (g : U → V) : Type ℓ where
  field
    i      : U' → U
    j      : V' → V
    i-inj  : Injective i
    j-inj  : Injective j
    square : ∀ a → g (i a) ≡ j (f a)

-- ------------------------------------------------------------
-- The theorem.  Pearl's M_x keeps the state spaces of M.  So we
-- take U' = U and V' = V, both finite.
-- ------------------------------------------------------------
module SameStates {U V : Type ℓ}
  (finU : isFinSet U) (finV : isFinSet V)
  {Fx F : U → V} (m : ArrowMono Fx F)
  where
  open ArrowMono m

  i-equiv : isEquiv i
  i-equiv = finset-inj-equiv finU i i-inj

  j-equiv : isEquiv j
  j-equiv = finset-inj-equiv finV j j-inj

  iE : U ≃ U
  iE = i , i-equiv

  jE : V ≃ V
  jE = j , j-equiv

  -- The sub-model meets every state of M.  So the subobject is
  -- the whole of M, and its characteristic map is constantly
  -- true.
  covers-U : (a : U) → fiber i a
  covers-U a = invEq iE a , secEq iE a

  covers-V : (b : V) → fiber j b
  covers-V b = invEq jE b , secEq jE b

  -- Fx is F with its states renamed: rename the exogenous state
  -- by i, apply F, and rename back by the inverse of j.
  relabel : Fx ≡ (λ a → invEq jE (F (i a)))
  relabel = funExt λ a →
    sym (retEq jE (Fx a)) ∙ cong (invEq jE) (sym (square a))

  -- The inverse maps also commute with the two functions.  So
  -- the square has an inverse square, and it is an isomorphism
  -- in the arrow category.
  inverse-square : ∀ a → Fx (invEq iE a) ≡ invEq jE (F a)
  inverse-square a =
    funExt⁻ relabel (invEq iE a) ∙ cong (λ c → invEq jE (F c)) (secEq iE a)

-- If both vertical maps are identities, the square says Fx = F.
-- Then the intervention changes nothing.
unchanged-case : {U V : Type ℓ} {Fx F : U → V}
               → (∀ a → F a ≡ Fx a) → Fx ≡ F
unchanged-case sq = funExt λ a → sym (sq a)

-- ------------------------------------------------------------
-- Example: perfect confounding.
--
-- One exogenous variable U : Bool.  Two endogenous variables,
-- X := U and Y := U.  So a state of V is a pair (x , y).
-- The intervention do(X := true) replaces the equation for X by
-- the constant true.  The variables and state spaces stay the
-- same.
-- ------------------------------------------------------------
F-conf : Bool → Bool × Bool
F-conf u = u , u

Fx-conf : Bool → Bool × Bool
Fx-conf u = true , u

-- The renaming of V that turns Fx-conf into F-conf.  It sends
-- (true , y) to (y , y), and (false , y) to (y , not y).
rename : Bool × Bool → Bool × Bool
rename (true  , y) = y , y
rename (false , y) = y , not y

rename⁻ : Bool × Bool → Bool × Bool
rename⁻ (true  , true ) = true  , true
rename⁻ (true  , false) = false , true
rename⁻ (false , true ) = false , false
rename⁻ (false , false) = true  , false

rename-ret : ∀ s → rename⁻ (rename s) ≡ s
rename-ret (true  , true ) = refl
rename-ret (true  , false) = refl
rename-ret (false , true ) = refl
rename-ret (false , false) = refl

rename-inj : Injective rename
rename-inj {a} {b} p = sym (rename-ret a) ∙ cong rename⁻ p ∙ rename-ret b

-- A sub-model square from M_x into M exists.
confounded-square : ArrowMono Fx-conf F-conf
confounded-square = record
  { i      = λ u → u
  ; j      = rename
  ; i-inj  = λ p → p
  ; j-inj  = rename-inj
  ; square = λ u → refl
  }

-- But M_x is not M: at u = false they disagree on X.
intervention-changes-model : ¬ (Fx-conf ≡ F-conf)
intervention-changes-model p = true≢false (cong fst (funExt⁻ p false))

-- So, by the theorem, confounded-square is an isomorphism.  It
-- records M_x only as M with its states renamed.
isFinSetBool×Bool : isFinSet (Bool × Bool)
isFinSetBool×Bool = isFinSet× (Bool , isFinSetBool) (Bool , isFinSetBool)

module Confounded =
  SameStates isFinSetBool isFinSetBool×Bool confounded-square

confounded-whole : (s : Bool × Bool) → fiber rename s
confounded-whole = Confounded.covers-V

confounded-relabel : Fx-conf ≡ (λ u → invEq Confounded.jE (F-conf u))
confounded-relabel = Confounded.relabel

-- ------------------------------------------------------------
-- A proper sub-model needs a smaller state space.  The natural
-- one is the part of M where X = true.
-- ------------------------------------------------------------
U-cond : Type
U-cond = Σ[ u ∈ Bool ] fst (F-conf u) ≡ true

F-cond : U-cond → Bool × Bool
F-cond w = F-conf (fst w)

conditioning-square : ArrowMono F-cond F-conf
conditioning-square = record
  { i      = fst
  ; j      = λ s → s
  ; i-inj  = λ p → Σ≡Prop (λ _ → isSetBool _ _) p
  ; j-inj  = λ p → p
  ; square = λ w → refl
  }

-- On that part, Y is always true.  This is conditioning on
-- X = true: in this model Y copies U, and X = true forces
-- U = true.
conditioning-fixes-Y : (w : U-cond) → snd (F-cond w) ≡ true
conditioning-fixes-Y (u , p) = p

-- Under do(X := true), Y can still be false.
intervention-frees-Y : snd (Fx-conf false) ≡ false
intervention-frees-Y = refl
