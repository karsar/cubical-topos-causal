{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.Contextuality — a gluing obstruction: local causal
-- data that is pairwise consistent and has no global model.
--
-- Section 4 (Topos.Gluing) showed that two mechanisms agreeing
-- on an overlap always glue.  The glued object is a pullback,
-- and a pullback is a limit, so it exists in every presheaf
-- topos.  An obstruction needs three contexts.  Over a cover
-- with three measurement contexts, local sections can agree
-- pairwise on every overlap and still have no global section.
-- The sheaf condition then fails.  Abramsky and Brandenburger
-- define (strong) contextuality by this failure.  The module
-- checks it for a causal empirical model.
--
-- The witness is Specker's triangle.  Three Boolean observables
-- A, B, C are measured pairwise.  Each pair is perfectly
-- anti-correlated, and each pair is locally realisable.  The
-- family is compatible: every value of a shared observable
-- occurs in both contexts that contain it, so the marginals
-- agree.  No global assignment exists, because A≠B and B≠C
-- force A=C, against A≠C.
--
-- Scope: this is the support fragment, that is, possibilistic
-- or strong contextuality.  The quantitative Čech-cohomological
-- refinement (Abramsky-Mansfield-Barbosa) and the
-- optimal-transport account of counterfactual obstructions
-- (arXiv:2603.17384) are not formalised here.
-- ============================================================

module Topos.Contextuality where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; not; true≢false; false≢true)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁)
open import Cubical.Relation.Nullary using (¬_)

-- ----------------------------------------------------------
-- The triangle scenario.  A global assignment fixes all three
-- observables.  Each measurement context sees a projected pair.
-- ----------------------------------------------------------
Assign : Type
Assign = Bool × Bool × Bool

obsA : Assign → Bool
obsA v = fst v
obsB : Assign → Bool
obsB v = fst (snd v)
obsC : Assign → Bool
obsC v = snd (snd v)

-- The empirical model records which paired outcomes each context
-- supports.  Specker's model is perfect anti-correlation in
-- every context.
okAB okBC okAC : Bool → Bool → Type
okAB a b = ¬ (a ≡ b)
okBC b c = ¬ (b ≡ c)
okAC a c = ¬ (a ≡ c)

-- A global section is a global assignment that every context
-- supports.
GlobalSection : Type
GlobalSection =
  Σ[ v ∈ Assign ] (okAB (obsA v) (obsB v)
                 × okBC (obsB v) (obsC v)
                 × okAC (obsA v) (obsC v))

-- ----------------------------------------------------------
-- Local consistency: each context is individually realisable.
-- ----------------------------------------------------------
local-AB : Σ[ ab ∈ Bool × Bool ] okAB (fst ab) (snd ab)
local-AB = (true , false) , true≢false
local-BC : Σ[ bc ∈ Bool × Bool ] okBC (fst bc) (snd bc)
local-BC = (true , false) , true≢false
local-AC : Σ[ ac ∈ Bool × Bool ] okAC (fst ac) (snd ac)
local-AC = (true , false) , true≢false

-- ----------------------------------------------------------
-- Compatibility, which is no-signalling at the support level.
-- Every value of a shared observable occurs in both contexts
-- that contain it, so the single-observable marginals agree.
-- The proofs below rest on a ≠ not a.
-- ----------------------------------------------------------
a≢nota : (a : Bool) → ¬ (a ≡ not a)
a≢nota true  p = true≢false p
a≢nota false p = false≢true p

realA-AB : (a : Bool) → ∥ Σ[ b ∈ Bool ] okAB a b ∥₁
realA-AB a = ∣ not a , a≢nota a ∣₁
realA-AC : (a : Bool) → ∥ Σ[ c ∈ Bool ] okAC a c ∥₁
realA-AC a = ∣ not a , a≢nota a ∣₁
realB-AB : (b : Bool) → ∥ Σ[ a ∈ Bool ] okAB a b ∥₁
realB-AB b = ∣ not b , (λ p → a≢nota b (sym p)) ∣₁
realB-BC : (b : Bool) → ∥ Σ[ c ∈ Bool ] okBC b c ∥₁
realB-BC b = ∣ not b , a≢nota b ∣₁
realC-BC : (c : Bool) → ∥ Σ[ b ∈ Bool ] okBC b c ∥₁
realC-BC c = ∣ not c , (λ p → a≢nota c (sym p)) ∣₁
realC-AC : (c : Bool) → ∥ Σ[ a ∈ Bool ] okAC a c ∥₁
realC-AC c = ∣ not c , (λ p → a≢nota c (sym p)) ∣₁

-- ----------------------------------------------------------
-- The obstruction.  The compatible, locally consistent family
-- has no global section.  A≠B and B≠C force A=C, which
-- contradicts A≠C.
-- ----------------------------------------------------------
no-global : ¬ GlobalSection
no-global ((true  , true  , _    ) , p , _ , _) = p refl
no-global ((false , false , _    ) , p , _ , _) = p refl
no-global ((true  , false , true ) , _ , _ , r) = r refl
no-global ((true  , false , false) , _ , q , _) = q refl
no-global ((false , true  , true ) , _ , q , _) = q refl
no-global ((false , true  , false) , _ , _ , r) = r refl

-- ----------------------------------------------------------
-- The two halves packaged.  Specker's causal empirical model is
-- strongly contextual: a compatible family of local sections
-- with no amalgamation.
-- ----------------------------------------------------------
record StrongContextuality : Type where
  field
    locally-realisable : (Σ[ ab ∈ Bool × Bool ] okAB (fst ab) (snd ab))
                       × (Σ[ bc ∈ Bool × Bool ] okBC (fst bc) (snd bc))
                       × (Σ[ ac ∈ Bool × Bool ] okAC (fst ac) (snd ac))
    no-amalgamation    : ¬ GlobalSection

specker-contextual : StrongContextuality
specker-contextual = record
  { locally-realisable = local-AB , local-BC , local-AC
  ; no-amalgamation    = no-global }
