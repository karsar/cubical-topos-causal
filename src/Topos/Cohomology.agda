{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.Cohomology — the cohomological refinement of the
-- contextuality obstruction.
--
-- Topos.Contextuality showed that Specker's empirical model has
-- no global section.  That is a possibilistic obstruction.
-- Abramsky, Mansfield and Barbosa refine it to a cohomological
-- invariant: the obstruction is a non-zero class in the first
-- Čech cohomology of the cover.
--
-- For the triangle the cover has three measurement contexts, the
-- edges, on three observables, the vertices.  The relevant
-- cohomology is that of a loop with Z₂ coefficients, so
-- H¹ ≅ Z₂.  A global model is a vertex labelling, a 0-cochain,
-- whose coboundary δ realises the observed pairwise
-- correlations, a 1-cochain.  Specker's model is the 1-cocycle
-- that is anti-correlated on every edge.  Its holonomy is 1,
-- where holonomy means the loop sum, the generator of H¹ ≅ Z₂.
-- Every coboundary has holonomy 0, so Specker's cocycle is not a
-- coboundary.  The class it names is the contextuality
-- obstruction, and it recovers the possibilistic no-global of
-- Topos.Contextuality.
--
-- Scope: the cohomology of this one cover is given concretely.
-- The general Čech apparatus, the nerve of an arbitrary cover
-- and the full cochain complex, is left to future work.
-- ============================================================

module Topos.Cohomology where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; not; true≢false; false≢true)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_; ΣPathP)
open import Cubical.Data.Empty using (rec)
open import Cubical.Relation.Nullary using (¬_)

open import Topos.Contextuality using (obsA; obsB; obsC; GlobalSection)

-- Z₂ as Bool under exclusive-or
_+₂_ : Bool → Bool → Bool
true  +₂ b = not b
false +₂ b = b
infixl 6 _+₂_

-- Triangle cochains.  A 0-cochain C⁰ labels each observable,
-- that is each vertex.  A 1-cochain C¹ gives a twist per
-- context, that is per edge.  Both are triples of Z₂ here.
Cochain : Type
Cochain = Bool × Bool × Bool

-- The coboundary δ : C⁰ → C¹ gives the pairwise correlations that
-- a labelling realises.
δ : Cochain → Cochain
δ (a , b , c) = (a +₂ b , b +₂ c , a +₂ c)

-- Holonomy hol : C¹ → Z₂ is the loop sum.  It generates H¹ ≅ Z₂.
hol : Cochain → Bool
hol (x , y , z) = x +₂ (y +₂ z)

-- im δ ⊆ ker hol.  Every coboundary has zero holonomy, so
-- hol ∘ δ = 0.
hol-δ : (g : Cochain) → hol (δ g) ≡ false
hol-δ (false , false , false) = refl
hol-δ (false , false , true ) = refl
hol-δ (false , true  , false) = refl
hol-δ (false , true  , true ) = refl
hol-δ (true  , false , false) = refl
hol-δ (true  , false , true ) = refl
hol-δ (true  , true  , false) = refl
hol-δ (true  , true  , true ) = refl

-- Specker's empirical 1-cocycle is anti-correlated on every edge.
specker-cocycle : Cochain
specker-cocycle = (true , true , true)

hol-specker : hol specker-cocycle ≡ true
hol-specker = refl

is-coboundary : Cochain → Type
is-coboundary z = Σ[ g ∈ Cochain ] (δ g ≡ z)

-- The cohomological obstruction.  Specker's cocycle is not a
-- coboundary, so its class in H¹ is non-zero.  Holonomy separates
-- the two cases: coboundaries have holonomy 0, Specker's cocycle
-- has holonomy 1.
obstruction : ¬ is-coboundary specker-cocycle
obstruction (g , p) =
  false≢true (sym (hol-δ g) ∙ cong hol p ∙ hol-specker)

-- ----------------------------------------------------------
-- Bridge to Topos.Contextuality.  A global model is a coboundary
-- witness, so the H¹ class recovers the possibilistic no-global.
-- ----------------------------------------------------------
≢→+₂ : (a b : Bool) → ¬ (a ≡ b) → (a +₂ b ≡ true)
≢→+₂ true  true  ne = rec (ne refl)
≢→+₂ true  false ne = refl
≢→+₂ false true  ne = refl
≢→+₂ false false ne = rec (ne refl)

global→coboundary : GlobalSection → is-coboundary specker-cocycle
global→coboundary (v , pAB , pBC , pAC) =
  (obsA v , obsB v , obsC v) ,
  ΣPathP ( ≢→+₂ (obsA v) (obsB v) pAB
         , ΣPathP ( ≢→+₂ (obsB v) (obsC v) pBC
                  , ≢→+₂ (obsA v) (obsC v) pAC ) )

-- the contextuality obstruction, derived again cohomologically
no-global-cohomological : ¬ GlobalSection
no-global-cohomological gs = obstruction (global→coboundary gs)

-- ----------------------------------------------------------
-- ker hol ⊆ im δ.  Every 1-cochain of holonomy 0 is a coboundary.
-- Together with hol-δ, which gives im δ ⊆ ker hol, this yields
-- im δ = ker hol.  So holonomy descends to an isomorphism
-- H¹ = C¹ / im δ ≅ Z₂, and Specker's class is its non-zero
-- generator.  The cases of holonomy 1 are vacuous, because the
-- hypothesis reads true ≡ false there.
-- ----------------------------------------------------------
ker-hol→coboundary : (z : Cochain) → hol z ≡ false → is-coboundary z
ker-hol→coboundary (false , false , false) h = (false , false , false) , refl
ker-hol→coboundary (false , false , true ) h = rec (true≢false h)
ker-hol→coboundary (false , true  , false) h = rec (true≢false h)
ker-hol→coboundary (false , true  , true ) h = (false , false , true ) , refl
ker-hol→coboundary (true  , false , false) h = rec (true≢false h)
ker-hol→coboundary (true  , false , true ) h = (false , true  , true ) , refl
ker-hol→coboundary (true  , true  , false) h = (false , true  , false) , refl
ker-hol→coboundary (true  , true  , true ) h = rec (true≢false h)

-- Holonomy is onto Z₂, so H¹ has both classes and is not
-- collapsed.
hol-onto : (b : Bool) → Σ[ z ∈ Cochain ] (hol z ≡ b)
hol-onto b = (false , false , b) , refl
