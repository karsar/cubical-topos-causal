{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.CechCohomology — the general degree-1 Čech apparatus.
--
-- Topos.Cohomology computed H¹ for the fixed triangle.  Here the
-- same obstruction is a theorem for an ARBITRARY cover at the
-- pairwise level and ARBITRARY abelian coefficients: over any set of
-- observables and any abelian group, a 1-cochain with non-trivial
-- holonomy around a closed walk is not a coboundary, hence a
-- non-zero class in H¹.
--
-- This is the degree-1 (contextuality) fragment of Čech cohomology,
-- for covers whose contexts are pairs.  The full nerve of an
-- arbitrary cover and the higher cochain complex are left to future
-- work.  We recover the triangle as an instance and contrast it with
-- a square, which is NOT contextual --- its holonomy is trivial,
-- exactly because an even cycle of anti-correlations is satisfiable.
-- ============================================================

module Topos.CechCohomology where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_)
open import Cubical.Data.Unit using (Unit*; tt*)
open import Cubical.Data.Bool using (Bool; true; false; not; true≢false)
open import Cubical.Relation.Nullary using (¬_)
import Cubical.Data.Empty as ⊥

-- a lightweight abelian group (coefficients for the cochains)
record AbGrp (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    G     : Type ℓ
    _·_   : G → G → G
    ε     : G
    inv   : G → G
    assoc : (a b c : G) → ((a · b) · c) ≡ (a · (b · c))
    idl   : (a : G) → (ε · a) ≡ a
    idr   : (a : G) → (a · ε) ≡ a
    invl  : (a : G) → (inv a · a) ≡ ε
    invr  : (a : G) → (a · inv a) ≡ ε
    comm  : (a b : G) → (a · b) ≡ (b · a)

module _ {ℓv ℓ} {V : Type ℓv} (Grp : AbGrp ℓ) where
  open AbGrp Grp

  -- 0-cochains label observables; 1-cochains label ordered pairs
  -- (the contexts).  δ⁰ is the coboundary: the realised correlation.
  Cochain0 : Type (ℓ-max ℓv ℓ)
  Cochain0 = V → G
  Cochain1 : Type (ℓ-max ℓv ℓ)
  Cochain1 = V → V → G

  δ⁰ : Cochain0 → Cochain1
  δ⁰ f i j = f j · inv (f i)

  -- holonomy of the closed walk v₀ ∷ vs: the sum of the cochain over
  -- its consecutive edges.
  hol : Cochain1 → V → List V → G
  hol g v₀ []        = ε
  hol g v₀ (v₁ ∷ vs) = g v₀ v₁ · hol g v₁ vs

  lastV : V → List V → V
  lastV v₀ []        = v₀
  lastV v₀ (v₁ ∷ vs) = lastV v₁ vs

  -- group algebra:  (a · x) · (inv a · b) ≡ x · b
  cancel : (a x b : G) → ((a · x) · (inv a · b)) ≡ (x · b)
  cancel a x b =
      assoc a x (inv a · b)
    ∙ cong (a ·_) (sym (assoc x (inv a) b))
    ∙ cong (λ z → a · (z · b)) (comm x (inv a))
    ∙ cong (a ·_) (assoc (inv a) x b)
    ∙ sym (assoc a (inv a) (x · b))
    ∙ cong (_· (x · b)) (invr a)
    ∙ idl (x · b)

  -- holonomy respects pointwise equality of cochains
  hol-resp : (g h : Cochain1) → ((i j : V) → g i j ≡ h i j)
           → (v₀ : V) (vs : List V) → hol g v₀ vs ≡ hol h v₀ vs
  hol-resp g h e v₀ []        = refl
  hol-resp g h e v₀ (v₁ ∷ vs) = cong₂ _·_ (e v₀ v₁) (hol-resp g h e v₁ vs)

  -- THE TELESCOPE: a coboundary's holonomy along a walk is the
  -- difference of its endpoints.
  hol-δ⁰ : (f : Cochain0) (v₀ : V) (vs : List V)
         → hol (δ⁰ f) v₀ vs ≡ (inv (f v₀) · f (lastV v₀ vs))
  hol-δ⁰ f v₀ []        = sym (invl (f v₀))
  hol-δ⁰ f v₀ (v₁ ∷ vs) =
      cong ((δ⁰ f v₀ v₁) ·_) (hol-δ⁰ f v₁ vs)
    ∙ cancel (f v₁) (inv (f v₀)) (f (lastV v₁ vs))

  -- Directed edges of a cover: the ordered pairs actually measured
  -- (the 1-cells of the nerve).  A coboundary realises g on these
  -- edges only, as in the Abramsky-style Čech reading.
  Edge : Type ℓv
  Edge = V × V

  -- the consecutive directed edges of the walk v₀ ∷ vs
  edges-of : V → List V → List Edge
  edges-of v₀ []        = []
  edges-of v₀ (v₁ ∷ vs) = (v₀ , v₁) ∷ edges-of v₁ vs

  -- f realises g as a coboundary on each edge of the given list
  realises-on : List Edge → Cochain0 → Cochain1 → Type (ℓ-max ℓv ℓ)
  realises-on []             f g = Unit*
  realises-on ((i , j) ∷ es) f g = (δ⁰ f i j ≡ g i j) × realises-on es f g

  -- g is a coboundary ON A GIVEN SET OF EDGES: some 0-cochain f has
  -- δ⁰ f ≡ g on exactly those measured contexts.
  is-coboundary : List Edge → Cochain1 → Type (ℓ-max ℓv ℓ)
  is-coboundary es g = Σ[ f ∈ Cochain0 ] realises-on es f g

  -- restricted hol-resp: holonomy respects a coboundary equation
  -- supplied only on the walk's own consecutive edges.
  hol-resp-walk : (g : Cochain1) (f : Cochain0) (v₀ : V) (vs : List V)
                → realises-on (edges-of v₀ vs) f g
                → hol g v₀ vs ≡ hol (δ⁰ f) v₀ vs
  hol-resp-walk g f v₀ []        _        = refl
  hol-resp-walk g f v₀ (v₁ ∷ vs) (p , ps) =
    cong₂ _·_ (sym p) (hol-resp-walk g f v₁ vs ps)

  -- A 1-cochain with non-trivial holonomy around a closed walk is not
  -- a coboundary on that walk's edges --- a non-zero class in H¹.
  -- (Any edge-realiser would give the walk holonomy ε, by the telescope.)
  holonomy-obstruction :
      (g : Cochain1) (v₀ : V) (vs : List V)
    → lastV v₀ vs ≡ v₀
    → ¬ (hol g v₀ vs ≡ ε)
    → ¬ is-coboundary (edges-of v₀ vs) g
  holonomy-obstruction g v₀ vs closed nontriv (f , allEq) =
    nontriv ( hol-resp-walk g f v₀ vs allEq
            ∙ hol-δ⁰ f v₀ vs
            ∙ cong (λ w → inv (f v₀) · f w) closed
            ∙ invl (f v₀) )

-- ============================================================
-- Coefficients Z₂ and two instances.
-- ============================================================

xr : Bool → Bool → Bool
xr true  b = not b
xr false b = b

xr-idr : (b : Bool) → xr b false ≡ b
xr-idr true  = refl
xr-idr false = refl
xr-self : (b : Bool) → xr b b ≡ false
xr-self true  = refl
xr-self false = refl
xr-comm : (a b : Bool) → xr a b ≡ xr b a
xr-comm true  true  = refl
xr-comm true  false = refl
xr-comm false true  = refl
xr-comm false false = refl
xr-assoc : (a b c : Bool) → xr (xr a b) c ≡ xr a (xr b c)
xr-assoc true  true  true  = refl
xr-assoc true  true  false = refl
xr-assoc true  false true  = refl
xr-assoc true  false false = refl
xr-assoc false true  true  = refl
xr-assoc false true  false = refl
xr-assoc false false true  = refl
xr-assoc false false false = refl

Z₂ : AbGrp ℓ-zero
Z₂ = record
  { G = Bool ; _·_ = xr ; ε = false ; inv = λ b → b
  ; assoc = xr-assoc ; idl = λ _ → refl ; idr = xr-idr
  ; invl = xr-self ; invr = xr-self ; comm = xr-comm }

-- The triangle (Specker): three observables, every pair anti-
-- correlated.  Holonomy around A→B→C→A is 1 — it IS contextual.
data Tri : Type where tA tB tC : Tri

gTri : Tri → Tri → Bool
gTri tA tB = true
gTri tB tC = true
gTri tC tA = true
gTri _  _  = false

-- No 0-cochain realises gTri on the triangle's three measured edges
-- tA→tB→tC→tA: such a realiser would give the closed walk holonomy ε,
-- but gTri's holonomy is 1.
triangle-contextual :
  ¬ is-coboundary Z₂ (edges-of Z₂ tA (tB ∷ tC ∷ tA ∷ [])) gTri
triangle-contextual =
  holonomy-obstruction Z₂ gTri tA (tB ∷ tC ∷ tA ∷ []) refl true≢false

-- The square: four observables in a 4-cycle, every edge anti-
-- correlated.  Holonomy is 0 (an even cycle), so the obstruction
-- does NOT fire --- and indeed the square is satisfiable.
data Quad : Type where q0 q1 q2 q3 : Quad

gQuad : Quad → Quad → Bool
gQuad q0 q1 = true
gQuad q1 q2 = true
gQuad q2 q3 = true
gQuad q3 q0 = true
gQuad _  _  = false

square-holonomy-trivial : hol Z₂ gQuad q0 (q1 ∷ q2 ∷ q3 ∷ q0 ∷ []) ≡ false
square-holonomy-trivial = refl

-- The square is satisfiable: a global 2-colouring realises every edge
-- anti-correlation (endpoints differ), the global section the triangle
-- lacks (Topos.Contextuality.no-global).  So the holonomy invariant
-- separates the contextual triangle from the satisfiable square.
colour : Quad → Bool
colour q0 = false
colour q1 = true
colour q2 = false
colour q3 = true

-- The square's cochain is a coboundary on its 4-cycle: δ⁰ colour ≡
-- gQuad on every edge.  So is-coboundary is inhabited, and
-- triangle-contextual is a negation of an attainable predicate.
square-coboundary :
  is-coboundary Z₂ (edges-of Z₂ q0 (q1 ∷ q2 ∷ q3 ∷ q0 ∷ [])) gQuad
square-coboundary = colour , (refl , refl , refl , refl , tt*)

square-satisfiable : (i j : Quad) → gQuad i j ≡ true → colour i ≡ not (colour j)
square-satisfiable q0 q1 _ = refl
square-satisfiable q1 q2 _ = refl
square-satisfiable q2 q3 _ = refl
square-satisfiable q3 q0 _ = refl
square-satisfiable q0 q0 h = ⊥.rec (true≢false (sym h))
square-satisfiable q0 q2 h = ⊥.rec (true≢false (sym h))
square-satisfiable q0 q3 h = ⊥.rec (true≢false (sym h))
square-satisfiable q1 q0 h = ⊥.rec (true≢false (sym h))
square-satisfiable q1 q1 h = ⊥.rec (true≢false (sym h))
square-satisfiable q1 q3 h = ⊥.rec (true≢false (sym h))
square-satisfiable q2 q0 h = ⊥.rec (true≢false (sym h))
square-satisfiable q2 q1 h = ⊥.rec (true≢false (sym h))
square-satisfiable q2 q2 h = ⊥.rec (true≢false (sym h))
square-satisfiable q3 q1 h = ⊥.rec (true≢false (sym h))
square-satisfiable q3 q2 h = ⊥.rec (true≢false (sym h))
square-satisfiable q3 q3 h = ⊥.rec (true≢false (sym h))
