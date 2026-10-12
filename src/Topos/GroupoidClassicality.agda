{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.GroupoidClassicality: when the forcing logic of the
-- regime site is classical, on an arbitrary base.
--
-- Topos.Classicality and Topos.CoarseClassicality show, each on
-- one small site, that a Boolean tautology (excluded middle) can
-- fail to be forced.  This module proves the general statement.
-- The base category C is arbitrary.  A stage c forces a sieve
-- on c when the sieve contains the identity of c.
--
--  (a) For an arrow f : d → c, the stage c forces excluded middle
--      for the sieve that f generates exactly when f has a
--      section.  No stage forces the negation of that sieve.
--
--  (b) Excluded middle is forced for every principal sieve at
--      every stage exactly when C is a groupoid, that is, when
--      every arrow is invertible.
--
--  (c) Over a groupoid, forcing commutes with the connectives.
--      For a propositional formula, c ⊩ φ is the truth of φ at c
--      read with the connectives of the metatheory.  If the atoms
--      are decidable at c, every Boolean tautology is forced at c.
--      Modus ponens is sound for forcing on every base.
--
--  (d) Assume that "f has a section" is decidable for each arrow
--      f.  This holds on every finite site with decidable hom
--      sets.  Then the Boolean axiom (all tautologies, decidable
--      atoms) is sound for forcing exactly when C is a groupoid.
--      The intervention site Iv is not a groupoid, so the axiom
--      fails there.  Topos.Classicality gives one witness.
--
-- Causal reading.  Ibeling and Icard (AAAI 2020) give each level
-- of Pearl's hierarchy a language with a two-valued semantics.
-- Their axiom systems contain all Boolean tautologies and modus
-- ponens.  By (c) and (d), that propositional layer is sound
-- for the topos reading exactly when every arrow between regimes
-- is invertible.  A discrete site, with only identities, is a
-- special case.  Invertible arrows, such as a relabelling of
-- values, keep the logic classical.  A non-invertible arrow,
-- such as the restriction from observation to an intervention,
-- makes it intuitionistic.
--
-- Scope.  The module treats the propositional connectives only.
-- It says nothing about the probability terms or the arithmetic
-- of the Ibeling-Icard languages.  The decidability hypothesis in
-- (c) is the "atom source" of non-classicality.  The groupoid
-- hypothesis is the "stage source".  The two are independent.
--
-- The mathematics is standard: a presheaf topos is Boolean
-- exactly when its base is a groupoid.  The module gives the
-- statement for the forcing relation of Topos.Forcing, with the
-- finite-site hypothesis made explicit.
-- ============================================================

module Topos.GroupoidClassicality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isProp×)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd; ΣPathP)
open import Cubical.Data.Sum as ⊎ using (_⊎_)
open import Cubical.Data.Unit using (Unit*; tt*)
open import Cubical.Data.Empty as E using (⊥; ⊥*; isProp⊥)
open import Cubical.Data.Bool using (Bool; true; false; _and_; _or_; not; Dec→Bool; false≢true; isSetBool)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)

open import Topos.Cat
open import Topos.Omega
open import Topos.DoubleNegation using (¬S; ⊥S; _⇒S_)
open import Topos.Forcing using (_∨S_; _⊩_; _∩_)
open import Topos.InterventionSite

-- ------------------------------------------------------------
-- Logical equivalence, and Boolean truth as a type.
-- ------------------------------------------------------------
_↔_ : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
P ↔ Q = (P → Q) × (Q → P)

T : Bool → Type
T b = b ≡ true

-- ------------------------------------------------------------
-- Propositional formulas over a type A of atoms, and their
-- classical (Boolean) evaluation.
-- ------------------------------------------------------------
infixr 6 _∧f_
infixr 5 _∨f_
infixr 4 _⇒f_

data Form {ℓa} (A : Type ℓa) : Type ℓa where
  atom           : A → Form A
  ⊤f ⊥f          : Form A
  _∧f_ _∨f_ _⇒f_ : Form A → Form A → Form A

module _ {ℓa} {A : Type ℓa} where

  evalB : (A → Bool) → Form A → Bool
  evalB v (atom a) = v a
  evalB v ⊤f       = true
  evalB v ⊥f       = false
  evalB v (φ ∧f ψ) = evalB v φ and evalB v ψ
  evalB v (φ ∨f ψ) = evalB v φ or evalB v ψ
  evalB v (φ ⇒f ψ) = not (evalB v φ) or evalB v ψ

  -- A tautology is true under every Boolean valuation.
  Tautology : Form A → Type ℓa
  Tautology φ = (v : A → Bool) → T (evalB v φ)

-- ------------------------------------------------------------
-- Each Boolean connective agrees with the connective of the
-- metatheory, on types that are equivalent to Boolean truth.
-- ------------------------------------------------------------
private
  absurd : ∀ {ℓ} {X : Type ℓ} → T false → X
  absurd e = E.rec (false≢true e)

module _ {ℓ} {P Q : Type ℓ} where

  and↔ : (x y : Bool) → P ↔ T x → Q ↔ T y → (P × Q) ↔ T (x and y)
  and↔ true  true  hp hq = (λ _ → refl) , (λ _ → snd hp refl , snd hq refl)
  and↔ true  false hp hq = (λ pq → fst hq (snd pq)) , absurd
  and↔ false true  hp hq = (λ pq → fst hp (fst pq)) , absurd
  and↔ false false hp hq = (λ pq → fst hp (fst pq)) , absurd

  or↔ : (x y : Bool) → P ↔ T x → Q ↔ T y → ∥ P ⊎ Q ∥₁ ↔ T (x or y)
  or↔ true  true  hp hq = (λ _ → refl) , (λ _ → ∣ ⊎.inl (snd hp refl) ∣₁)
  or↔ true  false hp hq = (λ _ → refl) , (λ _ → ∣ ⊎.inl (snd hp refl) ∣₁)
  or↔ false true  hp hq = (λ _ → refl) , (λ _ → ∣ ⊎.inr (snd hq refl) ∣₁)
  or↔ false false hp hq =
    PT.rec (isSetBool _ _) (⊎.rec (fst hp) (fst hq)) , absurd

  imp↔ : (x y : Bool) → P ↔ T x → Q ↔ T y → (P → Q) ↔ T (not x or y)
  imp↔ true  true  hp hq = (λ _ → refl) , (λ _ _ → snd hq refl)
  imp↔ true  false hp hq = (λ h → fst hq (h (snd hp refl))) , absurd
  imp↔ false true  hp hq = (λ _ → refl) , (λ _ p → absurd (fst hp p))
  imp↔ false false hp hq = (λ _ → refl) , (λ _ p → absurd (fst hp p))


dec↔ : ∀ {ℓ} {P : Type ℓ} (d : Dec P) → P ↔ T (Dec→Bool d)
dec↔ (yes p) = (λ _ → refl) , (λ _ → p)
dec↔ (no ¬p) = (λ p → E.rec (¬p p)) , absurd

-- ============================================================
-- The base category is arbitrary from here on.
-- ============================================================
module _ {ℓ} {C : Precategory ℓ ℓ} where
  open Precategory C

  private
    _⊩C_ : (c : Ob) → Sieve {C = C} c → Type ℓ
    c ⊩C S = _⊩_ {C = C} c S

  -- ----------------------------------------------------------
  -- Invertible arrows, groupoids, and sections.
  -- ----------------------------------------------------------
  isIso : {d c : Ob} → Hom d c → Type ℓ
  isIso {d} {c} f = Σ[ g ∈ Hom c d ] ((f ⋆ g ≡ idn) × (g ⋆ f ≡ idn))

  -- An inverse is unique, so being invertible is a proposition.
  isPropIsIso : {d c : Ob} (f : Hom d c) → isProp (isIso f)
  isPropIsIso f (g , fg , gf) (g' , fg' , gf') =
    ΣPathP (g≡g' , isProp→PathP (λ i → isProp× (isSetHom _ _) (isSetHom _ _))
                                (fg , gf) (fg' , gf'))
    where
      g≡g' : g ≡ g'
      g≡g' = sym (⋆-idR g) ∙ cong (g ⋆_) (sym fg') ∙ sym (⋆-assoc g f g')
           ∙ cong (_⋆ g') gf ∙ ⋆-idL g'

  IsGroupoid : Type ℓ
  IsGroupoid = {d c : Ob} (f : Hom d c) → isIso f

  -- A section of f : d → c is an h : c → d with "h then f" = id.
  HasSection : {d c : Ob} → Hom d c → Type ℓ
  HasSection {d} {c} f = Σ[ h ∈ Hom c d ] (h ⋆ f ≡ idn)

  -- ----------------------------------------------------------
  -- The sieve generated by an arrow f : d → c.  An arrow g into
  -- c is in it when g factors through f.
  -- ----------------------------------------------------------
  ⟨_⟩ : {d c : Ob} → Hom d c → Sieve {C = C} c
  ⟨_⟩ {d} {c} f =
    (λ e g → ∥ Σ[ h ∈ Hom e d ] (h ⋆ f ≡ g) ∥₁ , squash₁) ,
    (λ e e' k g → PT.map λ hp →
       (k ⋆ fst hp) , ⋆-assoc k (fst hp) f ∙ cong (k ⋆_) (snd hp))

  -- Excluded middle for a sieve S on c.
  EM : (c : Ob) → Sieve {C = C} c → Sieve {C = C} c
  EM c S = _∨S_ {C = C} {c = c} S (¬S {C = C} {c = c} S)

  -- c forces ⟨ f ⟩ exactly when f has a section.  Both sides are
  -- the same type.
  ⊩⟨⟩→section : {d c : Ob} (f : Hom d c) → c ⊩C ⟨ f ⟩ → ∥ HasSection f ∥₁
  ⊩⟨⟩→section f x = x

  section→⊩⟨⟩ : {d c : Ob} (f : Hom d c) → ∥ HasSection f ∥₁ → c ⊩C ⟨ f ⟩
  section→⊩⟨⟩ f x = x

  -- No stage forces the negation of a principal sieve.  The
  -- restriction along f itself is in ⟨ f ⟩.
  ⊮¬⟨⟩ : {d c : Ob} (f : Hom d c) → ¬ (c ⊩C ¬S {C = C} {c = c} ⟨ f ⟩)
  ⊮¬⟨⟩ {d} f n = E.rec* (n d f ∣ idn , ⋆-idL f ∙ sym (⋆-idR f) ∣₁)

  -- ----------------------------------------------------------
  -- (a) Excluded middle for ⟨ f ⟩ is forced exactly when f has a
  -- section.
  -- ----------------------------------------------------------
  em⟨⟩→section : {d c : Ob} (f : Hom d c) → c ⊩C EM c ⟨ f ⟩ → ∥ HasSection f ∥₁
  em⟨⟩→section f = PT.rec squash₁ (⊎.rec (λ s → s) (λ n → E.rec (⊮¬⟨⟩ f n)))

  section→em⟨⟩ : {d c : Ob} (f : Hom d c) → ∥ HasSection f ∥₁ → c ⊩C EM c ⟨ f ⟩
  section→em⟨⟩ f s = ∣ ⊎.inl s ∣₁

  -- If an arrow has no section, excluded middle fails at its
  -- codomain.
  no-section→em-fails : {d c : Ob} (f : Hom d c)
                      → ¬ ∥ HasSection f ∥₁ → ¬ (c ⊩C EM c ⟨ f ⟩)
  no-section→em-fails f ns x = ns (em⟨⟩→section f x)

  -- ----------------------------------------------------------
  -- (b) Excluded middle for every principal sieve, at every stage,
  -- holds exactly when C is a groupoid.
  --
  -- If every arrow has a section, every arrow is invertible.  Let
  -- h be a section of f, and k a section of h.  Then
  -- f = (k ⋆ h) ⋆ f = k ⋆ (h ⋆ f) = k, so f ⋆ h = k ⋆ h = id.
  -- ----------------------------------------------------------
  em⟨⟩→groupoid : ({d c : Ob} (f : Hom d c) → c ⊩C EM c ⟨ f ⟩) → IsGroupoid
  em⟨⟩→groupoid em {d} {c} f =
    PT.rec (isPropIsIso f)
      (λ { (h , hf) →
        PT.rec (isPropIsIso f)
          (λ { (k , kh) → h , fh h hf k kh , hf })
          (em⟨⟩→section h (em h)) })
      (em⟨⟩→section f (em f))
    where
      fh : (h : Hom c d) → h ⋆ f ≡ idn → (k : Hom d c) → k ⋆ h ≡ idn
         → f ⋆ h ≡ idn
      fh h hf k kh = cong (_⋆ h) f≡k ∙ kh
        where
          f≡k : f ≡ k
          f≡k = sym (⋆-idL f) ∙ cong (_⋆ f) (sym kh) ∙ ⋆-assoc k h f
              ∙ cong (k ⋆_) hf ∙ ⋆-idR k

  groupoid→em⟨⟩ : IsGroupoid → {d c : Ob} (f : Hom d c) → c ⊩C EM c ⟨ f ⟩
  groupoid→em⟨⟩ gpd f = section→em⟨⟩ f ∣ fst (gpd f) , snd (snd (gpd f)) ∣₁

  em⟨⟩↔groupoid : ({d c : Ob} (f : Hom d c) → c ⊩C EM c ⟨ f ⟩) ↔ IsGroupoid
  em⟨⟩↔groupoid = em⟨⟩→groupoid , groupoid→em⟨⟩

  -- ----------------------------------------------------------
  -- (c) Over a groupoid, forcing of an implication is the
  -- implication of forcings.
  -- ----------------------------------------------------------

  -- Membership along an invertible arrow gives forcing.
  iso-reflects : {c e : Ob} (S : Sieve {C = C} c) (g : Hom e c)
               → isIso g → fst (fst S e g) → c ⊩C S
  iso-reflects S g (g⁻ , _ , g⁻g) s =
    subst (λ h → fst (fst S _ h)) g⁻g (snd S _ _ g⁻ g s)

  -- Modus ponens.  This direction holds on every base.
  ⊩-mp : (c : Ob) (S T : Sieve {C = C} c)
       → c ⊩C (_⇒S_ {C = C} {c = c} S T) → c ⊩C S → c ⊩C T
  ⊩-mp c S T H s =
    subst (λ h → fst (fst T c h)) (⋆-idL idn)
      (H c idn (subst (λ h → fst (fst S c h)) (sym (⋆-idL idn)) s))

  -- The converse needs every arrow into c to be invertible.
  →⊩⇒ : IsGroupoid → (c : Ob) (S T : Sieve {C = C} c)
      → (c ⊩C S → c ⊩C T) → c ⊩C (_⇒S_ {C = C} {c = c} S T)
  →⊩⇒ gpd c S T R e g s =
    snd T c e g idn (R (iso-reflects S (g ⋆ idn) (gpd (g ⋆ idn)) s))

  -- The interpretation of a formula as a sieve on c, from an
  -- assignment of sieves to atoms.
  module _ {A : Type ℓ} where

    ⟦_⟧ : {c : Ob} → Form A → (A → Sieve {C = C} c) → Sieve {C = C} c
    ⟦_⟧ {c} (atom a) ρ = ρ a
    ⟦_⟧ {c} ⊤f       ρ = maximal {C = C} c
    ⟦_⟧ {c} ⊥f       ρ = ⊥S {C = C} c
    ⟦_⟧ {c} (φ ∧f ψ) ρ = _∩_ {C = C} {c = c} (⟦ φ ⟧ ρ) (⟦ ψ ⟧ ρ)
    ⟦_⟧ {c} (φ ∨f ψ) ρ = _∨S_ {C = C} {c = c} (⟦ φ ⟧ ρ) (⟦ ψ ⟧ ρ)
    ⟦_⟧ {c} (φ ⇒f ψ) ρ = _⇒S_ {C = C} {c = c} (⟦ φ ⟧ ρ) (⟦ ψ ⟧ ρ)

    -- The truth of a formula at the single stage c, read with the
    -- connectives of the metatheory.  This is the stagewise,
    -- two-valued reading when the atoms are decidable.
    atStage : (c : Ob) → (A → Sieve {C = C} c) → Form A → Type ℓ
    atStage c ρ (atom a) = c ⊩C ρ a
    atStage c ρ ⊤f       = Unit*
    atStage c ρ ⊥f       = ⊥*
    atStage c ρ (φ ∧f ψ) = atStage c ρ φ × atStage c ρ ψ
    atStage c ρ (φ ∨f ψ) = ∥ atStage c ρ φ ⊎ atStage c ρ ψ ∥₁
    atStage c ρ (φ ⇒f ψ) = atStage c ρ φ → atStage c ρ ψ

    -- Over a groupoid, forcing IS truth at the stage.
    forced↔atStage : IsGroupoid → (c : Ob) (ρ : A → Sieve {C = C} c)
                   (φ : Form A) → (c ⊩C ⟦ φ ⟧ ρ) ↔ atStage c ρ φ
    forced↔atStage gpd c ρ (atom a) = (λ x → x) , (λ x → x)
    forced↔atStage gpd c ρ ⊤f       = (λ x → x) , (λ x → x)
    forced↔atStage gpd c ρ ⊥f       = (λ x → x) , (λ x → x)
    forced↔atStage gpd c ρ (φ ∧f ψ) =
      let hφ = forced↔atStage gpd c ρ φ ; hψ = forced↔atStage gpd c ρ ψ in
        (λ p → fst hφ (fst p) , fst hψ (snd p))
      , (λ p → snd hφ (fst p) , snd hψ (snd p))
    forced↔atStage gpd c ρ (φ ∨f ψ) =
      let hφ = forced↔atStage gpd c ρ φ ; hψ = forced↔atStage gpd c ρ ψ in
        PT.map (⊎.map (fst hφ) (fst hψ))
      , PT.map (⊎.map (snd hφ) (snd hψ))
    forced↔atStage gpd c ρ (φ ⇒f ψ) =
      let hφ = forced↔atStage gpd c ρ φ ; hψ = forced↔atStage gpd c ρ ψ in
        (λ H x → fst hψ (⊩-mp c (⟦ φ ⟧ ρ) (⟦ ψ ⟧ ρ) H (snd hφ x)))
      , (λ R → →⊩⇒ gpd c (⟦ φ ⟧ ρ) (⟦ ψ ⟧ ρ) (λ s → snd hψ (R (fst hφ s))))

    -- With decidable atoms, truth at the stage is the Boolean
    -- evaluation.  No hypothesis on C is needed here.
    atStage↔evalB : (c : Ob) (ρ : A → Sieve {C = C} c)
                    (dec : (a : A) → Dec (c ⊩C ρ a)) (φ : Form A)
                  → atStage c ρ φ ↔ T (evalB (λ a → Dec→Bool (dec a)) φ)
    atStage↔evalB c ρ dec (atom a) = dec↔ (dec a)
    atStage↔evalB c ρ dec ⊤f       = (λ _ → refl) , (λ _ → tt*)
    atStage↔evalB c ρ dec ⊥f       = E.rec* , absurd
    atStage↔evalB c ρ dec (φ ∧f ψ) =
      and↔ (evalB _ φ) (evalB _ ψ) (atStage↔evalB c ρ dec φ) (atStage↔evalB c ρ dec ψ)
    atStage↔evalB c ρ dec (φ ∨f ψ) =
      or↔ (evalB _ φ) (evalB _ ψ) (atStage↔evalB c ρ dec φ) (atStage↔evalB c ρ dec ψ)
    atStage↔evalB c ρ dec (φ ⇒f ψ) =
      imp↔ (evalB _ φ) (evalB _ ψ) (atStage↔evalB c ρ dec φ) (atStage↔evalB c ρ dec ψ)

    -- (c) Over a groupoid, every Boolean tautology is forced at
    -- every stage, for every assignment of decidable atoms.
    groupoid→tautology-forced
      : IsGroupoid → (c : Ob) (ρ : A → Sieve {C = C} c)
      → ((a : A) → Dec (c ⊩C ρ a))
      → (φ : Form A) → Tautology φ → c ⊩C ⟦ φ ⟧ ρ
    groupoid→tautology-forced gpd c ρ dec φ taut =
      snd (forced↔atStage gpd c ρ φ)
          (snd (atStage↔evalB c ρ dec φ) (taut (λ a → Dec→Bool (dec a))))

  -- ----------------------------------------------------------
  -- (d) The Boolean axiom is sound exactly over groupoids, when
  -- "has a section" is decidable.
  -- ----------------------------------------------------------
  BooleanSound : Type (ℓ-suc ℓ)
  BooleanSound = {A : Type ℓ} (c : Ob) (ρ : A → Sieve {C = C} c)
               → ((a : A) → Dec (c ⊩C ρ a))
               → (φ : Form A) → Tautology φ → c ⊩C ⟦ φ ⟧ ρ

  -- Holds on every finite site with decidable hom sets.
  SectionDecidable : Type ℓ
  SectionDecidable = {d c : Ob} (f : Hom d c) → Dec ∥ HasSection f ∥₁

  private
    emForm : Form (Unit* {ℓ})
    emForm = atom tt* ∨f (atom tt* ⇒f ⊥f)

    em-taut-b : (b : Bool) → T (b or (not b or false))
    em-taut-b true  = refl
    em-taut-b false = refl

    emForm-taut : Tautology emForm
    emForm-taut v = em-taut-b (v tt*)

  booleanSound→groupoid : SectionDecidable → BooleanSound → IsGroupoid
  booleanSound→groupoid sd bs =
    em⟨⟩→groupoid λ {d} {c} f →
      bs {A = Unit*} c (λ _ → ⟨ f ⟩) (λ _ → sd f) emForm emForm-taut

  groupoid→booleanSound : IsGroupoid → BooleanSound
  groupoid→booleanSound gpd c ρ dec φ taut =
    groupoid→tautology-forced gpd c ρ dec φ taut

  booleanSound↔groupoid : SectionDecidable → BooleanSound ↔ IsGroupoid
  booleanSound↔groupoid sd = booleanSound→groupoid sd , groupoid→booleanSound

-- ============================================================
-- The intervention site Iv (do0 → obs ← do1).
-- ============================================================
private
  no-obs→do0 : IHom obs do0 → ⊥
  no-obs→do0 ()

  no-obs→do1 : IHom obs do1 → ⊥
  no-obs→do1 ()

-- Every arrow of Iv either has a section or has none, decidably.
iv-section-decidable : SectionDecidable {C = Iv}
iv-section-decidable idₒ = yes ∣ idₒ , refl ∣₁
iv-section-decidable id₀ = yes ∣ id₀ , refl ∣₁
iv-section-decidable id₁ = yes ∣ id₁ , refl ∣₁
iv-section-decidable e0  = no (PT.rec isProp⊥ λ hs → no-obs→do0 (fst hs))
iv-section-decidable e1  = no (PT.rec isProp⊥ λ hs → no-obs→do1 (fst hs))

-- The restriction e0 : do0 → obs is not invertible.
iv-not-groupoid : ¬ IsGroupoid {C = Iv}
iv-not-groupoid gpd = no-obs→do0 (fst (gpd e0))

-- So the Boolean axiom is not sound for forcing on Iv.
iv-not-booleanSound : ¬ BooleanSound {C = Iv}
iv-not-booleanSound bs =
  iv-not-groupoid (booleanSound→groupoid {C = Iv} iv-section-decidable bs)

-- The explicit failing instance: excluded middle for the sieve
-- generated by e0 is not forced at obs.
iv-em-fails : ¬ (_⊩_ {C = Iv} obs (EM {C = Iv} obs (⟨_⟩ {C = Iv} e0)))
iv-em-fails = no-section→em-fails {C = Iv} e0
  (PT.rec isProp⊥ λ hs → no-obs→do0 (fst hs))
