{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.Modularity: modularity as a property of the menu of
-- interventions in a world, and worlds without it.
--
-- Topos.MechanismObject classifies one mechanism.  It checks
-- that the constant at x₀ replaces the mechanism of X.  It does
-- not check that the other mechanisms stay the same.  That
-- second condition is modularity.  Pearl's surgery assumes it.
-- Cartwright argues that real systems often do not have it.
--
-- Modularity is not a property of one intervention.  Any pair
-- of mechanisms is a surgery on the variables that it changes.
-- A pair is a "fat hand" only if the act had a smaller target.
-- Thus modularity is a property of the MENU: the set of
-- interventions that a world allows.  The question is this:
-- can you change each mechanism alone?
--
-- This module uses two mechanism slots, X and Y.  Mechs is the
-- product of their mechanism objects:
--     Mechs = MX ×ᴾ MY,   MX = Exp ParX (Dist_E ValX), ...
--
--   Allowed      the menu of a world.  It is a predicate on
--                pairs of mechanisms.  The predicate is a
--                proposition, and restriction keeps it true.
--                χ-allowed is its characteristic map.  This
--                level does not assume modularity.
--   Splits       the menu is modular.  If the menu allows a
--                pair, it also allows the change to X alone and
--                the change to Y alone.  The slot that does not
--                change keeps its original mechanism.
--   product-splits
--                take one menu for each slot.  If each menu
--                contains the original mechanism, then their
--                product splits.
--
-- Hardness is a different property.  A hard intervention puts a
-- constant in place of a mechanism.  A soft intervention puts
-- another mechanism in its place.  HardSurg is the menu of all
-- combinations of hard surgeries at the values x₀ and y₀.
-- χ-hard is its characteristic map.  In Pearl's world the menu
-- is HardSurg (PearlWorld, pearl→χ≡).  Pearl's world splits
-- (pearl-splits).
--
-- Three worlds on the one-context base of
-- Topos.MechanismSeparation show that the properties differ:
--   soft      the menu splits, but it allows a soft
--             intervention.  Thus it is not a world of hard
--             surgeries (soft-splits, soft-not-hard).
--   fat       a fat hand.  The act that sets X also changes Y.
--             The menu does not split (fat-not-splits).
--   joint     you can only set X and Y together.  The menu
--             does not split (joint-not-splits).
-- ============================================================

module Topos.Modularity where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Bool using (Bool; true; false; not)
open import Cubical.Data.Empty as E using (⊥; isProp⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁; ∣_∣₁; squash₁)

open import FDist-Convex using (FDist; pure; trunc; 𝔼)
open import WeightQ using (Weight; w0; w1; w0≢w1)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.InternalDist
open import Topos.Exponential
open import Topos.Classifier
  using (Classifies; χ; χ-sieve; χ-classifies; unique; P-fix; P-fix-closed)
open import Topos.MechanismObject using (Adm; Adm-closed)
open import Topos.MechanismSeparation
  using (Pt; BoolP; x₀; const-mech; copy-mech; const-admissible;
         copy-not-admissible; indTrue)

-- ------------------------------------------------------------
-- One slot.
-- ------------------------------------------------------------
module _ {ℓ} {C : Precategory ℓ ℓ} where
  open Precategory C
  open PSh

  MechO : (Par Val : PSh C ℓ) → PSh C ℓ
  MechO Par Val = Exp {C = C} Par (Dist_E {C = C} Val)

  -- A slot passes the hard-surgery test if its mechanism is
  -- the original k or the constant at v₀.
  HardSlot : (Par Val : PSh C ℓ) (v₀ : Section {C = C} Val)
             (k : Section {C = C} (MechO Par Val))
           → (c : Ob) → F₀ (MechO Par Val) c → hProp ℓ
  HardSlot Par Val v₀ k c m =
    ∥ fst (P-fix (MechO Par Val) k c m) ⊎ fst (Adm Par Val v₀ c m) ∥₁
    , squash₁

  -- Closure under restriction.  Each disjunct stays true.
  -- "Equal to the original" stays true because k is natural.
  -- "Constant" stays true by Adm-closed.
  HardSlot-closed : (Par Val : PSh C ℓ) (v₀ : Section {C = C} Val)
                    (k : Section {C = C} (MechO Par Val))
                    (d e : Ob) (g : Hom e d) (m : F₀ (MechO Par Val) d)
                  → fst (HardSlot Par Val v₀ k d m)
                  → fst (HardSlot Par Val v₀ k e (F₁ (MechO Par Val) g m))
  HardSlot-closed Par Val v₀ k d e g m = PT.map step
    where
      step : _ ⊎ _ → _ ⊎ _
      step (inl p) = inl (P-fix-closed (MechO Par Val) k d e g m p)
      step (inr a) = inr (Adm-closed Par Val v₀ d e g m a)

-- ------------------------------------------------------------
-- Two slots.
-- ------------------------------------------------------------
module _ {ℓ} {C : Precategory ℓ ℓ}
         (ParX ValX ParY ValY : PSh C ℓ)
         (x₀' : Section {C = C} ValX) (y₀ : Section {C = C} ValY)
         (kX : Section {C = C} (MechO ParX ValX))
         (kY : Section {C = C} (MechO ParY ValY)) where
  open Precategory C
  open PSh

  MX MY Mechs : PSh C ℓ
  MX = MechO ParX ValX
  MY = MechO ParY ValY
  Mechs = MX ×ᴾ MY

  -- The original mechanisms, at each context.
  oX : (c : Ob) → F₀ MX c
  oX c = fst kX c tt

  oY : (c : Ob) → F₀ MY c
  oY c = fst kY c tt

  -- ----------------------------------------------------------
  -- The menu of interventions in a world.
  -- ----------------------------------------------------------
  record Allowed : Type (ℓ-suc ℓ) where
    field
      A        : (c : Ob) → F₀ Mechs c → hProp ℓ
      A-closed : (d e : Ob) (g : Hom e d) (m : F₀ Mechs d)
               → fst (A d m) → fst (A e (F₁ Mechs g m))

  open Allowed

  χ-allowed : Allowed → Nat Mechs (Ω {C = C})
  χ-allowed W = χ Mechs (A W) (A-closed W)

  -- ----------------------------------------------------------
  -- Modularity: the menu splits.  You can apply each allowed
  -- change to one slot alone.  The other slot keeps its
  -- original mechanism.
  -- ----------------------------------------------------------
  Splits : Allowed → Type ℓ
  Splits W =
    (c : Ob) (mX : F₀ MX c) (mY : F₀ MY c)
    → fst (A W c (mX , mY))
    → fst (A W c (mX , oY c)) × fst (A W c (oX c , mY))

  isPropSplits : (W : Allowed) → isProp (Splits W)
  isPropSplits W =
    isPropΠ λ c → isPropΠ λ mX → isPropΠ λ mY → isPropΠ λ _ →
    isProp× (snd (A W c (mX , oY c))) (snd (A W c (oX c , mY)))

  -- The product of one menu for each slot.
  product : (PX : (c : Ob) → F₀ MX c → hProp ℓ)
            (PY : (c : Ob) → F₀ MY c → hProp ℓ)
          → ((d e : Ob) (g : Hom e d) (m : F₀ MX d)
             → fst (PX d m) → fst (PX e (F₁ MX g m)))
          → ((d e : Ob) (g : Hom e d) (m : F₀ MY d)
             → fst (PY d m) → fst (PY e (F₁ MY g m)))
          → Allowed
  A (product PX PY _ _) c (mX , mY) =
    (fst (PX c mX) × fst (PY c mY)) , isProp× (snd (PX c mX)) (snd (PY c mY))
  A-closed (product PX PY cX cY) d e g (mX , mY) (px , py) =
    cX d e g mX px , cY d e g mY py

  -- If each slot menu contains the original mechanism, then
  -- the product menu splits.
  product-splits : (PX : (c : Ob) → F₀ MX c → hProp ℓ)
                   (PY : (c : Ob) → F₀ MY c → hProp ℓ)
                   (cX : (d e : Ob) (g : Hom e d) (m : F₀ MX d)
                       → fst (PX d m) → fst (PX e (F₁ MX g m)))
                   (cY : (d e : Ob) (g : Hom e d) (m : F₀ MY d)
                       → fst (PY d m) → fst (PY e (F₁ MY g m)))
                 → ((c : Ob) → fst (PX c (oX c)))
                 → ((c : Ob) → fst (PY c (oY c)))
                 → Splits (product PX PY cX cY)
  product-splits PX PY cX cY ox oy c mX mY (px , py) =
    (px , oy c) , (ox c , py)

  -- ----------------------------------------------------------
  -- Hard surgeries at the fixed values.  Each slot keeps its
  -- original mechanism, or it becomes the constant at its value.
  -- ----------------------------------------------------------
  HardSurg : (c : Ob) → F₀ Mechs c → hProp ℓ
  HardSurg c (mX , mY) =
    (fst (HardSlot ParX ValX x₀' kX c mX) × fst (HardSlot ParY ValY y₀ kY c mY))
    , isProp× squash₁ squash₁

  HardSurg-closed : (d e : Ob) (g : Hom e d) (m : F₀ Mechs d)
                  → fst (HardSurg d m) → fst (HardSurg e (F₁ Mechs g m))
  HardSurg-closed d e g (mX , mY) (sx , sy) =
    HardSlot-closed ParX ValX x₀' kX d e g mX sx ,
    HardSlot-closed ParY ValY y₀ kY d e g mY sy

  χ-hard : Nat Mechs (Ω {C = C})
  χ-hard = χ Mechs HardSurg HardSurg-closed

  χ-hard-classifies : Classifies Mechs HardSurg HardSurg-closed (fst χ-hard)
  χ-hard-classifies = χ-classifies Mechs HardSurg HardSurg-closed

  χ-hard-unique : (χ' : Nat Mechs (Ω {C = C}))
                → Classifies Mechs HardSurg HardSurg-closed (fst χ') → χ' ≡ χ-hard
  χ-hard-unique = unique Mechs HardSurg HardSurg-closed

  -- Every allowed intervention is a hard surgery.
  HardOnly : Allowed → Type ℓ
  HardOnly W = (c : Ob) (m : F₀ Mechs c) → fst (A W c m) → fst (HardSurg c m)

  -- Every hard surgery is allowed.
  AllHard : Allowed → Type ℓ
  AllHard W = (c : Ob) (m : F₀ Mechs c) → fst (HardSurg c m) → fst (A W c m)

  PearlWorld : Allowed → Type ℓ
  PearlWorld W = HardOnly W × AllHard W

  -- Pearl's world.  Its menu is exactly the hard surgeries.
  pearl : Allowed
  pearl = product (HardSlot ParX ValX x₀' kX) (HardSlot ParY ValY y₀ kY)
                  (HardSlot-closed ParX ValX x₀' kX)
                  (HardSlot-closed ParY ValY y₀ kY)

  pearl-is-pearl : PearlWorld pearl
  pearl-is-pearl = (λ _ _ h → h) , (λ _ _ h → h)

  -- Pearl's world is modular.
  pearl-splits : Splits pearl
  pearl-splits =
    product-splits (HardSlot ParX ValX x₀' kX) (HardSlot ParY ValY y₀ kY)
                   (HardSlot-closed ParX ValX x₀' kX)
                   (HardSlot-closed ParY ValY y₀ kY)
                   (λ c → ∣ inl refl ∣₁) (λ c → ∣ inl refl ∣₁)

  -- Take a world that allows only hard surgeries.  Each arrow
  -- in the sieve of "allowed" is also in the sieve of "hard
  -- surgery".
  hard→χ≤ : (W : Allowed) → HardOnly W
          → (c : Ob) (m : F₀ Mechs c) (d : Ob) (f : Hom d c)
          → fst (fst (χ-sieve Mechs (A W) (A-closed W) c m) d f)
          → fst (fst (χ-sieve Mechs HardSurg HardSurg-closed c m) d f)
  hard→χ≤ W h c m d f = h d (F₁ Mechs f m)

  -- In a Pearl world the two characteristic maps are equal.
  pearl→χ≡ : (W : Allowed) → PearlWorld W → χ-allowed W ≡ χ-hard
  pearl→χ≡ W (h , cpl) =
    χ-hard-unique (χ-allowed W) λ c m →
      (λ s → fst (χ-classifies Mechs (A W) (A-closed W) c m) (cpl c m s)) ,
      (λ eq → h c m (snd (χ-classifies Mechs (A W) (A-closed W) c m) eq))

-- ============================================================
-- Three worlds on the one-context base.
--
-- Both slots have Bool parents and Bool values.  Both fixed
-- values are true.  Both original mechanisms copy their parent.
-- ============================================================

MB : PSh Pt ℓ-zero
MB = MechO {C = Pt} BoolP BoolP

-- A mechanism of MB as a section.  There is only one context,
-- so naturality is only an equality of families.
asSection : PSh.F₀ MB tt → Section {C = Pt} MB
asSection m = (λ _ _ → m) ,
  (λ _ _ _ _ → ExpEl≡ {C = Pt} BoolP (Dist_E {C = Pt} BoolP) tt _ _ refl)

copyS : Section {C = Pt} MB
copyS = asSection copy-mech

-- A third mechanism.  It returns the opposite of the parent.
-- It is not the original (copy), and it is not the constant at
-- true.  An intervention that installs it is soft.
flip-mech : PSh.F₀ MB tt
flip-mech = (λ _ _ p → pure (not p)) , (λ _ _ _ _ _ → refl)

flipS : Section {C = Pt} MB
flipS = asSection flip-mech

-- At parent true, flip returns the point mass at false.  The
-- expectation of the indicator of true tells the two point
-- masses apart.
flip≢copy : ¬ (flip-mech ≡ copy-mech)
flip≢copy p = w0≢w1 (cong (λ m → 𝔼 (fst m tt tt true) indTrue) p)

flip-not-admissible : ¬ (fst (Adm BoolP BoolP x₀ tt flip-mech))
flip-not-admissible adm = w0≢w1 (cong (λ d → 𝔼 d indTrue) (adm tt tt true))

flip-not-hard : ¬ (fst (HardSlot BoolP BoolP x₀ copyS tt flip-mech))
flip-not-hard = PT.rec isProp⊥ λ
  { (inl p) → flip≢copy p
  ; (inr a) → flip-not-admissible a }

-- Shorthands for the two-slot instance.
MechsB : PSh Pt ℓ-zero
MechsB = Mechs BoolP BoolP BoolP BoolP x₀ x₀ copyS copyS

AllowedB : Type₁
AllowedB = Allowed BoolP BoolP BoolP BoolP x₀ x₀ copyS copyS

SplitsB : AllowedB → Type
SplitsB = Splits BoolP BoolP BoolP BoolP x₀ x₀ copyS copyS

-- ------------------------------------------------------------
-- The soft world.  The menu can set X hard.  It can keep Y, or
-- it can change Y to flip.  Each slot changes alone, so the
-- menu splits.  But the change of Y to flip is not a hard
-- surgery.  Thus modular and hard are different properties.
-- ------------------------------------------------------------
softY : (c : Unit) → PSh.F₀ MB c → hProp ℓ-zero
softY c m = ∥ fst (P-fix MB copyS c m) ⊎ fst (P-fix MB flipS c m) ∥₁ , squash₁

softY-closed : (d e : Unit) (g : Unit) (m : PSh.F₀ MB d)
             → fst (softY d m) → fst (softY e (PSh.F₁ MB g m))
softY-closed d e g m = PT.map step
  where
    step : _ ⊎ _ → _ ⊎ _
    step (inl p) = inl (P-fix-closed MB copyS d e g m p)
    step (inr p) = inr (P-fix-closed MB flipS d e g m p)

soft : AllowedB
soft = product BoolP BoolP BoolP BoolP x₀ x₀ copyS copyS
         (HardSlot BoolP BoolP x₀ copyS) softY
         (HardSlot-closed BoolP BoolP x₀ copyS) softY-closed

soft-splits : SplitsB soft
soft-splits =
  product-splits BoolP BoolP BoolP BoolP x₀ x₀ copyS copyS
    (HardSlot BoolP BoolP x₀ copyS) softY
    (HardSlot-closed BoolP BoolP x₀ copyS) softY-closed
    (λ c → ∣ inl refl ∣₁) (λ c → ∣ inl refl ∣₁)

-- Keep X and change Y to flip.  The menu allows this act, but
-- it is not a hard surgery.
soft-op : PSh.F₀ MechsB tt
soft-op = copy-mech , flip-mech

soft-not-hard : ¬ (HardOnly BoolP BoolP BoolP BoolP x₀ x₀ copyS copyS soft)
soft-not-hard h =
  flip-not-hard (snd (h tt soft-op (∣ inl refl ∣₁ , ∣ inr refl ∣₁)))

-- ------------------------------------------------------------
-- The fat world.  The only allowed act sets X to true.  The
-- same act also changes Y to flip.  You cannot set X alone.
-- ------------------------------------------------------------
fat : AllowedB
Allowed.A fat c (mX , mY) =
  (fst (Adm BoolP BoolP x₀ c mX) × fst (P-fix MB flipS c mY))
  , isProp× (snd (Adm BoolP BoolP x₀ c mX)) (snd (P-fix MB flipS c mY))
Allowed.A-closed fat d e g (mX , mY) (a , p) =
  Adm-closed BoolP BoolP x₀ d e g mX a , P-fix-closed MB flipS d e g mY p

fat-op : PSh.F₀ MechsB tt
fat-op = const-mech , flip-mech

fat-allowed : fst (Allowed.A fat tt fat-op)
fat-allowed = const-admissible , refl

-- To set X alone, Y must keep copy.  The menu does not allow
-- this.
fat-not-splits : ¬ (SplitsB fat)
fat-not-splits s = flip≢copy (sym (snd (fst (s tt const-mech flip-mech fat-allowed))))

-- ------------------------------------------------------------
-- The joint world.  You must set X and Y together.  You cannot
-- set Y alone.
-- ------------------------------------------------------------
joint : AllowedB
Allowed.A joint c (mX , mY) =
  (fst (Adm BoolP BoolP x₀ c mX) × fst (Adm BoolP BoolP x₀ c mY))
  , isProp× (snd (Adm BoolP BoolP x₀ c mX)) (snd (Adm BoolP BoolP x₀ c mY))
Allowed.A-closed joint d e g (mX , mY) (a , b) =
  Adm-closed BoolP BoolP x₀ d e g mX a , Adm-closed BoolP BoolP x₀ d e g mY b

joint-op : PSh.F₀ MechsB tt
joint-op = const-mech , const-mech

joint-allowed : fst (Allowed.A joint tt joint-op)
joint-allowed = const-admissible , const-admissible

-- Every joint act is a hard surgery.
joint-hard : HardOnly BoolP BoolP BoolP BoolP x₀ x₀ copyS copyS joint
joint-hard c (mX , mY) (a , b) = ∣ inr a ∣₁ , ∣ inr b ∣₁

-- To set Y alone, X must keep copy.  The menu does not allow
-- this.
joint-not-splits : ¬ (SplitsB joint)
joint-not-splits s =
  copy-not-admissible (fst (snd (s tt const-mech const-mech joint-allowed)))
