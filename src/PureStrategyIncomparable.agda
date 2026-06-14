-- PureStrategyIncomparable.agda
-- Negative result: in a mixed market, neither pure strategy FSD-dominates the other.
--
-- MAIN RESULTS.
--
--   l0NotFSDom-l3-mixed:
--     l0RealizedSurplusN envs ss₁ < 0ℚ →
--     ¬ FSDom (l0RealizedSurplusN envs) (realizedSurplusN envs) (ss₁ ∷ [])
--
--   l3NotFSDom-l0-mixed:
--     realizedSurplusN envs ss₂ < l0RealizedSurplusN envs ss₂ →
--     ¬ FSDom (realizedSurplusN envs) (l0RealizedSurplusN envs) (ss₂ ∷ [])
--
-- PROOF STRUCTURE.
-- Each proof exhibits a threshold t at which the FSDom inequality
-- survivalCount g [ss] t ≤ℕ survivalCount f [ss] t fails:
--
--   l0NotFSDom-l3-mixed: threshold t = 0.
--     survivalCount L3 [ss₁] 0 = 1  (L3 ≥ 0 always, from realizedSurplusN-nonNeg)
--     survivalCount L0 [ss₁] 0 = 0  (L0(ss₁) < 0 by hypothesis)
--     FSDom gives 1 ≤ℕ 0 — absurd.
--
--   l3NotFSDom-l0-mixed: threshold t = l0RealizedSurplusN envs ss₂.
--     survivalCount L0 [ss₂] t = 1  (L0(ss₂) ≥ t by ≤-refl)
--     survivalCount L3 [ss₂] t = 0  (L3(ss₂) < t by hypothesis)
--     FSDom gives 1 ≤ℕ 0 — absurd.
--
-- ECONOMIC INTERPRETATION.
-- In any market with both inverted and productive pairs, L0 sometimes yields
-- negative surplus (the inverted pair) and L3 sometimes yields strictly less
-- surplus than L0 (the productive pair).  Neither strategy uniformly dominates;
-- the oracle mix from Modules 21–22 is required for a dominant strategy.
--
-- RELATION TO PRIOR MODULES.
-- Modules 21–22 show the oracle mix FSD-dominates both pure strategies.
-- This module shows the converse implication fails: pure strategies are
-- not comparable to each other under FSD in a mixed market.

module PureStrategyIncomparable where

open import Data.Nat      using (ℕ; suc) renaming (_≤_ to _≤ℕ_)
open import Data.List     using (List; []; _∷_)
open import Data.Vec      using (Vec) renaming ([] to v[]; _∷_ to _v∷_)
open import Data.Rational using (ℚ; _≤_; _<_; 0ℚ)
import Data.Rational.Properties as ℚP
open import Data.Empty    using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂)

open import Agent
open import Seed          using (Seed)
open import Trace         using (realizedSurplus; realizedSurplusNonNeg)
open import FlagshipFull  using (SimEnvironment; concreteSim)
open import Stochastic    using (FSDom; survivalCount)
open import MultiAgentSim using (realizedSurplusN; l0RealizedSurplusN)


-- ── Private Helpers ───────────────────────────────────────────────────────────

private

  -- LEMMA (realizedSurplusN-nonNeg).
  -- Pure L3 realized surplus is always ≥ 0, by induction on the Vec.
  -- Each pair's contribution is non-negative by realizedSurplusNonNeg.

  realizedSurplusN-nonNeg
    : ∀ {n k} (envs : Vec SimEnvironment k) (ss : Vec (Seed (suc n) 2) k)
    → 0ℚ ≤ realizedSurplusN {n} envs ss
  realizedSurplusN-nonNeg v[]       v[]       = ℚP.≤-refl
  realizedSurplusN-nonNeg (e v∷ es) (s v∷ ss) =
    ℚP.+-mono-≤
      (realizedSurplusNonNeg (concreteSim e s))
      (realizedSurplusN-nonNeg es ss)

  -- LEMMA (sc-singleton-yes).
  -- If t ≤ f x, then survivalCount f [x] t = 1.
  -- PROOF. After filterᵇ reduction, the predicate isYes (t ≤? f x) is true
  -- (since t ≤? f x = yes _ when t ≤ f x), so the filter keeps x; length = 1. ✓

  sc-singleton-yes
    : {S : Set} (f : S → ℚ) (x : S) (t : ℚ)
    → t ≤ f x
    → survivalCount f (x ∷ []) t ≡ 1
  sc-singleton-yes f x t h with ℚP._≤?_ t (f x)
  ... | yes _ = refl
  ... | no nh = ⊥-elim (nh h)

  -- LEMMA (sc-singleton-no).
  -- If f x < t, then survivalCount f [x] t = 0.
  -- PROOF. After filterᵇ reduction, the predicate isYes (t ≤? f x) is false
  -- (since t > f x, so t ≤? f x = no _), so the filter drops x; length = 0. ✓

  sc-singleton-no
    : {S : Set} (f : S → ℚ) (x : S) (t : ℚ)
    → f x < t
    → survivalCount f (x ∷ []) t ≡ 0
  sc-singleton-no f x t h with ℚP._≤?_ t (f x)
  ... | yes lh = ⊥-elim (ℚP.<-irrefl (ℚP.≤-antisym (ℚP.<⇒≤ h) lh) h)
  ... | no _   = refl

  -- ¬ (1 ≤ℕ 0): absurd by exhaustion of ≤ constructors.
  ¬1≤ℕ0 : ¬ (1 ≤ℕ 0)
  ¬1≤ℕ0 ()


-- ── Main Theorems ─────────────────────────────────────────────────────────────

-- THEOREM (l0NotFSDom-l3-mixed).
-- If L0 surplus is strictly negative at some seed ss₁,
-- then L0 does not FSD-dominate L3 on the singleton population [ss₁].

l0NotFSDom-l3-mixed
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → (ss₁ : Vec (Seed (suc n) 2) k)
  → l0RealizedSurplusN {n} envs ss₁ < 0ℚ
  → ¬ FSDom (l0RealizedSurplusN {n} envs) (realizedSurplusN {n} envs) (ss₁ ∷ [])
l0NotFSDom-l3-mixed {n} envs ss₁ h fsd =
  -- fsd 0ℚ : survivalCount L3 [ss₁] 0 ≤ℕ survivalCount L0 [ss₁] 0
  let leq  = fsd 0ℚ
      c-l3 = sc-singleton-yes (realizedSurplusN {n} envs) ss₁ 0ℚ
               (realizedSurplusN-nonNeg envs ss₁)
      c-l0 = sc-singleton-no (l0RealizedSurplusN {n} envs) ss₁ 0ℚ h
  in ¬1≤ℕ0 (subst₂ _≤ℕ_ c-l3 c-l0 leq)


-- THEOREM (l3NotFSDom-l0-mixed).
-- If L3 surplus is strictly less than L0 surplus at some seed ss₂,
-- then L3 does not FSD-dominate L0 on the singleton population [ss₂].

l3NotFSDom-l0-mixed
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → (ss₂ : Vec (Seed (suc n) 2) k)
  → realizedSurplusN {n} envs ss₂ < l0RealizedSurplusN {n} envs ss₂
  → ¬ FSDom (realizedSurplusN {n} envs) (l0RealizedSurplusN {n} envs) (ss₂ ∷ [])
l3NotFSDom-l0-mixed {n} envs ss₂ h fsd =
  -- fsd t : survivalCount L0 [ss₂] t ≤ℕ survivalCount L3 [ss₂] t
  -- at t = l0RealizedSurplusN envs ss₂
  let t    = l0RealizedSurplusN {n} envs ss₂
      leq  = fsd t
      c-l0 = sc-singleton-yes (l0RealizedSurplusN {n} envs) ss₂ t ℚP.≤-refl
      c-l3 = sc-singleton-no  (realizedSurplusN {n} envs) ss₂ t h
  in ¬1≤ℕ0 (subst₂ _≤ℕ_ c-l0 c-l3 leq)
