-- MixedEffFSD.agda
-- Efficiency ratio FSD for mixed markets, extending MixedWelfare.agda
-- (oracle-mix raw surplus) to the efficiency ratio metric.
--
-- The oracle-mix efficiency ratio:
--
--   concreteMixEffN envs hmix ps mfs>0 ss
--     = concreteMixSurplusN envs hmix ss ÷ mfs
--
-- Main results:
--
--   mixEffFSDom-l3:
--     FSDom (concreteMixEffN envs hmix ps mfs>0)
--           (concreteL3EffN envs ps mfs>0) Ω
--
--   mixEffFSDom-l0:
--     FSDom (concreteMixEffN envs hmix ps mfs>0)
--           (concreteL0EffN envs ps mfs>0) Ω
--
-- where concreteL3EffN and concreteL0EffN are from MultiAgentEffFSD.agda.
--
-- PROOF STRUCTURE.
-- Identical to Modules 19–20: lift pointwise raw-surplus bounds
-- (l3LE-mix, l0LE-mix — reproved locally, private in MixedWelfare)
-- via *-monoʳ-≤-nonNeg (1/ mfs).  Instance chain per theorem where-block.
--
-- COMPLETION OF THE 3D TABLE.
--   Single pair  × raw surplus  — Module 17 (Stochastic)
--   Single pair  × efficiency   — Module 19 (EfficiencyFSD)
--   k pairs      × raw surplus  — Module 18 (MultiAgentSim)
--   k pairs      × efficiency   — Module 20 (MultiAgentEffFSD)
--   Mixed market × raw surplus  — Module 21 (MixedWelfare)
--   Mixed market × efficiency   — Module 22 (MixedEffFSD)        ← this module
--
-- Zero changes to any existing module.

module MixedEffFSD where

open import Data.Nat      using (ℕ; suc)
open import Data.List     using (List; []; _∷_; map)
open import Data.Vec      using (Vec) renaming ([] to v[]; _∷_ to _v∷_)
open import Data.Rational using (ℚ; _≤_; _<_; _+_; 0ℚ; _÷_; 1/_; _⊓_)
open import Data.Rational using (NonNegative; NonZero; Positive
                                ; positive; >-nonZero)
open import Data.Product  using (proj₁; proj₂)
import Data.Rational.Properties as ℚP
open import Data.Rational.Properties using (pos⇒nonNeg; 1/pos⇒pos)

open import Agent
open import Seed            using (Seed)
open import Trace           using (realizedSurplus; realizedSurplusNonNeg)
open import SimulationModel using (l0RealizedSurplus)
open import FlagshipFull    using (SimEnvironment; concreteSim)
open import L0AgentStrategy using (concreteL0Sim; l0Nonpos-inverted; l3LE-l0-productive)
open import Efficiency      using (ProfitablePair; maxFeasibleSurplus)
open import Probability     using (sumQ)
open import Stochastic      using (FSDom; FSD-from-pointwise)
open import MultiAgentSim   using (realizedSurplusN; l0RealizedSurplusN)
open import MultiAgentEffFSD using (concreteL3EffN; concreteL0EffN)
open import MixedWelfare    using (Mixed; mix[]; invMix; prodMix; concreteMixSurplusN)


-- ── Local Abbreviations ───────────────────────────────────────────────────────

private
  vB : SimEnvironment → ℚ
  vB env = ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))

  vS : SimEnvironment → ℚ
  vS env = ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))

  capEnv : SimEnvironment → ℚ
  capEnv env = vB env ⊓ Agent.budget (SimEnvironment.buyer env)


-- ── Oracle Mix Efficiency Function ───────────────────────────────────────────
--
-- concreteMixEffN envs hmix ps mfs>0 ss
--   = oracle-mix total surplus ÷ mfs
--
-- Definitionally: concreteMixSurplusN ... * (1/ mfs), which is what
-- *-monoʳ-≤-nonNeg operates on.

concreteMixEffN
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → Mixed envs
  → (ps : List ProfitablePair)
  → 0ℚ < maxFeasibleSurplus ps
  → Vec (Seed (suc n) 2) k → ℚ
concreteMixEffN {n} envs hmix ps mfs>0 ss =
  concreteMixSurplusN {n} envs hmix ss ÷ maxFeasibleSurplus ps
  where instance _ = >-nonZero mfs>0


-- ── Private Helpers ───────────────────────────────────────────────────────────

private

  -- LEMMA (l3LE-mix).
  -- Reproved from the private version in MixedWelfare.agda.

  l3LE-mix
    : ∀ {n k} (envs : Vec SimEnvironment k) (hmix : Mixed envs)
    → (ss : Vec (Seed (suc n) 2) k)
    → realizedSurplusN {n} envs ss ≤ concreteMixSurplusN {n} envs hmix ss
  l3LE-mix v[]        mix[]            v[]        = ℚP.≤-refl
  l3LE-mix (e v∷ es) (invMix  _ hmix) (s v∷ ss) =
    ℚP.+-monoʳ-≤ (realizedSurplus (concreteSim e s)) (l3LE-mix es hmix ss)
  l3LE-mix (e v∷ es) (prodMix h hmix) (s v∷ ss) =
    ℚP.+-mono-≤
      (l3LE-l0-productive e s (proj₁ h) (proj₁ (proj₂ h)) (proj₂ (proj₂ h)))
      (l3LE-mix es hmix ss)

  -- LEMMA (l0LE-mix).
  -- Reproved from the private version in MixedWelfare.agda.

  l0LE-mix
    : ∀ {n k} (envs : Vec SimEnvironment k) (hmix : Mixed envs)
    → (ss : Vec (Seed (suc n) 2) k)
    → l0RealizedSurplusN {n} envs ss ≤ concreteMixSurplusN {n} envs hmix ss
  l0LE-mix v[]        mix[]            v[]        = ℚP.≤-refl
  l0LE-mix (e v∷ es) (invMix  h hmix) (s v∷ ss) =
    ℚP.+-mono-≤
      (ℚP.≤-trans
        (l0Nonpos-inverted e s h)
        (realizedSurplusNonNeg (concreteSim e s)))
      (l0LE-mix es hmix ss)
  l0LE-mix (e v∷ es) (prodMix _ hmix) (s v∷ ss) =
    ℚP.+-monoʳ-≤ (l0RealizedSurplus (concreteL0Sim e s)) (l0LE-mix es hmix ss)

  -- LEMMA (sumQ-map-mono).
  -- Reproved locally (private in Stochastic.agda).

  sumQ-map-mono
    : {S : Set} (f g : S → ℚ) (xs : List S)
    → (∀ s → g s ≤ f s)
    → sumQ (map g xs) ≤ sumQ (map f xs)
  sumQ-map-mono f g []       _  = ℚP.≤-refl
  sumQ-map-mono f g (x ∷ xs) pw =
    ℚP.+-mono-≤ (pw x) (sumQ-map-mono f g xs pw)


-- ── FSD Theorems ──────────────────────────────────────────────────────────────

-- THEOREM (mixEffFSDom-l3).
-- Oracle-mix efficiency FSD-dominates pure L3 efficiency in any mixed market:
--
--   FSDom (concreteMixEffN envs hmix ps mfs>0)
--         (concreteL3EffN envs ps mfs>0) Ω
--
-- PROOF. FSD-from-pointwise.  Pointwise:
--   realizedSurplusN ss * (1/mfs) ≤ concreteMixSurplusN ss * (1/mfs)
-- from l3LE-mix lifted by *-monoʳ-≤-nonNeg (1/ mfs). ✓

mixEffFSDom-l3
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → (hmix : Mixed envs)
  → (ps : List ProfitablePair)
  → (mfs>0 : 0ℚ < maxFeasibleSurplus ps)
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → FSDom (concreteMixEffN {n} envs hmix ps mfs>0)
          (concreteL3EffN {n} envs ps mfs>0)
          Ω
mixEffFSDom-l3 {n} envs hmix ps mfs>0 Ω =
  FSD-from-pointwise _ _ Ω
    (λ ss → ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (l3LE-mix {n} envs hmix ss))
  where
    mfs = maxFeasibleSurplus ps
    instance
      _   = >-nonZero mfs>0
      pc  : Positive mfs;          pc  = positive mfs>0
      p1c : Positive (1/ mfs);     p1c = 1/pos⇒pos mfs
      n1c : NonNegative (1/ mfs);  n1c = pos⇒nonNeg (1/ mfs)


-- THEOREM (mixEffFSDom-l0).
-- Oracle-mix efficiency FSD-dominates pure L0 efficiency in any mixed market:
--
--   FSDom (concreteMixEffN envs hmix ps mfs>0)
--         (concreteL0EffN envs ps mfs>0) Ω
--
-- PROOF. FSD-from-pointwise + l0LE-mix lifted by *-monoʳ-≤-nonNeg (1/ mfs). ✓

mixEffFSDom-l0
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → (hmix : Mixed envs)
  → (ps : List ProfitablePair)
  → (mfs>0 : 0ℚ < maxFeasibleSurplus ps)
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → FSDom (concreteMixEffN {n} envs hmix ps mfs>0)
          (concreteL0EffN {n} envs ps mfs>0)
          Ω
mixEffFSDom-l0 {n} envs hmix ps mfs>0 Ω =
  FSD-from-pointwise _ _ Ω
    (λ ss → ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (l0LE-mix {n} envs hmix ss))
  where
    mfs = maxFeasibleSurplus ps
    instance
      _   = >-nonZero mfs>0
      pc  : Positive mfs;          pc  = positive mfs>0
      p1c : Positive (1/ mfs);     p1c = 1/pos⇒pos mfs
      n1c : NonNegative (1/ mfs);  n1c = pos⇒nonNeg (1/ mfs)


-- ── Expected Efficiency Corollaries ──────────────────────────────────────────

-- COROLLARY (mixEffExpected-l3).
-- E[oracle-mix efficiency] ≥ E[L3 efficiency] in any mixed market.

mixEffExpected-l3
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → (hmix : Mixed envs)
  → (ps : List ProfitablePair)
  → (mfs>0 : 0ℚ < maxFeasibleSurplus ps)
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → sumQ (map (concreteL3EffN {n} envs ps mfs>0) Ω)
    ≤ sumQ (map (concreteMixEffN {n} envs hmix ps mfs>0) Ω)
mixEffExpected-l3 {n} envs hmix ps mfs>0 Ω =
  sumQ-map-mono _ _ Ω
    (λ ss → ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (l3LE-mix {n} envs hmix ss))
  where
    mfs = maxFeasibleSurplus ps
    instance
      _   = >-nonZero mfs>0
      pc  : Positive mfs;          pc  = positive mfs>0
      p1c : Positive (1/ mfs);     p1c = 1/pos⇒pos mfs
      n1c : NonNegative (1/ mfs);  n1c = pos⇒nonNeg (1/ mfs)


-- COROLLARY (mixEffExpected-l0).
-- E[oracle-mix efficiency] ≥ E[L0 efficiency] in any mixed market.

mixEffExpected-l0
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → (hmix : Mixed envs)
  → (ps : List ProfitablePair)
  → (mfs>0 : 0ℚ < maxFeasibleSurplus ps)
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → sumQ (map (concreteL0EffN {n} envs ps mfs>0) Ω)
    ≤ sumQ (map (concreteMixEffN {n} envs hmix ps mfs>0) Ω)
mixEffExpected-l0 {n} envs hmix ps mfs>0 Ω =
  sumQ-map-mono _ _ Ω
    (λ ss → ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (l0LE-mix {n} envs hmix ss))
  where
    mfs = maxFeasibleSurplus ps
    instance
      _   = >-nonZero mfs>0
      pc  : Positive mfs;          pc  = positive mfs>0
      p1c : Positive (1/ mfs);     p1c = 1/pos⇒pos mfs
      n1c : NonNegative (1/ mfs);  n1c = pos⇒nonNeg (1/ mfs)
