-- EfficiencyFSD.agda
-- First-order stochastic dominance on efficiency ratios, extending the raw-surplus
-- FSD results in Stochastic.agda to the metric used in Gode & Sunder (1993).
--
-- The efficiency ratio  eff(s) = realizedSurplus(s) / maxFeasibleSurplus(ps)
-- measures what fraction of the available gains from trade an institution
-- actually realises.  Gode & Sunder's headline result is that ZIT agents in a
-- double auction achieve near-100% efficiency — the institution does the work.
--
-- This module proves FSD on efficiency ratios for both market environments:
--
--   INVERTED  (v_b ≤ v_s, mfs > 0):
--     l3EffFSDom-l0-inverted   — L3 efficiency FSD-dominates L0 efficiency
--
--   PRODUCTIVE (v_s ≤ v_b, mfs > 0):
--     l0EffFSDom-l3-productive — L0 efficiency FSD-dominates L3 efficiency
--
-- Both theorems share the same proof structure:
--   1. The corresponding raw-surplus pointwise bound (l0Nonpos-inverted or
--      l3LE-l0-productive from L0AgentStrategy.agda).
--   2. div-mono-≤: dividing both sides by the positive mfs preserves ≤.
--   3. FSD-from-pointwise (Stochastic.agda).
--
-- Expected-value corollaries (E[eff L3] vs E[eff L0]) follow by
-- sumQ-map-mono, exactly as in Stochastic.agda and MultiAgentSim.agda.
--
-- HYPOTHESIS (mfs > 0).
-- Both directions require maxFeasibleSurplus ps > 0 to define the efficiency
-- ratio.  In the inverted case this means the profitable-pair list ps must
-- come from OUTSIDE the inverted pair (e.g. from a parallel productive sub-
-- market).  In the productive case, mfs > 0 iff v_b > v_s strictly — the
-- natural condition for efficiency to be meaningful.
--
-- EXTENSION STRUCTURE.
-- Every proof here applies an existing lemma:
--   l0Nonpos-inverted  (L0AgentStrategy) + div-mono-≤ → l3EffFSDom-l0-inverted
--   l3LE-l0-productive (L0AgentStrategy) + div-mono-≤ → l0EffFSDom-l3-productive
--   FSD-from-pointwise (Stochastic)                   → both FSD theorems
--   sumQ-map-mono      (reproved locally)              → both expected theorems

module EfficiencyFSD where

open import Data.Nat      using (ℕ; suc)
open import Data.List     using (List; []; _∷_; map)
open import Data.Rational using (ℚ; _≤_; _<_; 0ℚ; _÷_; 1/_; _⊓_)
open import Data.Rational using (NonNegative; NonZero; Positive
                                ; nonNegative; positive; >-nonZero)
import Data.Rational.Properties as ℚP
open import Data.Rational.Properties using (pos⇒nonNeg; 1/pos⇒pos)

open import Agent
open import Seed            using (Seed)
open import Flagship        using (RawMatch)
open import SimulationModel using (l0RealizedSurplus)
open import Trace           using (realizedSurplusNonNeg)
open import FlagshipFull    using (SimEnvironment; concreteSim)
open import L0AgentStrategy using (concreteL0Sim; l0Nonpos-inverted; l3LE-l0-productive)
open import Efficiency      using (ProfitablePair; maxFeasibleSurplus; efficiencyRatio)
open import Probability     using (sumQ)
open import Stochastic      using (FSDom; FSD-from-pointwise)


-- ── L0 Efficiency Ratio ───────────────────────────────────────────────────────
--
-- The L0 counterpart of efficiencyRatio from Efficiency.agda.
-- Takes the raw L0 match list (not a Trace) and divides by mfs.
--
-- efficiencyRatio  : Trace         → List ProfitablePair → mfs > 0 → ℚ
-- l0EfficiencyRatio: List RawMatch → List ProfitablePair → mfs > 0 → ℚ
--
-- The asymmetry mirrors the single-pair case: L3 produces a certified Trace,
-- L0 produces uncertified RawMatches.  The efficiency denominator mfs is the
-- same for both.

l0EfficiencyRatio
  : List RawMatch → (ps : List ProfitablePair) → 0ℚ < maxFeasibleSurplus ps → ℚ
l0EfficiencyRatio ms ps mfs>0 = l0RealizedSurplus ms ÷ maxFeasibleSurplus ps
  where
    instance _ : NonZero (maxFeasibleSurplus ps)
             _ = >-nonZero mfs>0


-- ── Concrete Efficiency Functions ────────────────────────────────────────────
--
-- Given a fixed environment, profitable-pair list ps, and mfs > 0:
--
--   concreteL3Eff env ps mfs>0 : Seed (suc n) 2 → ℚ
--   concreteL0Eff env ps mfs>0 : Seed (suc n) 2 → ℚ
--
-- These are the functions to which FSDom is applied.

concreteL3Eff
  : ∀ {n} (env : SimEnvironment) (ps : List ProfitablePair)
  → 0ℚ < maxFeasibleSurplus ps
  → Seed (suc n) 2 → ℚ
concreteL3Eff {n} env ps mfs>0 s = efficiencyRatio (concreteSim {n} env s) ps mfs>0

concreteL0Eff
  : ∀ {n} (env : SimEnvironment) (ps : List ProfitablePair)
  → 0ℚ < maxFeasibleSurplus ps
  → Seed (suc n) 2 → ℚ
concreteL0Eff {n} env ps mfs>0 s = l0EfficiencyRatio (concreteL0Sim {n} env s) ps mfs>0


-- ── Private Helpers ───────────────────────────────────────────────────────────
--
-- KEY BRIDGE.
-- a ÷ c = a * (1/c) definitionally.  Division by a positive c is
-- order-preserving because *-monoʳ-≤-nonNeg (1/c) applies: NonNeg (1/c)
-- follows from 0 < c via positive → 1/pos⇒pos → pos⇒nonNeg.
--
-- Rather than package this as a standalone lemma (whose return type
-- a ÷ c ≤ b ÷ c would require {{NonZero c}} at the type level),
-- we provide the instance chain in each theorem's where-block and call
-- *-monoʳ-≤-nonNeg (1/ mfs) directly.  Agda accepts the result by
-- definitional equality with the unfolded ÷.

private

  -- LEMMA (sumQ-map-mono).
  -- If g(s) ≤ f(s) for every s, then sumQ (map g Ω) ≤ sumQ (map f Ω).
  -- This lemma is private in Stochastic.agda and MultiAgentSim.agda;
  -- reproved here for the expected-efficiency corollaries.

  sumQ-map-mono
    : {S : Set} (f g : S → ℚ) (xs : List S)
    → (∀ s → g s ≤ f s)
    → sumQ (map g xs) ≤ sumQ (map f xs)
  sumQ-map-mono f g []       _  = ℚP.≤-refl
  sumQ-map-mono f g (x ∷ xs) pw =
    ℚP.+-mono-≤ (pw x) (sumQ-map-mono f g xs pw)


-- ── FSD Theorems ──────────────────────────────────────────────────────────────

-- THEOREM (l3EffFSDom-l0-inverted).
-- In an inverted market (v_b ≤ v_s) with positive mfs, L3's efficiency
-- distribution first-order stochastically dominates L0's:
--
--   FSDom (concreteL3Eff env ps mfs>0) (concreteL0Eff env ps mfs>0) Ω
--
-- PROOF.
-- By FSD-from-pointwise.  Pointwise bound:
--   l0 efficiency(s) ≤ l3 efficiency(s)
-- i.e.,
--   l0(s) ÷ mfs  ≤  0 ÷ mfs  ≤  l3(s) ÷ mfs
--
-- Left half:  l0(s) ≤ 0  [l0Nonpos-inverted], apply div-mono-≤.
-- Right half: 0 ≤ l3(s)  [realizedSurplusNonNeg], apply div-mono-≤.
-- Combine by ≤-trans.

l3EffFSDom-l0-inverted
  : ∀ {n} (env : SimEnvironment)
  → ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))
    ≤ ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))
  → (ps : List ProfitablePair)
  → (mfs>0 : 0ℚ < maxFeasibleSurplus ps)
  → (Ω : List (Seed (suc n) 2))
  → FSDom (concreteL3Eff {n} env ps mfs>0)
          (concreteL0Eff {n} env ps mfs>0)
          Ω
l3EffFSDom-l0-inverted {n} env h_inv ps mfs>0 Ω =
  FSD-from-pointwise _ _ Ω
    (λ s → ℚP.≤-trans
              (ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (l0Nonpos-inverted {n} env s h_inv))
              (ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (realizedSurplusNonNeg (concreteSim {n} env s))))
  where
    mfs = maxFeasibleSurplus ps
    instance
      _   = >-nonZero mfs>0
      pc  : Positive mfs;          pc  = positive mfs>0
      p1c : Positive (1/ mfs);     p1c = 1/pos⇒pos mfs
      n1c : NonNegative (1/ mfs);  n1c = pos⇒nonNeg (1/ mfs)


-- THEOREM (l0EffFSDom-l3-productive).
-- In a productive market (v_s ≤ v_b, with 0 ≤ v_s and cap ≤ maxP) with
-- positive mfs, L0's efficiency distribution first-order stochastically
-- dominates L3's:
--
--   FSDom (concreteL0Eff env ps mfs>0) (concreteL3Eff env ps mfs>0) Ω
--
-- PROOF.
-- By FSD-from-pointwise.  Pointwise bound:
--   l3(s) ÷ mfs  ≤  l0(s) ÷ mfs
-- follows from l3(s) ≤ l0(s) [l3LE-l0-productive] and div-mono-≤.
--
-- GODE & SUNDER CONNECTION.
-- This is the formal analogue of G&S's finding that unrestricted ZIT agents
-- (L0) achieve higher efficiency than constrained agents (L3) in productive
-- markets: L3 misses value-creating trades that L0 would execute.
-- The FSD statement is strictly stronger than a comparison of means.

l0EffFSDom-l3-productive
  : ∀ {n} (env : SimEnvironment)
  → 0ℚ ≤ ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))
  → ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))
    ≤ ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))
  → (  ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))
     ⊓ Agent.budget (SimEnvironment.buyer env))
    ≤ SimEnvironment.maxP env
  → (ps : List ProfitablePair)
  → (mfs>0 : 0ℚ < maxFeasibleSurplus ps)
  → (Ω : List (Seed (suc n) 2))
  → FSDom (concreteL0Eff {n} env ps mfs>0)
          (concreteL3Eff {n} env ps mfs>0)
          Ω
l0EffFSDom-l3-productive {n} env hVS hProd hCap ps mfs>0 Ω =
  FSD-from-pointwise _ _ Ω
    (λ s → ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (l3LE-l0-productive {n} env s hVS hProd hCap))
  where
    mfs = maxFeasibleSurplus ps
    instance
      _   = >-nonZero mfs>0
      pc  : Positive mfs;          pc  = positive mfs>0
      p1c : Positive (1/ mfs);     p1c = 1/pos⇒pos mfs
      n1c : NonNegative (1/ mfs);  n1c = pos⇒nonNeg (1/ mfs)


-- ── Expected Efficiency Corollaries ──────────────────────────────────────────
--
-- Summing the pointwise efficiency bounds gives expected-value comparisons.
-- As in Stochastic.agda, FSD is strictly stronger than expected-value dominance;
-- both are proved directly from the pointwise ingredient.

-- COROLLARY (l3EffExpected-l0-inverted).
-- E[L3 efficiency] ≥ E[L0 efficiency] in inverted markets with mfs > 0.

l3EffExpected-l0-inverted
  : ∀ {n} (env : SimEnvironment)
  → ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))
    ≤ ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))
  → (ps : List ProfitablePair)
  → (mfs>0 : 0ℚ < maxFeasibleSurplus ps)
  → (Ω : List (Seed (suc n) 2))
  → sumQ (map (concreteL0Eff {n} env ps mfs>0) Ω)
    ≤ sumQ (map (concreteL3Eff {n} env ps mfs>0) Ω)
l3EffExpected-l0-inverted {n} env h_inv ps mfs>0 Ω =
  sumQ-map-mono _ _ Ω
    (λ s → ℚP.≤-trans
              (ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (l0Nonpos-inverted {n} env s h_inv))
              (ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (realizedSurplusNonNeg (concreteSim {n} env s))))
  where
    mfs = maxFeasibleSurplus ps
    instance
      _   = >-nonZero mfs>0
      pc  : Positive mfs;          pc  = positive mfs>0
      p1c : Positive (1/ mfs);     p1c = 1/pos⇒pos mfs
      n1c : NonNegative (1/ mfs);  n1c = pos⇒nonNeg (1/ mfs)


-- COROLLARY (l0EffExpected-l3-productive).
-- E[L0 efficiency] ≥ E[L3 efficiency] in productive markets with mfs > 0.

l0EffExpected-l3-productive
  : ∀ {n} (env : SimEnvironment)
  → 0ℚ ≤ ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))
  → ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))
    ≤ ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))
  → (  ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))
     ⊓ Agent.budget (SimEnvironment.buyer env))
    ≤ SimEnvironment.maxP env
  → (ps : List ProfitablePair)
  → (mfs>0 : 0ℚ < maxFeasibleSurplus ps)
  → (Ω : List (Seed (suc n) 2))
  → sumQ (map (concreteL3Eff {n} env ps mfs>0) Ω)
    ≤ sumQ (map (concreteL0Eff {n} env ps mfs>0) Ω)
l0EffExpected-l3-productive {n} env hVS hProd hCap ps mfs>0 Ω =
  sumQ-map-mono _ _ Ω
    (λ s → ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (l3LE-l0-productive {n} env s hVS hProd hCap))
  where
    mfs = maxFeasibleSurplus ps
    instance
      _   = >-nonZero mfs>0
      pc  : Positive mfs;          pc  = positive mfs>0
      p1c : Positive (1/ mfs);     p1c = 1/pos⇒pos mfs
      n1c : NonNegative (1/ mfs);  n1c = pos⇒nonNeg (1/ mfs)
