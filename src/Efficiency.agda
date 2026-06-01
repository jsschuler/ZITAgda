-- Efficiency.agda
-- Defines maximum feasible surplus, the efficiency ratio, and proves
-- that L3 efficiency is non-negative.
--
-- New Agda idea: instance arguments {{...}}
-- These are automatically resolved by the type-checker from declarations
-- in scope. They appear in the stdlib for type-class-like constraints
-- (NonZero, Positive, NonNegative). We declare them locally in where-blocks.
module Efficiency where

open import Data.List     using (List; []; _∷_)
open import Data.Rational using (ℚ; _≤_; _<_; _-_; _+_; _÷_; 1/_; 0ℚ)
open import Data.Rational
  using (NonNegative; NonZero; Positive; nonNegative; positive; >-nonZero)
open import Data.Rational.Properties
  using (≤-refl; pos⇒nonNeg; nonNegative⁻¹; 1/pos⇒pos; nonNeg*nonNeg⇒nonNeg)

open import Agent
open import Surplus using (p≤q⇒0≤q-p)
open import Trace  using (Trace; realizedSurplus; realizedSurplusNonNeg)


-- ── Profitable Pair ───────────────────────────────────────────────────────────
--
-- A profitable pair is a buyer-seller pair where gains from trade are positive:
-- the buyer's valuation exceeds the seller's reservation value.
-- This is the building block of the maximum feasible surplus.
--
-- The proof field is a FIRST-CLASS value stored in the record.
-- It cannot be forged. Constructing a ProfitablePair requires
-- supplying evidence that v_seller ≤ v_buyer.
record ProfitablePair : Set where
  field
    buyer   : Agent
    seller  : Agent
    -- Proof that this pair generates positive gains from trade.
    -- v_seller ≤ v_buyer — necessary for a welfare-improving trade.
    profit  : ValuationSchedule.unitValue (Agent.valuation seller)
            ≤ ValuationSchedule.unitValue (Agent.valuation buyer)


-- ── Pair Gain ─────────────────────────────────────────────────────────────────

-- The surplus of a single profitable pair: v_buyer - v_seller.
-- This is guaranteed ≥ 0 by the profit field.
pairGain : ProfitablePair → ℚ
pairGain pp = ValuationSchedule.unitValue (Agent.valuation (ProfitablePair.buyer  pp))
            - ValuationSchedule.unitValue (Agent.valuation (ProfitablePair.seller pp))

-- pairGain is always non-negative.
pairGainNonNeg : ∀ (pp : ProfitablePair) → 0ℚ ≤ pairGain pp
pairGainNonNeg pp = p≤q⇒0≤q-p (ProfitablePair.profit pp)


-- ── Maximum Feasible Surplus ──────────────────────────────────────────────────
--
-- Given a list of profitable pairs (the optimal matching for this market),
-- the maximum feasible surplus is the sum of their pair gains.
--
-- We do not compute the optimal matching here — we take it as given.
-- In a one-unit-trader market, it is the greedy matching of buyers
-- (sorted by v_b descending) against sellers (sorted by v_s ascending).
-- That construction lives in a future MarketOptimum module.
maxFeasibleSurplus : List ProfitablePair → ℚ
maxFeasibleSurplus []        = 0ℚ
maxFeasibleSurplus (pp ∷ ps) = pairGain pp + maxFeasibleSurplus ps

-- MFS is non-negative: it is a sum of non-negative pair gains.
-- Proof by the same structural induction as sumSurplusNonNeg in Trace.agda.
mfsNonNeg : ∀ (ps : List ProfitablePair) → 0ℚ ≤ maxFeasibleSurplus ps
mfsNonNeg []        = ≤-refl
mfsNonNeg (pp ∷ ps) = 0≤a+b (pairGainNonNeg pp) (mfsNonNeg ps)
  where
    -- Local helper: 0 ≤ a → 0 ≤ b → 0 ≤ a + b
    -- (same as in Trace.agda; repeated here to keep modules independent)
    open import Data.Rational.Properties using (+-mono-≤; +-identityˡ)
    open import Relation.Binary.PropositionalEquality using (subst)
    0≤a+b : {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a + b
    0≤a+b {a} {b} ha hb = subst (_≤ a + b) (+-identityˡ 0ℚ) (+-mono-≤ ha hb)


-- ── Efficiency Ratio ──────────────────────────────────────────────────────────
--
-- Efficiency = realizedSurplus / maxFeasibleSurplus
--
-- _÷_ requires a proof that the denominator is NonZero.
-- We express this as 0 < mfs (strict positivity implies NonZero).
--
-- Instance arguments ({{...}}) are Agda's mechanism for type-class-style
-- constraints. When _÷_ is called, Agda looks for a {{NonZero q}} in scope.
-- We declare it in a where-block via "instance _ : NonZero ... = ..."
-- The underscore _ is an anonymous name — we don't need to refer to it.
--
-- In Julia: comparable to @require from the Requires.jl package,
-- but enforced at compile time, not runtime.
efficiencyRatio : (t : Trace) (ps : List ProfitablePair)
                → 0ℚ < maxFeasibleSurplus ps
                → ℚ
efficiencyRatio t ps mfs>0 = realizedSurplus t ÷ maxFeasibleSurplus ps
  where
    instance
      _ : NonZero (maxFeasibleSurplus ps)
      _ = >-nonZero mfs>0


-- ── Theorem 4: L3 Efficiency is Non-Negative ─────────────────────────────────
--
-- THEOREM.
-- For any L3 trace t and market ps with positive MFS:
--   0 ≤ efficiencyRatio t ps
--
-- PROOF.
--   realizedSurplus t ≥ 0         [Theorem 3, realizedSurplusNonNeg]
--   1/(mfs) > 0                   [mfs > 0 and 1/pos⇒pos]
--   product of non-negatives ≥ 0  [nonNeg*nonNeg⇒nonNeg]
--   but eff = realized * (1/mfs) = realized ÷ mfs   [definitional]
--
-- The key step uses nonNeg*nonNeg⇒nonNeg, which takes NonNegative instances
-- for both factors and returns NonNegative for their product.
-- We then extract 0 ≤ eff from NonNegative eff via nonNegative⁻¹.
--
-- _÷_ is definitionally _*_ (1/_), so eff and realized*(1/mfs) are
-- the same term — no coercion needed.

l3EfficiencyNonNeg
  : ∀ (t : Trace) (ps : List ProfitablePair) (mfs>0 : 0ℚ < maxFeasibleSurplus ps)
  → 0ℚ ≤ efficiencyRatio t ps mfs>0

l3EfficiencyNonNeg t ps mfs>0 =
  nonNegative⁻¹ (efficiencyRatio t ps mfs>0)
  where
    mfs = maxFeasibleSurplus ps
    instance
      nz : NonZero mfs
      nz = >-nonZero mfs>0
      pq : Positive mfs
      pq = positive mfs>0
      pi : Positive (1/ mfs)
      pi = 1/pos⇒pos mfs
      ni : NonNegative (1/ mfs)
      ni = pos⇒nonNeg (1/ mfs)
      nr : NonNegative (realizedSurplus t)
      nr = nonNegative (realizedSurplusNonNeg t)
      ne : NonNegative (efficiencyRatio t ps mfs>0)
      ne = nonNeg*nonNeg⇒nonNeg (realizedSurplus t) (1/ mfs)
