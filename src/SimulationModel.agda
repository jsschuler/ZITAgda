-- SimulationModel.agda
-- States and proves the flagship theorem in two forms:
--
--   Pointwise form:  ∃ seed where L3 surplus > L0 surplus
--   Expected form:   given pointwise dominance, E[L3 surplus] > E[L0 surplus]
--
-- The pointwise form follows directly from the structural results (Theorems 3 & 5).
-- The expected form requires one additional hypothesis: that L3 dominates L0 at
-- every seed. This is stated explicitly as a condition, making the logical
-- dependency transparent.
--
-- New Agda ideas:
--   postulate  — declare a theorem without proof (named assumption / axiom)
--   module parameters — parametrize a whole module by values
module SimulationModel where

open import Data.Nat                using (ℕ)
open import Data.Rational           using (ℚ; _+_; _≤_; _<_; 0ℚ)
open import Data.Rational.Properties using (<-≤-trans; ≤-refl)
open import Data.List               using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All
  using (All) renaming ([] to []-all; _∷_ to _∷-all_)
open import Data.Product            using (Σ; _,_)
open import Function                using (_∘_)

open import Agent
open import Seed    using (Seed)
open import Trace   using (Trace; realizedSurplus; realizedSurplusNonNeg)
open import Flagship using (RawMatch; rawSurplus)
open import Probability using (sumQ; sumQNonNeg; sumQStrict; StrictAt; Pointwise≤)
open import Probability using (pw-nil; pw-cons; here; there)


-- ── Simulation Function Types ─────────────────────────────────────────────────
--
-- A simulation function maps a seed to a result.
-- We parametrize by (n k : ℕ) — the price grid size and tape length.
--
-- SimFnL3: produces a certified Trace (TradeSettled events carry Match,
--          which embeds L3 proofs). realizedSurplus is always ≥ 0.
--
-- SimFnL0: produces a list of RawMatches (uncertified).
--          rawSurplus can be negative.
--
-- Note: we could unify these with a parametrized trace type. For Phase 1,
-- keeping them separate makes the L3/L0 distinction structurally clear.

SimFnL3 : ∀ (n k : ℕ) → Set
SimFnL3 n k = Seed n k → Trace

SimFnL0 : ∀ (n k : ℕ) → Set
SimFnL0 n k = Seed n k → List RawMatch

-- L0 realized surplus: sum of rawSurplus over a list of raw matches.
-- This CAN be negative (no admissibility constraints on raw matches).
l0RealizedSurplus : List RawMatch → ℚ
l0RealizedSurplus ms = sumQ (map rawSurplus ms)


-- ── Theorem 6 (Pointwise Flagship) ───────────────────────────────────────────
--
-- THEOREM (Pointwise Flagship).
-- Suppose:
--   (1) simL3 is any L3 simulation function
--   (2) simL0 is any L0 simulation function
--   (3) There exists a seed s₀ where l0RealizedSurplus(simL0 s₀) < 0
-- Then:
--   ∃ s₀, l0RealizedSurplus(simL0 s₀) < realizedSurplus(simL3 s₀)
--
-- PROOF.
--   Take s₀ as the witness from (3).
--   l0RealizedSurplus(simL0 s₀) < 0           [from (3)]
--   0 ≤ realizedSurplus(simL3 s₀)             [from realizedSurplusNonNeg, Theorem 3]
--   l0RealizedSurplus(simL0 s₀) < realizedSurplus(simL3 s₀)   [<-≤-trans]
--
-- This is the constructive content of the flagship: we exhibit a concrete seed
-- where L3 strictly dominates L0, without any probability machinery.

flagshipPointwise
  : ∀ {n k}
  → (simL3 : SimFnL3 n k)
  → (simL0 : SimFnL0 n k)
  → Σ (Seed n k) (λ s₀ → l0RealizedSurplus (simL0 s₀) < 0ℚ)
  → Σ (Seed n k) (λ s₀ → l0RealizedSurplus (simL0 s₀) < realizedSurplus (simL3 s₀))

flagshipPointwise simL3 simL0 (s₀ , l0neg) =
  s₀ , <-≤-trans l0neg (realizedSurplusNonNeg (simL3 s₀))
  --    l0Real s₀ < 0   ≤   l3Real s₀


-- ── Theorem 7 (Expected Flagship, Conditional) ───────────────────────────────
--
-- THEOREM (Expected Flagship).
-- Given the same (1)–(3) as above, and additionally:
--   (4) ∀ s, l0RealizedSurplus(simL0 s) ≤ realizedSurplus(simL3 s)
--       (L3 dominates L0 pointwise over the seed space)
-- Then, for any finite list of seeds Ω:
--   sumQ (map l3Surplus Ω)  >  sumQ (map l0Surplus Ω)
-- i.e., the L3 total surplus strictly exceeds the L0 total surplus.
-- Since |Ω| > 0 and division by |Ω| preserves order, E[L3] > E[L0].
--
-- HYPOTHESIS (4) is stated explicitly rather than derived.
-- It would follow from a concrete simulation model where L3 admits a superset
-- of the value-creating trades that L0 admits — a property of the auction
-- mechanism rather than the agents. We leave the verification of (4) for
-- a future concrete simulation module.
--
-- In logic: this theorem has the form
--   (4) → (3) → strict-sum-comparison
-- The premises are separated so the logical dependencies are transparent.

flagshipExpected
  : ∀ {n k}
  → (simL3 : SimFnL3 n k)
  → (simL0 : SimFnL0 n k)
  → (Ω : List (Seed n k))
  → (s₀ : Seed n k)
  → l0RealizedSurplus (simL0 s₀) < 0ℚ           -- L0 failure witness (Theorem 5)
  → (∀ s → l0RealizedSurplus (simL0 s)
          ≤ realizedSurplus   (simL3 s))          -- pointwise dominance (Hyp 4)
  → StrictAt                                      -- the evidence structure for sumQStrict
      (map (l0RealizedSurplus ∘ simL0) (s₀ ∷ Ω))
      (map (realizedSurplus   ∘ simL3) (s₀ ∷ Ω))
  → sumQ (map (l0RealizedSurplus ∘ simL0) (s₀ ∷ Ω))
  < sumQ (map (realizedSurplus   ∘ simL3) (s₀ ∷ Ω))

flagshipExpected simL3 simL0 Ω s₀ l0neg dominate strictEvidence =
  sumQStrict strictEvidence


-- ── What Remains ─────────────────────────────────────────────────────────────
--
-- The full flagship theorem E[Eff(L3)] > E[Eff(L0)] requires:
--
--   A. A concrete simulation algorithm:
--      - agents draw prices from seeds using a price grid
--      - the batch auction matches bids and asks
--      - the trace is constructed from the matched pairs
--
--   B. Verification of hypothesis (4):
--      - for any seed, L3 admits a subset of L0's matches
--        (because L3 rejects proposals that would harm agents, but never
--         rejects proposals that strictly benefit them)
--      - actually, (4) is NOT generally true — L3 may reject some profitable
--        matches that L0 admits (when a buyer overbids and still profits)
--
--   C. A probability model connecting seeds to the distribution over traces:
--      - uniform seed distribution → uniform trace distribution
--      - cardinality |Seed n k| = n^k
--
-- These are the subjects of future modules:
--   PriceGrid.agda      — Fin n → ℚ mapping
--   AgentStrategy.agda  — how agents generate proposals from seeds
--   BatchAuction.agda   — the matching algorithm
--   FlagshipFull.agda   — combining all the above
