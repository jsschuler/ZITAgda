-- MultiAgentEffFSD.agda
-- Efficiency ratio FSD for k buyer-seller pairs, extending both
-- MultiAgentSim.agda (raw-surplus k-pair FSD) and EfficiencyFSD.agda
-- (single-pair efficiency FSD) to the k-pair efficiency metric.
--
-- The efficiency ratio for a portfolio of k pairs:
--
--   concreteL3EffN envs ps mfs>0 ss = realizedSurplusN envs ss  ÷ mfs
--   concreteL0EffN envs ps mfs>0 ss = l0RealizedSurplusN envs ss ÷ mfs
--
-- where mfs = maxFeasibleSurplus ps > 0 (shared denominator).
--
-- Main theorems:
--
--   INVERTED  (AllInverted envs, mfs > 0):
--     l3EffFSDom-l0-invertedN  — L3 portfolio efficiency FSD-dominates L0
--
--   PRODUCTIVE (AllProductive envs, mfs > 0):
--     l0EffFSDom-l3-productiveN — L0 portfolio efficiency FSD-dominates L3
--
-- Plus expected-efficiency corollaries in both directions.
--
-- PROOF STRUCTURE.
-- Each theorem follows the same three-step pattern as EfficiencyFSD.agda:
--   1. Reproduce the pointwise raw-surplus bound for k pairs
--      (l0LEL3-invertedN or l3LEL0-productiveN, private in MultiAgentSim;
--      reproved locally by identical Vec induction).
--   2. Lift to efficiency ratios via *-monoʳ-≤-nonNeg (1/ mfs), providing
--      the instance chain (>-nonZero, positive, 1/pos⇒pos, pos⇒nonNeg)
--      in each where-block.  a ÷ mfs = a * (1/ mfs) definitionally.
--   3. Apply FSD-from-pointwise (Stochastic.agda).
--
-- Zero changes to any existing module.  The k=1 case recovers the
-- single-pair results from EfficiencyFSD.agda.

module MultiAgentEffFSD where

open import Data.Nat      using (ℕ; suc)
open import Data.List     using (List; []; _∷_; map)
open import Data.Vec      using (Vec) renaming ([] to v[]; _∷_ to _v∷_)
open import Data.Rational using (ℚ; _≤_; _<_; 0ℚ; _÷_; 1/_; _⊓_)
open import Data.Rational using (NonNegative; NonZero; Positive
                                ; positive; >-nonZero)
open import Data.Product  using (proj₁; proj₂)
import Data.Rational.Properties as ℚP
open import Data.Rational.Properties using (pos⇒nonNeg; 1/pos⇒pos)

open import Agent
open import Seed            using (Seed)
open import FlagshipFull    using (SimEnvironment; concreteSim)
open import SimulationModel using (l0RealizedSurplus)
open import Trace           using (realizedSurplus; realizedSurplusNonNeg)
open import L0AgentStrategy using (concreteL0Sim; l0Nonpos-inverted; l3LE-l0-productive)
open import Efficiency      using (ProfitablePair; maxFeasibleSurplus)
open import Probability     using (sumQ)
open import Stochastic      using (FSDom; FSD-from-pointwise)
open import MultiAgentSim   using ( realizedSurplusN; l0RealizedSurplusN
                                  ; AllInverted; ai[]; _ai∷_
                                  ; AllProductive; ap[]; _ap∷_)


-- ── Local Abbreviations ───────────────────────────────────────────────────────
-- Mirror the private abbreviations from MultiAgentSim for use in constructor
-- pattern matches and theorem signatures.

private
  vB : SimEnvironment → ℚ
  vB env = ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))

  vS : SimEnvironment → ℚ
  vS env = ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))

  capEnv : SimEnvironment → ℚ
  capEnv env = vB env ⊓ Agent.budget (SimEnvironment.buyer env)


-- ── Concrete Portfolio Efficiency Functions ───────────────────────────────────
--
-- concreteL3EffN envs ps mfs>0 ss
--   = sum of k L3 realized surpluses, divided by mfs
-- concreteL0EffN envs ps mfs>0 ss
--   = sum of k L0 realized surpluses, divided by mfs
--
-- Both are functions Vec (Seed (suc n) 2) k → ℚ, the type required by FSDom.

concreteL3EffN
  : ∀ {n k} (envs : Vec SimEnvironment k) (ps : List ProfitablePair)
  → 0ℚ < maxFeasibleSurplus ps
  → Vec (Seed (suc n) 2) k → ℚ
concreteL3EffN {n} envs ps mfs>0 ss = realizedSurplusN {n} envs ss ÷ maxFeasibleSurplus ps
  where instance _ = >-nonZero mfs>0

concreteL0EffN
  : ∀ {n k} (envs : Vec SimEnvironment k) (ps : List ProfitablePair)
  → 0ℚ < maxFeasibleSurplus ps
  → Vec (Seed (suc n) 2) k → ℚ
concreteL0EffN {n} envs ps mfs>0 ss = l0RealizedSurplusN {n} envs ss ÷ maxFeasibleSurplus ps
  where instance _ = >-nonZero mfs>0


-- ── Private Helpers ───────────────────────────────────────────────────────────

private

  -- LEMMA (l0LEL3-invertedN).
  -- In AllInverted markets, L0 portfolio surplus ≤ L3 portfolio surplus.
  -- Reproved from the private version in MultiAgentSim.agda by identical
  -- Vec induction.

  l0LEL3-invertedN
    : ∀ {n k} (envs : Vec SimEnvironment k) (ss : Vec (Seed (suc n) 2) k)
    → AllInverted envs
    → l0RealizedSurplusN {n} envs ss ≤ realizedSurplusN {n} envs ss
  l0LEL3-invertedN v[]        v[]        ai[]       = ℚP.≤-refl
  l0LEL3-invertedN (e v∷ es) (s v∷ ss) (h ai∷ hs) =
    ℚP.+-mono-≤
      (ℚP.≤-trans
        (l0Nonpos-inverted e s h)
        (realizedSurplusNonNeg (concreteSim e s)))
      (l0LEL3-invertedN es ss hs)

  -- LEMMA (l3LEL0-productiveN).
  -- In AllProductive markets, L3 portfolio surplus ≤ L0 portfolio surplus.
  -- Reproved from the private version in MultiAgentSim.agda.

  l3LEL0-productiveN
    : ∀ {n k} (envs : Vec SimEnvironment k) (ss : Vec (Seed (suc n) 2) k)
    → AllProductive envs
    → realizedSurplusN {n} envs ss ≤ l0RealizedSurplusN {n} envs ss
  l3LEL0-productiveN v[]        v[]        ap[]          = ℚP.≤-refl
  l3LEL0-productiveN (e v∷ es) (s v∷ ss) (hconds ap∷ hs) =
    ℚP.+-mono-≤
      (l3LE-l0-productive e s (proj₁ hconds) (proj₁ (proj₂ hconds)) (proj₂ (proj₂ hconds)))
      (l3LEL0-productiveN es ss hs)

  -- LEMMA (sumQ-map-mono).
  -- If g(ss) ≤ f(ss) for every multi-seed ss, then sumQ (map g Ω) ≤ sumQ (map f Ω).
  -- Reproved locally (private in Stochastic.agda and EfficiencyFSD.agda).

  sumQ-map-mono
    : {S : Set} (f g : S → ℚ) (xs : List S)
    → (∀ s → g s ≤ f s)
    → sumQ (map g xs) ≤ sumQ (map f xs)
  sumQ-map-mono f g []       _  = ℚP.≤-refl
  sumQ-map-mono f g (x ∷ xs) pw =
    ℚP.+-mono-≤ (pw x) (sumQ-map-mono f g xs pw)


-- ── FSD Theorems ──────────────────────────────────────────────────────────────

-- THEOREM (l3EffFSDom-l0-invertedN).
-- In a k-pair inverted market (AllInverted envs) with positive mfs, L3's
-- portfolio efficiency distribution first-order stochastically dominates L0's:
--
--   FSDom (concreteL3EffN envs ps mfs>0) (concreteL0EffN envs ps mfs>0) Ω
--
-- PROOF.
-- By FSD-from-pointwise.  Pointwise bound:
--   l0EffN(ss) ≤ l3EffN(ss)
-- i.e., l0SumN(ss) * (1/mfs) ≤ l3SumN(ss) * (1/mfs).
-- Follows from l0LEL3-invertedN by *-monoʳ-≤-nonNeg (1/ mfs). ✓

l3EffFSDom-l0-invertedN
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → AllInverted envs
  → (ps : List ProfitablePair)
  → (mfs>0 : 0ℚ < maxFeasibleSurplus ps)
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → FSDom (concreteL3EffN {n} envs ps mfs>0)
          (concreteL0EffN {n} envs ps mfs>0)
          Ω
l3EffFSDom-l0-invertedN {n} envs hinv ps mfs>0 Ω =
  FSD-from-pointwise _ _ Ω
    (λ ss → ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (l0LEL3-invertedN {n} envs ss hinv))
  where
    mfs = maxFeasibleSurplus ps
    instance
      _   = >-nonZero mfs>0
      pc  : Positive mfs;          pc  = positive mfs>0
      p1c : Positive (1/ mfs);     p1c = 1/pos⇒pos mfs
      n1c : NonNegative (1/ mfs);  n1c = pos⇒nonNeg (1/ mfs)


-- THEOREM (l0EffFSDom-l3-productiveN).
-- In a k-pair productive market (AllProductive envs) with positive mfs, L0's
-- portfolio efficiency distribution first-order stochastically dominates L3's:
--
--   FSDom (concreteL0EffN envs ps mfs>0) (concreteL3EffN envs ps mfs>0) Ω
--
-- PROOF.
-- By FSD-from-pointwise and l3LEL0-productiveN, lifted by *-monoʳ-≤-nonNeg. ✓
--
-- GODE & SUNDER CONNECTION.
-- The portfolio version of G&S's headline efficiency result: even with k pairs,
-- unconstrained ZIT agents collectively achieve higher (in FSD sense) efficiency
-- than constrained agents in productive markets.

l0EffFSDom-l3-productiveN
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → AllProductive envs
  → (ps : List ProfitablePair)
  → (mfs>0 : 0ℚ < maxFeasibleSurplus ps)
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → FSDom (concreteL0EffN {n} envs ps mfs>0)
          (concreteL3EffN {n} envs ps mfs>0)
          Ω
l0EffFSDom-l3-productiveN {n} envs hprod ps mfs>0 Ω =
  FSD-from-pointwise _ _ Ω
    (λ ss → ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (l3LEL0-productiveN {n} envs ss hprod))
  where
    mfs = maxFeasibleSurplus ps
    instance
      _   = >-nonZero mfs>0
      pc  : Positive mfs;          pc  = positive mfs>0
      p1c : Positive (1/ mfs);     p1c = 1/pos⇒pos mfs
      n1c : NonNegative (1/ mfs);  n1c = pos⇒nonNeg (1/ mfs)


-- ── Expected Efficiency Corollaries ──────────────────────────────────────────

-- COROLLARY (l3EffExpectedN-l0-inverted).
-- E[L3 portfolio efficiency] ≥ E[L0 portfolio efficiency] in AllInverted markets.

l3EffExpectedN-l0-inverted
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → AllInverted envs
  → (ps : List ProfitablePair)
  → (mfs>0 : 0ℚ < maxFeasibleSurplus ps)
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → sumQ (map (concreteL0EffN {n} envs ps mfs>0) Ω)
    ≤ sumQ (map (concreteL3EffN {n} envs ps mfs>0) Ω)
l3EffExpectedN-l0-inverted {n} envs hinv ps mfs>0 Ω =
  sumQ-map-mono _ _ Ω
    (λ ss → ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (l0LEL3-invertedN {n} envs ss hinv))
  where
    mfs = maxFeasibleSurplus ps
    instance
      _   = >-nonZero mfs>0
      pc  : Positive mfs;          pc  = positive mfs>0
      p1c : Positive (1/ mfs);     p1c = 1/pos⇒pos mfs
      n1c : NonNegative (1/ mfs);  n1c = pos⇒nonNeg (1/ mfs)


-- COROLLARY (l0EffExpectedN-l3-productive).
-- E[L0 portfolio efficiency] ≥ E[L3 portfolio efficiency] in AllProductive markets.

l0EffExpectedN-l3-productive
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → AllProductive envs
  → (ps : List ProfitablePair)
  → (mfs>0 : 0ℚ < maxFeasibleSurplus ps)
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → sumQ (map (concreteL3EffN {n} envs ps mfs>0) Ω)
    ≤ sumQ (map (concreteL0EffN {n} envs ps mfs>0) Ω)
l0EffExpectedN-l3-productive {n} envs hprod ps mfs>0 Ω =
  sumQ-map-mono _ _ Ω
    (λ ss → ℚP.*-monoʳ-≤-nonNeg (1/ mfs) (l3LEL0-productiveN {n} envs ss hprod))
  where
    mfs = maxFeasibleSurplus ps
    instance
      _   = >-nonZero mfs>0
      pc  : Positive mfs;          pc  = positive mfs>0
      p1c : Positive (1/ mfs);     p1c = 1/pos⇒pos mfs
      n1c : NonNegative (1/ mfs);  n1c = pos⇒nonNeg (1/ mfs)
