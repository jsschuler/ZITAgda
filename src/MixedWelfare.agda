-- MixedWelfare.agda
-- Oracle-mix welfare for markets with both productive and inverted pairs.
--
-- In a market with k buyer-seller pairs, each pair is either:
--   Inverted  (v_b ≤ v_s): trades destroy value; L3 prevents them; L0 does not.
--   Productive (v_s ≤ v_b): trades create value; L0 executes more; L3 fewer.
--
-- The "oracle mix" strategy runs L3 on inverted pairs and L0 on productive pairs.
-- It is the welfare-optimal agent assignment: it avoids bad trades and executes
-- all good ones.
--
-- MAIN RESULTS.
--
--   mixFSDom-l3:
--     FSDom (concreteMixSurplusN envs hmix) (realizedSurplusN envs) Ω
--     — oracle mix FSD-dominates pure L3.
--
--   mixFSDom-l0:
--     FSDom (concreteMixSurplusN envs hmix) (l0RealizedSurplusN envs) Ω
--     — oracle mix FSD-dominates pure L0.
--
-- PROOF STRUCTURE.
-- The pointwise bounds follow by induction on Mixed:
--   invMix case: L3 used for both mix and L3-only; heads are equal (≤-refl).
--                L0-only head: l0(s) ≤ 0 ≤ L3(s) via l0Nonpos-inverted.
--   prodMix case: mix uses L0; L3-only head: L3(s) ≤ L0(s) via l3LE-l0-productive.
--                 L0-only head: equal (≤-refl).
--
-- SPECIAL CASES.
--   All invMix  → concreteMixSurplusN = realizedSurplusN
--                 mixFSDom-l0 recovers l3FSDom-l0-invertedN (MultiAgentSim)
--   All prodMix → concreteMixSurplusN = l0RealizedSurplusN
--                 mixFSDom-l3 recovers l0FSDom-l3-productiveN (MultiAgentSim)
--
-- This module therefore strictly generalises the two AllInverted/AllProductive
-- FSD results from MultiAgentSim.agda.

module MixedWelfare where

open import Data.Nat      using (ℕ; suc)
open import Data.List     using (List; []; _∷_; map)
open import Data.Vec      using (Vec) renaming ([] to v[]; _∷_ to _v∷_)
open import Data.Rational using (ℚ; _≤_; _+_; 0ℚ; _⊓_)
open import Data.Product  using (_×_; proj₁; proj₂)
import Data.Rational.Properties as ℚP

open import Agent
open import Seed            using (Seed)
open import Trace           using (realizedSurplus; realizedSurplusNonNeg)
open import SimulationModel using (l0RealizedSurplus)
open import FlagshipFull    using (SimEnvironment; concreteSim)
open import L0AgentStrategy using (concreteL0Sim; l0Nonpos-inverted; l3LE-l0-productive)
open import Probability     using (sumQ)
open import Stochastic      using (FSDom; FSD-from-pointwise)
open import MultiAgentSim   using (realizedSurplusN; l0RealizedSurplusN)


-- ── Local Abbreviations ───────────────────────────────────────────────────────

private
  vB : SimEnvironment → ℚ
  vB env = ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))

  vS : SimEnvironment → ℚ
  vS env = ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))

  capEnv : SimEnvironment → ℚ
  capEnv env = vB env ⊓ Agent.budget (SimEnvironment.buyer env)


-- ── Mixed Predicate ───────────────────────────────────────────────────────────
--
-- Mixed envs classifies each environment in the Vec as either Inverted
-- (v_b ≤ v_s) or Productive (0 ≤ v_s, v_s ≤ v_b, cap ≤ maxP).
--
-- The two constructors carry exactly the conditions needed to invoke
-- l0Nonpos-inverted and l3LE-l0-productive respectively.
--
-- AllInverted envs  ≅  Mixed envs with all invMix constructors
-- AllProductive envs ≅  Mixed envs with all prodMix constructors

data Mixed : ∀ {k} → Vec SimEnvironment k → Set where
  mix[]   : Mixed v[]
  invMix  : ∀ {k} {e : SimEnvironment} {es : Vec SimEnvironment k}
           → vB e ≤ vS e
           → Mixed es
           → Mixed (e v∷ es)
  prodMix : ∀ {k} {e : SimEnvironment} {es : Vec SimEnvironment k}
           → (0ℚ ≤ vS e  ×  vS e ≤ vB e  ×  capEnv e ≤ SimEnvironment.maxP e)
           → Mixed es
           → Mixed (e v∷ es)


-- ── Oracle Mix Simulation ─────────────────────────────────────────────────────
--
-- concreteMixSurplusN envs hmix ss:
--   For each pair, runs L3 if the environment is inverted, L0 if productive.
--   Dispatches on the Mixed proof hmix — the same proof that certifies
--   the welfare-optimality of the choice.
--
-- This is a total function by structural recursion on Mixed.

concreteMixSurplusN
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → Mixed envs
  → Vec (Seed (suc n) 2) k → ℚ
concreteMixSurplusN v[]        mix[]            v[]        = 0ℚ
concreteMixSurplusN (e v∷ es) (invMix  _ hmix) (s v∷ ss) =
  realizedSurplus (concreteSim e s) + concreteMixSurplusN es hmix ss
concreteMixSurplusN (e v∷ es) (prodMix _ hmix) (s v∷ ss) =
  l0RealizedSurplus (concreteL0Sim e s) + concreteMixSurplusN es hmix ss


-- ── Private Pointwise Bounds ──────────────────────────────────────────────────

private

  -- LEMMA (l3LE-mix).
  -- Oracle mix surplus ≥ pure L3 surplus, pointwise.
  --
  -- PROOF by induction on Mixed:
  --   invMix  case: mix head = L3 head (equal); ≤-refl + induction.
  --   prodMix case: mix head = L0 head ≥ L3 head [l3LE-l0-productive] + induction.

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
  -- Oracle mix surplus ≥ pure L0 surplus, pointwise.
  --
  -- PROOF by induction on Mixed:
  --   invMix  case: mix head = L3 head ≥ 0 ≥ L0 head [l0Nonpos-inverted] + induction.
  --   prodMix case: mix head = L0 head (equal); ≤-refl + induction.

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

-- THEOREM (mixFSDom-l3).
-- The oracle mix FSD-dominates pure L3:
--
--   FSDom (concreteMixSurplusN envs hmix) (realizedSurplusN envs) Ω
--
-- PROOF. FSD-from-pointwise + l3LE-mix. ✓
--
-- SPECIAL CASE: all invMix → concreteMixSurplusN = realizedSurplusN → trivial FSD.
--               all prodMix → recovers l0FSDom-l3-productiveN from MultiAgentSim.

mixFSDom-l3
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → (hmix : Mixed envs)
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → FSDom (concreteMixSurplusN {n} envs hmix)
          (realizedSurplusN {n} envs)
          Ω
mixFSDom-l3 {n} envs hmix Ω =
  FSD-from-pointwise _ _ Ω (λ ss → l3LE-mix {n} envs hmix ss)


-- THEOREM (mixFSDom-l0).
-- The oracle mix FSD-dominates pure L0:
--
--   FSDom (concreteMixSurplusN envs hmix) (l0RealizedSurplusN envs) Ω
--
-- PROOF. FSD-from-pointwise + l0LE-mix. ✓
--
-- SPECIAL CASE: all prodMix → concreteMixSurplusN = l0RealizedSurplusN → trivial FSD.
--               all invMix  → recovers l3FSDom-l0-invertedN from MultiAgentSim.
--
-- ECONOMIC INTERPRETATION.
-- In any mixed market, the oracle mix is welfare-optimal: it avoids
-- value-destroying trades (L3 for inverted) and captures all value-creating
-- trades (L0 for productive).  Both pure strategies leave welfare on the table:
-- pure L3 misses productive trades; pure L0 executes destructive ones.

mixFSDom-l0
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → (hmix : Mixed envs)
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → FSDom (concreteMixSurplusN {n} envs hmix)
          (l0RealizedSurplusN {n} envs)
          Ω
mixFSDom-l0 {n} envs hmix Ω =
  FSD-from-pointwise _ _ Ω (λ ss → l0LE-mix {n} envs hmix ss)


-- ── Expected Welfare Corollaries ──────────────────────────────────────────────

-- COROLLARY (mixExpected-l3).
-- E[oracle mix welfare] ≥ E[L3 welfare] under any Mixed conditions.

mixExpected-l3
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → (hmix : Mixed envs)
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → sumQ (map (realizedSurplusN {n} envs) Ω)
    ≤ sumQ (map (concreteMixSurplusN {n} envs hmix) Ω)
mixExpected-l3 {n} envs hmix Ω =
  sumQ-map-mono _ _ Ω (λ ss → l3LE-mix {n} envs hmix ss)


-- COROLLARY (mixExpected-l0).
-- E[oracle mix welfare] ≥ E[L0 welfare] under any Mixed conditions.

mixExpected-l0
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → (hmix : Mixed envs)
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → sumQ (map (l0RealizedSurplusN {n} envs) Ω)
    ≤ sumQ (map (concreteMixSurplusN {n} envs hmix) Ω)
mixExpected-l0 {n} envs hmix Ω =
  sumQ-map-mono _ _ Ω (λ ss → l0LE-mix {n} envs hmix ss)
