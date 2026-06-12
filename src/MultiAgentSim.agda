-- MultiAgentSim.agda
-- Extension of the ZIT flagship theorem to markets with k buyer-seller pairs.
--
-- This module adds multi-agent market machinery on top of the existing single-pair
-- results without modifying any existing module.  Every theorem here is an
-- application of an existing lemma from FlagshipFull, L0AgentStrategy, or
-- Stochastic — the extension is purely additive.
--
-- DESIGN.
--   MultiSeed n k  =  Vec (Seed (suc n) 2) k
--     k independent 2-draw seeds, one per buyer-seller pair.
--     The pairs are fully decoupled: pair i's outcome depends only on seed i.
--
--   concreteSimN  : Vec SimEnvironment k → Vec (Seed (suc n) 2) k → Trace
--     Concatenates k single-pair traces.  The output is still a Trace, so
--     realizedSurplusNonNeg from Trace.agda applies immediately —
--     the non-negativity proof is a one-liner.
--
--   realizedSurplusN  / l0RealizedSurplusN  : ... → ℚ
--     Defined by Vec recursion as the sum of k per-pair surpluses.
--     realizedSurplusN-eq connects realizedSurplus (concreteSimN envs ss)
--     to realizedSurplusN envs ss via the trace-splitting lemma realizedSurplus-++.
--
-- CONDITIONS.
--   AllInverted  envs  — every pair has v_b ≤ v_s
--   AllProductive envs — every pair has 0 ≤ v_s, v_s ≤ v_b, cap ≤ maxP
--
-- THEOREMS.
--   concreteSimNNonNeg      — L3 surplus ≥ 0 always (one-liner)
--   realizedSurplus-++      — surplus splits over trace concatenation
--   realizedSurplusN-eq     — concreteSimN surplus equals realizedSurplusN
--   l3FSDom-l0-invertedN    — L3 FSD-dominates L0 in all-inverted markets
--   l0FSDom-l3-productiveN  — L0 FSD-dominates L3 in all-productive markets
--   l3ExpectedN-l0-inverted — E[L3] ≥ E[L0] in all-inverted markets
--   l0ExpectedN-l3-productive — E[L0] ≥ E[L3] in all-productive markets
--
-- Each FSD/expected theorem is an application of FSD-from-pointwise or
-- sumQ-map-mono (Stochastic.agda) to a per-pair pointwise bound lifted by
-- Vec induction.
--
-- EXTENSION STRUCTURE.
--   l0Nonpos-inverted   (L0AgentStrategy) → l0LEL3-invertedN
--   l3LE-l0-productive  (L0AgentStrategy) → l3LEL0-productiveN
--   FSD-from-pointwise  (Stochastic)      → both FSD theorems
--   sumQ-map-mono       (reproved locally) → both expected-value theorems
--   realizedSurplusNonNeg (Trace)         → concreteSimNNonNeg (no reproof)

module MultiAgentSim where

open import Data.Nat      using (ℕ; suc; zero)
open import Data.Rational using (ℚ; _+_; _≤_; 0ℚ; _⊓_)
import Data.Rational.Properties as ℚP
open import Data.List     using (List; []; _∷_; _++_; map)
open import Data.Vec      using (Vec) renaming ([] to v[]; _∷_ to _v∷_)
open import Data.Product  using (_×_; _,_)
open import Function      using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Agent
open import Seed           using (Seed)
open import Institution    using (Match)
open import Surplus        using (surplus)
open import Trace          using ( Trace; Event; TradeSettled
                                  ; OrderSubmitted; OrderRejected; OrderAccepted; AuctionCleared
                                  ; tradesView; sumSurplus
                                  ; realizedSurplus; realizedSurplusNonNeg)
open import SimulationModel using (l0RealizedSurplus)
open import FlagshipFull   using (SimEnvironment; concreteSim)
open import L0AgentStrategy using (concreteL0Sim; l0Nonpos-inverted; l3LE-l0-productive)
open import Probability    using (sumQ)
open import Stochastic     using (FSDom; FSD-from-pointwise)


-- ── Multi-Agent Simulation ────────────────────────────────────────────────────
--
-- concreteSimN envs seeds : Trace
-- The k-pair trace is the concatenation of k single-pair traces.
-- Each pair uses its own independent 2-draw seed from the Vec.
--
-- Why concatenation rather than a separate structure?
-- Because Trace = List Event, concatenation gives a valid Trace,
-- and realizedSurplusNonNeg from Trace.agda applies to ALL traces.
-- The extension is free.

concreteSimN : ∀ {n k} → Vec SimEnvironment k → Vec (Seed (suc n) 2) k → Trace
concreteSimN v[]        v[]        = []
concreteSimN (e v∷ es) (s v∷ ss) = concreteSim e s ++ concreteSimN es ss


-- ── Surplus Sums by Vec Recursion ─────────────────────────────────────────────
--
-- Rather than extracting surplus from the concatenated Trace (which would
-- require trace-splitting lemmas to decompose), we also define the combined
-- surpluses directly by Vec recursion.  realizedSurplusN-eq then proves the
-- two definitions agree.
--
-- This gives a clean proof target for the pointwise bounds:
-- the induction structure of the bound proof matches the Vec recursion.

realizedSurplusN : ∀ {n k} → Vec SimEnvironment k → Vec (Seed (suc n) 2) k → ℚ
realizedSurplusN v[]        v[]        = 0ℚ
realizedSurplusN (e v∷ es) (s v∷ ss) =
  realizedSurplus (concreteSim e s) + realizedSurplusN es ss

l0RealizedSurplusN : ∀ {n k} → Vec SimEnvironment k → Vec (Seed (suc n) 2) k → ℚ
l0RealizedSurplusN v[]        v[]        = 0ℚ
l0RealizedSurplusN (e v∷ es) (s v∷ ss) =
  l0RealizedSurplus (concreteL0Sim e s) + l0RealizedSurplusN es ss


-- ── Non-Negativity (Free) ─────────────────────────────────────────────────────
--
-- THEOREM (concreteSimNNonNeg).
-- The multi-agent L3 trace has non-negative realized surplus at every multi-seed.
--
-- PROOF.
-- concreteSimN envs seeds : Trace.  Apply realizedSurplusNonNeg.  QED.
--
-- This one-line proof shows the extension is structurally clean:
-- the multi-agent trace is still a Trace; no new reasoning is needed.

concreteSimNNonNeg
  : ∀ {n k} (envs : Vec SimEnvironment k) (seeds : Vec (Seed (suc n) 2) k)
  → 0ℚ ≤ realizedSurplus (concreteSimN {n} envs seeds)
concreteSimNNonNeg envs seeds = realizedSurplusNonNeg (concreteSimN envs seeds)


-- ── Trace Splitting Lemmas ─────────────────────────────────────────────────────
--
-- realizedSurplus-++ : realizedSurplus (t1 ++ t2) ≡ realizedSurplus t1 + realizedSurplus t2
--
-- Proved by two private helper lemmas:
--   tradesView-++ : tradesView distributes over ++
--   sumSurplus-++ : sumSurplus distributes over ++ on List Match
--
-- These are the only genuinely new proof content in this module.

private

  -- tradesView distributes over trace concatenation.
  -- Proof by induction on t1, case-splitting on each Event constructor.
  -- The TradeSettled case contributes an element; all other cases are transparent.
  tradesView-++
    : ∀ (t1 t2 : Trace)
    → tradesView (t1 ++ t2) ≡ tradesView t1 ++ tradesView t2
  tradesView-++ []                        t2 = refl
  tradesView-++ (TradeSettled m    ∷ es) t2 = cong (m ∷_) (tradesView-++ es t2)
  tradesView-++ (OrderSubmitted _ _ ∷ es) t2 = tradesView-++ es t2
  tradesView-++ (OrderRejected  _ _ ∷ es) t2 = tradesView-++ es t2
  tradesView-++ (OrderAccepted  _ _ ∷ es) t2 = tradesView-++ es t2
  tradesView-++ (AuctionCleared _   ∷ es) t2 = tradesView-++ es t2

  -- sumSurplus distributes over ++ on List Match.
  -- Proof by induction on ms1.
  --   Base:  sumSurplus [] + sumSurplus ms2 = 0 + sumSurplus ms2 = sumSurplus ms2  ✓
  --   Step:  surplus m + (sumSurplus ms1 + sumSurplus ms2)
  --        = (surplus m + sumSurplus ms1) + sumSurplus ms2  ✓  (by +-assoc)
  sumSurplus-++
    : ∀ (ms1 ms2 : List Match)
    → sumSurplus (ms1 ++ ms2) ≡ sumSurplus ms1 + sumSurplus ms2
  sumSurplus-++ []         ms2 = sym (ℚP.+-identityˡ (sumSurplus ms2))
  sumSurplus-++ (m ∷ ms1) ms2 =
    trans (cong (λ x → surplus m + x) (sumSurplus-++ ms1 ms2))
          (sym (ℚP.+-assoc (surplus m) (sumSurplus ms1) (sumSurplus ms2)))


-- realizedSurplus distributes over trace concatenation.
-- Chains tradesView-++ and sumSurplus-++ via congruence.

realizedSurplus-++
  : ∀ (t1 t2 : Trace)
  → realizedSurplus (t1 ++ t2) ≡ realizedSurplus t1 + realizedSurplus t2
realizedSurplus-++ t1 t2 =
  trans (cong sumSurplus (tradesView-++ t1 t2))
        (sumSurplus-++ (tradesView t1) (tradesView t2))


-- ── Connecting concreteSimN to realizedSurplusN ───────────────────────────────
--
-- LEMMA (realizedSurplusN-eq).
-- The realized surplus of the multi-agent trace equals the Vec-recursive sum.
--
-- Proof by induction on k using realizedSurplus-++.
-- Base: realizedSurplus [] = sumSurplus (tradesView []) = sumSurplus [] = 0ℚ.  ✓
-- Step: realizedSurplus (concreteSim e s ++ concreteSimN es ss)
--     = realizedSurplus (concreteSim e s) + realizedSurplus (concreteSimN es ss)
--     = realizedSurplus (concreteSim e s) + realizedSurplusN es ss   (IH)

realizedSurplusN-eq
  : ∀ {n k} (envs : Vec SimEnvironment k) (seeds : Vec (Seed (suc n) 2) k)
  → realizedSurplus (concreteSimN {n} envs seeds) ≡ realizedSurplusN {n} envs seeds
realizedSurplusN-eq v[]        v[]        = refl
realizedSurplusN-eq (e v∷ es) (s v∷ ss) =
  trans (realizedSurplus-++ (concreteSim e s) (concreteSimN es ss))
        (cong (realizedSurplus (concreteSim e s) +_) (realizedSurplusN-eq es ss))


-- ── Environment Conditions ────────────────────────────────────────────────────
--
-- AllInverted envs : every environment in the Vec has v_b ≤ v_s.
-- AllProductive envs: every environment has 0 ≤ v_s, v_s ≤ v_b, cap ≤ maxP.
--
-- These are inductive predicates on Vec SimEnvironment k, one condition
-- per position in the Vec.  Constructors:
--   ai[] / ap[]   — base case for the empty Vec
--   _ai∷_ / _ap∷_ — inductive step: one condition for the head, predicate for the tail
--
-- AllProductive bundles the three per-environment hypotheses into a single
-- ×-tuple to keep the constructor binary (condition × tail-predicate).

private
  -- Abbreviations for the long field-access expressions.
  vB : SimEnvironment → ℚ
  vB env = ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))

  vS : SimEnvironment → ℚ
  vS env = ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))

  capEnv : SimEnvironment → ℚ
  capEnv env = vB env ⊓ Agent.budget (SimEnvironment.buyer env)

data AllInverted : ∀ {k} → Vec SimEnvironment k → Set where
  ai[]  : AllInverted v[]
  _ai∷_ : ∀ {k} {e : SimEnvironment} {es : Vec SimEnvironment k}
         → vB e ≤ vS e
         → AllInverted es
         → AllInverted (e v∷ es)

data AllProductive : ∀ {k} → Vec SimEnvironment k → Set where
  ap[]  : AllProductive v[]
  _ap∷_ : ∀ {k} {e : SimEnvironment} {es : Vec SimEnvironment k}
         → (0ℚ ≤ vS e  ×  vS e ≤ vB e  ×  capEnv e ≤ SimEnvironment.maxP e)
         → AllProductive es
         → AllProductive (e v∷ es)


-- ── Pointwise Bounds ──────────────────────────────────────────────────────────
--
-- l0LEL3-invertedN: in AllInverted markets, L0 sum ≤ L3 sum.
-- l3LEL0-productiveN: in AllProductive markets, L3 sum ≤ L0 sum.
--
-- Both proved by induction on k, applying +-mono-≤ at each step.
-- The per-pair ingredient comes directly from the single-pair theorems:
--   l0Nonpos-inverted  → L0(s) ≤ 0  →  L0(s) ≤ L3(s) via 0 ≤ L3(s)
--   l3LE-l0-productive → L3(s) ≤ L0(s)

private

  l0LEL3-invertedN
    : ∀ {n k} (envs : Vec SimEnvironment k) (seeds : Vec (Seed (suc n) 2) k)
    → AllInverted envs
    → l0RealizedSurplusN {n} envs seeds ≤ realizedSurplusN {n} envs seeds
  l0LEL3-invertedN v[]        v[]        ai[]        = ℚP.≤-refl
  l0LEL3-invertedN (e v∷ es) (s v∷ ss) (h ai∷ hs)  =
    ℚP.+-mono-≤
      (ℚP.≤-trans
        (l0Nonpos-inverted e s h)
        (realizedSurplusNonNeg (concreteSim e s)))
      (l0LEL3-invertedN es ss hs)

  l3LEL0-productiveN
    : ∀ {n k} (envs : Vec SimEnvironment k) (seeds : Vec (Seed (suc n) 2) k)
    → AllProductive envs
    → realizedSurplusN {n} envs seeds ≤ l0RealizedSurplusN {n} envs seeds
  l3LEL0-productiveN v[]        v[]        ap[]                       = ℚP.≤-refl
  l3LEL0-productiveN (e v∷ es) (s v∷ ss) ((hVS , hProd , hCap) ap∷ hs) =
    ℚP.+-mono-≤
      (l3LE-l0-productive e s hVS hProd hCap)
      (l3LEL0-productiveN es ss hs)


-- ── Main FSD Theorems ─────────────────────────────────────────────────────────

-- THEOREM (l3FSDom-l0-invertedN).
-- In a k-pair inverted market (AllInverted), the combined L3 surplus
-- first-order stochastically dominates the combined L0 surplus.
--
-- PROOF.
-- By FSD-from-pointwise it suffices to show pointwise dominance over multi-seeds:
--   ∀ ss, l0RealizedSurplusN envs ss ≤ realizedSurplusN envs ss
-- This is l0LEL3-invertedN, proved by Vec induction above.
--
-- RELATIONSHIP TO SINGLE-PAIR RESULT.
-- The k=1 case recovers l3FSDom-l0-inverted from Stochastic.agda exactly.
-- For k > 1, the combined surplus is the sum of k independent pair surpluses;
-- since each satisfies the pointwise bound, so does the sum.

l3FSDom-l0-invertedN
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → AllInverted envs
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → FSDom (realizedSurplusN {n} envs) (l0RealizedSurplusN {n} envs) Ω
l3FSDom-l0-invertedN {n} envs hinv Ω =
  FSD-from-pointwise _ _ Ω
    (λ seeds → l0LEL3-invertedN envs seeds hinv)


-- THEOREM (l0FSDom-l3-productiveN).
-- In a k-pair productive market (AllProductive), the combined L0 surplus
-- first-order stochastically dominates the combined L3 surplus.
--
-- PROOF.
-- By FSD-from-pointwise and l3LEL0-productiveN.
--
-- ECONOMIC INTERPRETATION.
-- In productive markets (v_b > v_s), L3's constraints suppress k-fold:
-- every pair where L3 fails to trade but L0 would trade contributes a deficit.
-- The FSD result holds regardless of how many pairs there are.

l0FSDom-l3-productiveN
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → AllProductive envs
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → FSDom (l0RealizedSurplusN {n} envs) (realizedSurplusN {n} envs) Ω
l0FSDom-l3-productiveN {n} envs hprod Ω =
  FSD-from-pointwise _ _ Ω
    (λ seeds → l3LEL0-productiveN envs seeds hprod)


-- ── Expected Value Theorems ───────────────────────────────────────────────────
--
-- These are the multi-agent counterparts of l3Expected-l0-inverted and its
-- productive-market symmetric in Stochastic.agda.
--
-- LEMMA (sumQ-map-mono).
-- If g(s) ≤ f(s) for every s, then sumQ (map g Ω) ≤ sumQ (map f Ω).
-- This lemma is private in Stochastic.agda; we reprove it here.
-- The proof is the same: induction on Ω, applying +-mono-≤ at each step.

private
  sumQ-map-mono
    : {S : Set} (f g : S → ℚ) (xs : List S)
    → (∀ s → g s ≤ f s)
    → sumQ (map g xs) ≤ sumQ (map f xs)
  sumQ-map-mono f g []       _  = ℚP.≤-refl
  sumQ-map-mono f g (x ∷ xs) pw =
    ℚP.+-mono-≤ (pw x) (sumQ-map-mono f g xs pw)


-- THEOREM (l3ExpectedN-l0-inverted).
-- In a k-pair inverted market (AllInverted), the total L3 surplus over any
-- seed population Ω is at least the total L0 surplus:
--
--   Σ_{ss ∈ Ω}  l0RealizedSurplusN envs ss
--     ≤  Σ_{ss ∈ Ω}  realizedSurplusN envs ss
--
-- Dividing both sides by |Ω| gives E[L3] ≥ E[L0].
--
-- PROOF.
-- By sumQ-map-mono applied to the pointwise bound l0LEL3-invertedN.
-- The argument is identical to l3Expected-l0-inverted in Stochastic.agda,
-- with the single-pair surplus functions replaced by their k-pair sums.

l3ExpectedN-l0-inverted
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → AllInverted envs
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → sumQ (map (l0RealizedSurplusN {n} envs) Ω)
    ≤ sumQ (map (realizedSurplusN   {n} envs) Ω)
l3ExpectedN-l0-inverted {n} envs hinv Ω =
  sumQ-map-mono _ _ Ω
    (λ seeds → l0LEL3-invertedN envs seeds hinv)


-- THEOREM (l0ExpectedN-l3-productive).
-- In a k-pair productive market (AllProductive), the total L0 surplus is at
-- least the total L3 surplus:
--
--   Σ_{ss ∈ Ω}  realizedSurplusN envs ss
--     ≤  Σ_{ss ∈ Ω}  l0RealizedSurplusN envs ss

l0ExpectedN-l3-productive
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → AllProductive envs
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → sumQ (map (realizedSurplusN   {n} envs) Ω)
    ≤ sumQ (map (l0RealizedSurplusN {n} envs) Ω)
l0ExpectedN-l3-productive {n} envs hprod Ω =
  sumQ-map-mono _ _ Ω
    (λ seeds → l3LEL0-productiveN envs seeds hprod)


-- ── Trace-Based Corollary ──────────────────────────────────────────────────────
--
-- The FSD theorem can equivalently be stated with  realizedSurplus ∘ concreteSimN
-- (the natural Trace-based surplus) in place of realizedSurplusN.
-- The two are equal by realizedSurplusN-eq; this corollary makes the connection
-- explicit.

l3FSDom-l0-invertedN-trace
  : ∀ {n k} (envs : Vec SimEnvironment k)
  → AllInverted envs
  → (Ω : List (Vec (Seed (suc n) 2) k))
  → FSDom (realizedSurplus ∘ concreteSimN {n} envs)
          (l0RealizedSurplusN {n} envs)
          Ω
l3FSDom-l0-invertedN-trace {n} envs hinv Ω =
  FSD-from-pointwise _ _ Ω
    (λ seeds →
      ℚP.≤-trans
        (l0LEL3-invertedN envs seeds hinv)
        (ℚP.≤-reflexive (sym (realizedSurplusN-eq envs seeds))))
