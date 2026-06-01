-- FlagshipFull.agda
-- Connects the concrete ZIT simulation to the abstract flagship theorems.
--
-- This module assembles all Phase 1 pieces:
--   PriceGrid     → tick functions (seed index → price)
--   AgentStrategy → certified proposals (price + L3 proof)
--   BatchAuction  → matching algorithm (certified proposals → Match list)
--   Trace         → event log (Match list → Trace)
--   SimulationModel → abstract flagship theorems (SimFnL3 → surplus comparison)
--
-- RESULT: The concrete L3 simulation function satisfies SimFnL3 (its TYPE says so).
-- All abstract theorems from SimulationModel.agda apply to it automatically.
-- In particular, realizedSurplusNonNeg holds for every output trace.
--
-- WHAT REMAINS (Phase 2):
--   - A concrete L0 simulation with negative surplus witnesses
--   - Proof of pointwise dominance (∀ s, l0Surplus(s) ≤ l3Surplus(s))
--   - The expected theorem E[Eff(L3)] > E[Eff(L0)] over the full seed space
--
-- New Agda ideas:
--   module parameters  — parametrize an entire module by values
--   open module record — dot-access to record fields made into module names
--   λ s → body        — anonymous function (lambda abstraction)
module FlagshipFull where

open import Data.Nat      using (ℕ; suc; zero) renaming (_<_ to _<ℕ_)
open import Data.Fin      using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Rational using (ℚ; _≤_; _<_; _⊓_; 0ℚ)
open import Data.List     using (List; []; _∷_; map)
open import Data.Product  using (Σ; _,_)

open import Agent
open import Proposal
open import Institution   using (Match)
open import Trace         using (Trace; Event; TradeSettled; realizedSurplus;
                                  realizedSurplusNonNeg)
open import Seed          using (Seed; drawAt)
open import AgentStrategy using (CertifiedBid; CertifiedAsk;
                                  makeBuyerBid; makeSellerAsk)
open import BatchAuction  using (BidEntry; AskEntry; matchZip)
open import SimulationModel using (SimFnL3)


-- ── Simulation Environment ────────────────────────────────────────────────────
--
-- A SimEnvironment bundles the market parameters needed to run one episode:
--   buyer  : a buyer agent with valuation and budget
--   seller : a seller agent with valuation and inventory
--   maxP   : the maximum possible price (upper bound for seller asks)
--
-- The proof fields are preconditions:
--   cap≥0 : the buyer's effective cap (min(v,b)) is non-negative.
--            In a well-formed market, all valuations and budgets are ≥ 0.
--   v≤maxP : the seller's reservation price does not exceed the market maximum.
--            Required by sellerTick to produce a well-defined offset grid.
--   hasInv : the seller holds at least one unit.
--            Required by SellerAdmissible.hasInventory.
--
-- Agda modules can be parametrized — see the comment in SimulationModel.agda.
-- Here we use a record instead, which keeps all parameters first-class.

record SimEnvironment : Set where
  field
    buyer   : Agent
    seller  : Agent
    maxP    : ℚ
    cap≥0   : 0ℚ ≤  ValuationSchedule.unitValue (Agent.valuation buyer)
                  ⊓ Agent.budget buyer
    v≤maxP  : ValuationSchedule.unitValue (Agent.valuation seller) ≤ maxP
    hasInv  : zero <ℕ Agent.inventory seller


-- ── One-Episode Matching ──────────────────────────────────────────────────────
--
-- Given a seed with 2 draws (one for the buyer, one for the seller),
-- generate certified proposals and run the batch auction.
--
-- Seed (suc n) 2 = Vec (Fin (suc n)) 2
--   two elements, each an index into the (suc n)-point price grid.
--
-- draw 0  → buyer's bid index  → makeBuyerBid  → CertifiedBid
-- draw 1  → seller's ask index → makeSellerAsk → CertifiedAsk
--
-- matchZip [ bid ] [ ask ] : List Match
--   produces at most one Match (the pair crosses, or not).

runMatches : ∀ {n} → SimEnvironment → Seed (suc n) 2 → List Match
runMatches {n} env s = matchZip bids asks
  where
    open SimEnvironment env

    i_b : Fin (suc n)
    i_b = drawAt s fzero              -- buyer's price draw

    i_s : Fin (suc n)
    i_s = drawAt s (fsuc fzero)       -- seller's price draw

    bidEntry : BidEntry
    bidEntry = buyer , makeBuyerBid n buyer i_b cap≥0

    askEntry : AskEntry
    askEntry = seller , makeSellerAsk n seller maxP i_s v≤maxP hasInv

    bids : List BidEntry
    bids = bidEntry ∷ []

    asks : List AskEntry
    asks = askEntry ∷ []


-- ── Convert Matches to Trace ──────────────────────────────────────────────────
--
-- Each Match m is wrapped in TradeSettled m to form an Event.
-- The Trace is just a list of Events.
--
-- This is a certified trace: every TradeSettled event carries a Match,
-- which carries BuyerAdmissible and SellerAdmissible evidence.
-- The type system enforces this — no uncertified trade can appear in the Trace.

matchesToTrace : List Match → Trace
matchesToTrace ms = map TradeSettled ms


-- ── Concrete L3 Simulation Function ──────────────────────────────────────────
--
-- concreteSim env : SimFnL3 (suc n) 2
--
-- SimFnL3 (suc n) 2 = Seed (suc n) 2 → Trace  [from SimulationModel.agda]
--
-- concreteSim env is a FUNCTION from seeds to traces,
-- which is exactly the type required by the abstract flagship theorems.
-- The abstract theorems take ANY SimFnL3 — they apply to our concrete one.
--
-- In Julia: this would be a function closure over the environment.
-- In Agda: the type PROVES it satisfies the interface.

concreteSim : ∀ {n} → SimEnvironment → SimFnL3 (suc n) 2
concreteSim env = λ s → matchesToTrace (runMatches env s)


-- ── Theorem: Every Trace has Non-Negative Surplus ────────────────────────────
--
-- THEOREM (Concrete L3 Surplus).
-- For any environment env and seed s,
--   0 ≤ realizedSurplus (concreteSim env s)
--
-- PROOF.
--   concreteSim env s is a Trace.
--   realizedSurplusNonNeg applies to ALL traces (Theorem 3 from Trace.agda).
--   QED.
--
-- This is the culmination of the structural chain:
--   L3Constraint → BuyerAdmissible + SellerAdmissible
--   → valuationChain (v_seller ≤ v_buyer)
--   → surplusNonNeg (0 ≤ v_buyer - v_seller)
--   → sumSurplusNonNeg (0 ≤ Σ surplus)
--   → realizedSurplusNonNeg (0 ≤ realizedSurplus)
--
-- Every step uses certified evidence — no uncertified match can enter the trace.

concreteSimSurplusNonNeg
  : ∀ {n} (env : SimEnvironment) (s : Seed (suc n) 2)
  → 0ℚ ≤ realizedSurplus (concreteSim env s)
concreteSimSurplusNonNeg env s = realizedSurplusNonNeg (concreteSim env s)


-- ── Application of Abstract Flagship ─────────────────────────────────────────
--
-- flagshipPointwise (from SimulationModel.agda) says:
--   given ANY SimFnL3 and ANY SimFnL0, if there exists a seed where
--   L0 surplus < 0, then there exists a seed where L3 surplus > L0 surplus.
--
-- We apply it to our concrete simulation.
-- The L0 simulation is left abstract — the theorem holds for ANY such function.
-- This models the assumption that L0 ZIT agents CAN produce negative-surplus trades
-- (as witnessed concretely by witnessMatch in Flagship.agda).

open import SimulationModel using (flagshipPointwise; l0RealizedSurplus)
open import Flagship         using (RawMatch)

-- The pointwise flagship theorem for our concrete L3 simulation:
-- given any L0 simulation with a bad-seed witness, our concrete L3 sim dominates it.
concretePointwiseFlagship
  : ∀ {n}
  → (env    : SimEnvironment)
  → (simL0  : Seed (suc n) 2 → List RawMatch)
  → Σ (Seed (suc n) 2) (λ s₀ → l0RealizedSurplus (simL0 s₀) < 0ℚ)
  → Σ (Seed (suc n) 2) (λ s₀ → l0RealizedSurplus (simL0 s₀)
                                < realizedSurplus (concreteSim env s₀))
concretePointwiseFlagship env simL0 witness =
  flagshipPointwise (concreteSim env) simL0 witness
  --                ↑ our concrete SimFnL3    ↑ any L0 sim


-- ── Summary: What Phase 1 Has Proved ─────────────────────────────────────────
--
-- STRUCTURAL RESULTS (hold for all seeds, all environments):
--
--   (Theorem 1) valuationChain:   v_seller ≤ v_buyer  for any Match
--   (Theorem 2) surplusNonNeg:    0 ≤ v_buyer - v_seller  for any Match
--   (Theorem 3) realizedSurplus:  0 ≤ Σ surplus(t)  for any L3 Trace t
--   (Theorem 4) l3Efficiency:     0 ≤ efficiencyRatio(t, ps)
--   (Theorem 5) dominance:        L3 guarantees (3); L0 admits v_seller > v_buyer
--
-- SIMULATION RESULTS (concrete ZIT model with seed-driven strategies):
--
--   concreteSim : SimFnL3 — satisfies the abstract interface by construction
--   concreteSimSurplusNonNeg — Theorem 3 applies to every output trace
--
-- FLAGSHIP RESULTS (conditional on L0 behavior):
--
--   (Theorem 6) concretePointwiseFlagship:
--     ∃ s₀ where L3 surplus > L0 surplus
--     (given: ∃ s₁ where L0 surplus < 0)
--
-- PHASE 2 REQUIREMENTS:
--
--   (a) A concrete L0 simulation (using unconstrained seeds → RawMatch)
--   (b) Proof: ∃ seed where L0 surplus < 0 (by constructing the L0 witness seed)
--   (c) Proof or postulate: ∀ s, L0 surplus ≤ L3 surplus (pointwise dominance)
--   (d) The expected theorem: E[Eff(L3)] > E[Eff(L0)] using flagshipExpected
