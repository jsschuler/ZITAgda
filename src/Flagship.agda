-- Flagship.agda
-- The structural dominance theorem:
--   L3 guarantees realizedSurplus ≥ 0 for every trace.
--   L0 admits value-destroying trades: ∃ match where v_seller > v_buyer.
--
-- New Agda ideas:
--   1. toWitness: extract proofs from decidable computations at compile time
--   2. Σ (dependent sum): the type of existential statements
--   3. Record construction syntax
module Flagship where

open import Data.Integer            using (+_)
open import Data.Rational           using (ℚ; _≤_; _<_; _-_; _/_; 0ℚ; 1ℚ; _>_)
open import Data.Rational.Properties using (_≤?_; _<?_)
open import Data.Product            using (Σ; _,_; _×_)
open import Data.Unit               using (tt)

-- toWitness extracts a proof from a successful decision procedure.
-- The idea: if (p ≤? q) evaluates to (yes proof) at compile time,
-- then toWitness tt : p ≤ q.
-- This lets us prove CONCRETE inequalities by computation — no hand-proof needed.
-- Agda's type-checker evaluates the decision procedure and checks it returns yes.
-- If the inequality were false, this would be a TYPE ERROR, not a runtime error.
open import Relation.Nullary.Decidable using (toWitness)

open import Agent
open import Proposal
open import Trace       using (Trace; realizedSurplus; realizedSurplusNonNeg)


-- ── Concrete Rational Literals ────────────────────────────────────────────────
--
-- The stdlib provides 0ℚ and 1ℚ. We define 2ℚ and 3ℚ here using
-- the constructor  _/_ : ℤ → ℕ → {{NonZero}} → ℚ
-- (+ n) is the integer +n of type ℤ.
-- The NonZero 1 instance is found automatically by Agda.

private
  2ℚ : ℚ
  2ℚ = (+ 2) / 1

  3ℚ : ℚ
  3ℚ = (+ 3) / 1


-- ── Raw Match (L0) ────────────────────────────────────────────────────────────
--
-- A RawMatch is a crossed pair of proposals with NO admissibility proofs.
-- Any agent can submit any price and get matched if bid ≥ ask.
-- This models the L0 institution — unconstrained.
--
-- Compare with Match in Institution.agda, which requires BuyerAdmissible
-- and SellerAdmissible fields. RawMatch has no such fields.
-- The absence of proof fields is the formal encoding of "no constraint."
record RawMatch : Set where
  field
    buyer         : Agent
    seller        : Agent
    bid           : Proposal
    ask           : Proposal
    crosses       : Proposal.price ask ≤ Proposal.price bid
    clearingPrice : ℚ
    priceInRange  : (Proposal.price ask ≤ clearingPrice)
                  × (clearingPrice ≤ Proposal.price bid)


-- ── Raw Surplus ───────────────────────────────────────────────────────────────

-- Surplus of a raw (L0) match. Same formula as for L3, but CAN BE NEGATIVE
-- because the admissibility constraints are absent.
rawSurplus : RawMatch → ℚ
rawSurplus m = ValuationSchedule.unitValue (Agent.valuation (RawMatch.buyer  m))
             - ValuationSchedule.unitValue (Agent.valuation (RawMatch.seller m))


-- ── Witness Construction ──────────────────────────────────────────────────────
--
-- We exhibit a concrete L0 match where v_seller > v_buyer.
-- This is impossible under L3 (proved by valuationChain in Institution.agda).
--
-- The witness:
--   Buyer  valuation = 1   bids 3  (above valuation — L3 would reject this)
--   Seller valuation = 2   asks 0  (below cost      — L3 would reject this)
--   bid (3) ≥ ask (0) ✓    clearing price = 1 ∈ [0, 3] ✓
--   Raw surplus = v_buyer - v_seller = 1 - 2 = -1 < 0

buyerWitness : Agent
buyerWitness = record
  { id        = 0
  ; role      = Buyer
  ; valuation = record { unitValue = 1ℚ }
  ; budget    = 3ℚ
  ; inventory = 0
  }

sellerWitness : Agent
sellerWitness = record
  { id        = 1
  ; role      = Seller
  ; valuation = record { unitValue = 2ℚ }
  ; budget    = 0ℚ
  ; inventory = 1
  }

bidWitness : Proposal
bidWitness = record
  { proposer = 0
  ; price    = 3ℚ      -- bids above own valuation — irrational but L0-legal
  ; role     = Buyer
  }

askWitness : Proposal
askWitness = record
  { proposer = 1
  ; price    = 0ℚ      -- asks below own cost — irrational but L0-legal
  ; role     = Seller
  }

-- The concrete L0 witness match.
-- toWitness tt proves each concrete inequality by computation at compile time.
-- Agda evaluates e.g. (0ℚ ≤? 3ℚ) → yes p, and toWitness tt extracts p.
witnessMatch : RawMatch
witnessMatch = record
  { buyer         = buyerWitness
  ; seller        = sellerWitness
  ; bid           = bidWitness
  ; ask           = askWitness
  ; crosses       = toWitness {a? = 0ℚ ≤? 3ℚ} tt
  ; clearingPrice = 1ℚ
  ; priceInRange  = toWitness {a? = 0ℚ ≤? 1ℚ} tt
                  , toWitness {a? = 1ℚ ≤? 3ℚ} tt
  }


-- ── Witness Theorem ───────────────────────────────────────────────────────────
--
-- The seller's valuation strictly exceeds the buyer's in the witness.
-- Under L3: structurally impossible (valuationChain proves ¬(v_s > v_b)).
-- Under L0: no proof is required, so this is admitted.
--
-- Proved by computation: Agda evaluates (1ℚ <? 2ℚ) → yes p at compile time.
witnessSellerHigher
  : ValuationSchedule.unitValue (Agent.valuation (RawMatch.seller witnessMatch))
  > ValuationSchedule.unitValue (Agent.valuation (RawMatch.buyer  witnessMatch))
witnessSellerHigher = toWitness {a? = 1ℚ <? 2ℚ} tt


-- ── The Structural Dominance Theorem ─────────────────────────────────────────
--
-- THEOREM (Structural Dominance).
--
-- L3 provides a hard structural guarantee absent from L0:
--
--   (1) ∀ t : Trace,   realizedSurplus(t) ≥ 0
--       Every completed L3 trade generates non-negative value.
--
--   (2) ∃ m : RawMatch,   v_seller(m) > v_buyer(m)
--       L0 admits value-destroying trades.
--
-- These are the structural facts from which the flagship efficiency inequality
--   E[Eff(L3)] > E[Eff(L0)]
-- follows once a probability model over seeds is added
-- (future work: Probability.agda, SimulationModel.agda).
--
-- The type  Σ A P  is the DEPENDENT SUM (dependent pair / existential).
--   Σ A P  =  ∃ (a : A), P(a)
-- A value of  Σ A P  is a pair  (a , p)  where  a : A  and  p : P(a).
-- In logic:  Σ A P  is  ∃ a, P(a).
-- In Julia:  there is no type-level existential. Closest is a Tuple{Any,Any}
--            but without the dependent typing.

dominance
  :  (∀ (t : Trace) → 0ℚ ≤ realizedSurplus t)
  ×  Σ RawMatch (λ m →
       ValuationSchedule.unitValue (Agent.valuation (RawMatch.seller m))
       > ValuationSchedule.unitValue (Agent.valuation (RawMatch.buyer m)))

dominance = realizedSurplusNonNeg
          , witnessMatch
          , witnessSellerHigher
