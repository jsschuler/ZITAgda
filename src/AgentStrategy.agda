-- AgentStrategy.agda
-- Produces L3-certified proposals from agent data and seed indices.
--
-- The central idea: a strategy is a FUNCTION from seed index → certified proposal.
-- The return type carries admissibility EVIDENCE, so any call to makeXxx
-- is, by construction, a proof that the proposal is L3-admissible.
--
-- Two families:
--   makeBuyerBid   — produces a bid at grid index i within [0, v ⊓ b]
--   makeSellerAsk  — produces an ask at grid index i within [v, maxP)
--
-- Connections to previous modules:
--   PriceGrid    provides tick functions and their properties
--   Institution  provides BuyerAdmissible and SellerAdmissible record types
--   Agent        provides Agent record (valuation, budget, inventory, id)
--   Proposal     provides Proposal record (proposer, price, role)
--
-- New Agda idea: record construction syntax
--   record { field₁ = val₁ ; field₂ = val₂ }
-- is how you build a record value. It is the Agda analog of
--   struct MyRecord { field₁ = val₁, field₂ = val₂ }
-- in other languages. The type-checker verifies each val has the right type.
module AgentStrategy where

open import Data.Nat      using (ℕ; zero; suc) renaming (_<_ to _<ℕ_)
open import Data.Fin      using (Fin)
open import Data.Rational using (ℚ; _⊓_; 0ℚ; _≤_)

open import Agent
open import Proposal
open import Institution   using (BuyerAdmissible; SellerAdmissible)
open import PriceGrid


-- ── Certified Proposal Types ─────────────────────────────────────────────────
--
-- A CertifiedBid for agent a is a PAIR:
--   1. A Proposal (price, role, proposer)
--   2. A BuyerAdmissible proof that the proposal satisfies L3 for agent a
--
-- The evidence field is non-forgeable — you cannot construct a CertifiedBid
-- without providing a proof. This is the Agda encoding of
-- "the institution admits this proposal."
--
-- In Julia: no equivalent. A Tuple{Proposal, Bool} would carry the answer
-- but not the proof. CertifiedBid carries the proof itself.

record CertifiedBid (a : Agent) : Set where
  field
    proposal   : Proposal
    admissible : BuyerAdmissible a proposal

record CertifiedAsk (a : Agent) : Set where
  field
    proposal   : Proposal
    admissible : SellerAdmissible a proposal


-- ── L3 Buyer Strategy ────────────────────────────────────────────────────────
--
-- makeBuyerBid n a i cap≥0
--   n      : grid resolution (number of ticks = suc n)
--   a      : the buyer agent
--   i      : seed index  (which tick the oracle gave)
--   cap≥0  : proof that 0 ≤ v ⊓ b (both valuation and budget are non-negative)
--
-- Price: p = (v ⊓ b) * (toℕ i / suc n)
--   where v = Agent.valuation.unitValue, b = Agent.budget
--
-- The admissibility fields are filled by the PriceGrid theorems:
--   bidBelowValue   ← buyerTickBelowValuation n v b i cap≥0
--   bidWithinBudget ← buyerTickWithinBudget   n v b i cap≥0
--
-- PROOF CHECK:
--   bidBelowValue  : Proposal.price π ≤ v
--   Proposal.price π  =  p  =  buyerTick n v b i   ← definitionally
--   buyerTickBelowValuation ... : buyerTick n v b i ≤ v  ✓
--
-- The types align definitionally — no cast or subst needed.

makeBuyerBid
  : (n : ℕ)
  → (a : Agent)
  → Fin (suc n)
  → 0ℚ ≤ ValuationSchedule.unitValue (Agent.valuation a) ⊓ Agent.budget a
  → CertifiedBid a
makeBuyerBid n a i cap≥0 = record
  { proposal   = record
      { proposer = Agent.id a
      ; price    = p
      ; role     = Buyer
      }
  ; admissible = record
      { bidBelowValue   = buyerTickBelowValuation n v b i cap≥0
      ; bidWithinBudget = buyerTickWithinBudget   n v b i cap≥0
      }
  }
  where
    v = ValuationSchedule.unitValue (Agent.valuation a)
    b = Agent.budget a
    p = buyerTick n v b i


-- ── L3 Seller Strategy ───────────────────────────────────────────────────────
--
-- makeSellerAsk n a maxP i v≤maxP hasInv
--   n       : grid resolution
--   a       : the seller agent
--   maxP    : upper price bound for the market (a model parameter)
--   i       : seed index
--   v≤maxP  : proof that v ≤ maxP (spread is non-negative, grid is well-defined)
--   hasInv  : proof that the agent holds at least one unit (zero <ℕ inventory)
--
-- Price: p = v + (maxP - v) * (toℕ i / suc n)
--   where v = Agent.valuation.unitValue
--
-- The admissibility fields:
--   askAboveValue  ← sellerTickAboveValuation n v maxP i v≤maxP
--   hasInventory   ← hasInv  (passed directly — price grid has no say over stock)
--
-- Note: hasInventory is a proof about the agent's current state, not the seed.
-- The seed governs the PRICE; the inventory check is a separate precondition.
-- In a full simulation model, inventory would be tracked through the trace.

makeSellerAsk
  : (n : ℕ)
  → (a : Agent)
  → (maxP : ℚ)
  → Fin (suc n)
  → ValuationSchedule.unitValue (Agent.valuation a) ≤ maxP
  → zero <ℕ Agent.inventory a
  → CertifiedAsk a
makeSellerAsk n a maxP i v≤maxP hasInv = record
  { proposal   = record
      { proposer = Agent.id a
      ; price    = p
      ; role     = Seller
      }
  ; admissible = record
      { askAboveValue = sellerTickAboveValuation n v maxP i v≤maxP
      ; hasInventory  = hasInv
      }
  }
  where
    v = ValuationSchedule.unitValue (Agent.valuation a)
    p = sellerTick n v maxP i


-- ── What This Module Proves ───────────────────────────────────────────────────
--
-- Every call to makeBuyerBid   produces a BuyerAdmissible proof.
-- Every call to makeSellerAsk  produces a SellerAdmissible proof.
--
-- This means: any simulation that uses these strategy functions CANNOT
-- construct L3-violating proposals. The constraint is enforced at the
-- *type level*, not at runtime.
--
-- The ZIT intuition: L3 agents are zero-intelligence WITH the constraint.
-- Their prices are drawn uniformly from [0, v ⊓ b] or [v, maxP).
-- They are "random" within their admissible region — but structurally
-- they can never bid above value or ask below cost.
