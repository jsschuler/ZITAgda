-- Institution.agda
-- Defines the batch clearing auction and proves the core structural lemma:
-- every admitted match satisfies v_seller ≤ v_buyer.
--
-- This module is the mathematical heart of Phase 1.
-- The flagship theorem will be assembled from lemmas proved here.
module Institution where

open import Data.Nat      using (ℕ; zero) renaming (_<_ to _<ℕ_)
open import Data.Rational using (ℚ; _≤_)

-- ≤-trans : Transitive _≤_
-- i.e.  a ≤ b  →  b ≤ c  →  a ≤ c
-- This is the only arithmetic fact we need for the structural lemma.
open import Data.Rational.Properties using (≤-trans)
open import Data.Product              using (_×_)

open import Agent
open import Proposal


-- ── Admissibility Records ─────────────────────────────────────────────────────
--
-- We split L3Constraint into two named records, one per role.
-- Using a record instead of _×_ gives us named projections
-- (e.g. BuyerAdmissible.bidBelowValue) which makes proofs self-documenting.
--
-- These are the *evidence types* the institution produces when it accepts
-- a proposal. The institution does not return Bool — it returns a proof.

-- Evidence that a buyer's proposal passes L3.
record BuyerAdmissible (a : Agent) (π : Proposal) : Set where
  field
    -- The bid does not exceed the buyer's private valuation.
    -- Economically: the buyer cannot gain by bidding above value.
    bidBelowValue   : Proposal.price π ≤ ValuationSchedule.unitValue (Agent.valuation a)

    -- The bid does not exceed the buyer's cash on hand.
    -- Economically: the buyer can actually pay if matched.
    bidWithinBudget : Proposal.price π ≤ Agent.budget a

-- Evidence that a seller's proposal passes L3.
record SellerAdmissible (a : Agent) (π : Proposal) : Set where
  field
    -- The ask is at least the seller's reservation value.
    -- Economically: the seller cannot gain by asking below cost.
    askAboveValue : ValuationSchedule.unitValue (Agent.valuation a) ≤ Proposal.price π

    -- The seller holds at least one unit to deliver.
    -- Zero <ℕ n is the Agda spelling of n > 0 for natural numbers.
    hasInventory  : zero <ℕ Agent.inventory a


-- ── Match ─────────────────────────────────────────────────────────────────────
--
-- A Match is a crossed pair of admitted proposals: a buyer bid and a seller ask
-- where ask ≤ bid (the market-clearing condition).
--
-- The record CARRIES the admissibility proofs as fields.
-- You cannot construct a Match without providing them.
-- An inadmissible match is not rejected — it is *unrepresentable*.
--
-- This is the institution as a type: the type Match only contains
-- economically valid transactions.
record Match : Set where
  field
    buyer     : Agent
    seller    : Agent
    bid       : Proposal      -- the buyer's submitted price
    ask       : Proposal      -- the seller's submitted price

    -- Proof that the buyer's proposal satisfies L3.
    buyerAdm  : BuyerAdmissible buyer bid

    -- Proof that the seller's proposal satisfies L3.
    sellerAdm : SellerAdmissible seller ask

    -- The market-clearing condition: ask ≤ bid.
    -- A profitable trade is possible only when the buyer bids at least
    -- as much as the seller asks.
    crosses   : Proposal.price ask ≤ Proposal.price bid

    -- The clearing price is any rational in [ask, bid].
    -- In a uniform-price batch auction, all trades clear at the same price.
    clearingPrice : ℚ

    -- Evidence that the clearing price is within the spread.
    -- priceInRange.askBelowClear : ask ≤ clearingPrice
    -- priceInRange.clearBelowBid : clearingPrice ≤ bid
    priceInRange  : (Proposal.price ask ≤ clearingPrice)
                  × (clearingPrice ≤ Proposal.price bid)


-- ── Structural Lemma: Valuation Chain ────────────────────────────────────────
--
-- THEOREM (Valuation Chain).
-- For any admitted match m:
--   v_seller ≤ v_buyer
--
-- PROOF.
-- The following chain holds by the fields of m:
--
--   v_seller  ≤  ask           (SellerAdmissible.askAboveValue)
--            ≤  bid            (Match.crosses)
--            ≤  v_buyer        (BuyerAdmissible.bidBelowValue)
--
-- Each step is a ≤ relation on ℚ; we chain them with ≤-trans.
--
-- In Agda a proof IS a program.
-- The type of valuationChain is the statement of the theorem.
-- The definition is the proof. There is no separation.
--
-- In Julia terms: this function's TYPE is a mathematical theorem,
-- its BODY is its proof. The type-checker verifying it compiles
-- is equivalent to checking the proof.

valuationChain
  : (m : Match)
  → ValuationSchedule.unitValue (Agent.valuation (Match.seller m))
  ≤ ValuationSchedule.unitValue (Agent.valuation (Match.buyer  m))

valuationChain m =
  ≤-trans
    (≤-trans
      (SellerAdmissible.askAboveValue (Match.sellerAdm m))   -- v_s ≤ ask
      (Match.crosses m))                                     -- ask ≤ bid
    (BuyerAdmissible.bidBelowValue (Match.buyerAdm m))       -- bid ≤ v_b
