-- BatchAuction.agda
-- Implements the batch clearing auction: match certified bids and asks
-- into a list of certified Match values.
--
-- The key invariant: every Match in the output is structurally L3-admissible.
-- This follows from the input types — if the inputs are certified, the outputs are too.
-- The batch auction cannot introduce inadmissible trades by construction.
--
-- Two functions:
--   tryMatch   : one bid × one ask → Maybe Match
--                (Some if ask.price ≤ bid.price, None otherwise)
--   matchPairs : List bids × List asks → List Match
--                (zip the lists, collect successes)
--
-- Design notes for Phase 1:
--   - No order-book sorting. Buyers and sellers are matched in list order.
--   - The clearing price is set to the ask price (simplest proof obligation).
--   - Full sorted order-book matching is future work (BatchAuctionFull.agda).
--   - BidEntry / AskEntry use Σ-types to package heterogeneous agents.
--
-- New Agda ideas:
--   Data.Maybe   — the option type (Maybe A = Nothing | Just a)
--   with clause  — pattern match on the result of an expression mid-definition
--   Dec          — decidable propositions (yes p | no ¬p)
module BatchAuction where

open import Data.Nat     using (ℕ)
open import Data.Rational
  using (ℚ; _≤_)
open import Data.Rational.Properties
  using (_≤?_; ≤-refl)
open import Data.List    using (List; []; _∷_; _++_; [_])
open import Data.Maybe    using (Maybe; just; nothing)
open import Data.Product  using (Σ; _,_; _×_)
open import Relation.Nullary using (yes; no)

open import Agent
open import Proposal
open import Institution  using (BuyerAdmissible; SellerAdmissible; Match)
open import AgentStrategy using (CertifiedBid; CertifiedAsk)


-- ── Entry Types ───────────────────────────────────────────────────────────────
--
-- BidEntry packages a buyer agent together with a certified bid.
-- AskEntry packages a seller agent together with a certified ask.
--
-- The Σ-type  Σ Agent CertifiedBid  is the dependent sum:
--   "there exists an agent a, and a certified bid for a."
-- A value is a pair  (a , cb)  where  a : Agent  and  cb : CertifiedBid a.
--
-- Why not just List (CertifiedBid someConcreteAgent)?
-- Because the auction processes bids from different agents, and each CertifiedBid
-- carries evidence parameterized by ITS OWN agent. Σ lets us pack them together
-- in a single list type without losing the agent.

BidEntry : Set
BidEntry = Σ Agent CertifiedBid

AskEntry : Set
AskEntry = Σ Agent CertifiedAsk


-- ── tryMatch: single bid × single ask → Maybe Match ──────────────────────────
--
-- Attempt to match one certified bid against one certified ask.
-- Returns Just m if they cross (ask.price ≤ bid.price), Nothing otherwise.
--
-- PROOF OBLIGATIONS:
--   crosses      : Proposal.price ask ≤ Proposal.price bid
--                  (from the Dec result; we only enter the 'yes' branch with the proof)
--   clearingPrice: set to Proposal.price ask  (ask-price clearing)
--   priceInRange :
--     fst = ask.price ≤ clearingPrice = ask.price ≤ ask.price  → ≤-refl
--     snd = clearingPrice ≤ bid.price = ask.price ≤ bid.price  → crosses
--
-- The with clause pattern-matches on the result of  ask.price ≤? bid.price
-- at the DEFINITION level. In Julia: an if/else on the comparison result.
-- In Agda: the match exhausts all cases (yes/no), giving us the proof in 'yes'.

tryMatch : BidEntry → AskEntry → Maybe Match
tryMatch (buyer , cb) (seller , ca)
  with Proposal.price (CertifiedAsk.proposal ca) ≤? Proposal.price (CertifiedBid.proposal cb)
... | yes crosses = just record
      { buyer        = buyer
      ; seller       = seller
      ; bid          = CertifiedBid.proposal cb
      ; ask          = CertifiedAsk.proposal ca
      ; buyerAdm     = CertifiedBid.admissible cb
      ; sellerAdm    = CertifiedAsk.admissible ca
      ; crosses      = crosses
      ; clearingPrice = Proposal.price (CertifiedAsk.proposal ca)
      ; priceInRange  = ≤-refl , crosses
      }
... | no  _       = nothing


-- ── collectMatches: filter-map over a list ────────────────────────────────────
--
-- Apply f to every element of xs, collecting Just results.
-- This is Data.List.filterMap, defined here to keep BatchAuction self-contained.
--
-- In Julia: filter(x -> x !== nothing, map(f, xs)) but type-safe.

private
  collectMatches : ∀ {A : Set} → (A → Maybe Match) → List A → List Match
  collectMatches f []       = []
  collectMatches f (x ∷ xs) with f x
  ... | just m  = m ∷ collectMatches f xs
  ... | nothing =     collectMatches f xs


-- ── matchPairs: zip two lists, collect successes ──────────────────────────────
--
-- Given a list of certified bids and a list of certified asks,
-- attempt to match bid[i] against ask[i] for each i.
-- Unmatched tails (if the lists have different lengths) are dropped.
--
-- This is the Phase 1 batch auction:
--   bid₀ vs ask₀, bid₁ vs ask₁, ...
-- No sorting, no price discovery mechanism — just pairwise crossing checks.
--
-- Economic interpretation: agents are already paired (e.g. by a random permutation
-- encoded in a seed). The auction admits crossing pairs and rejects the rest.

matchPairs : List BidEntry → List AskEntry → List Match
matchPairs []           _            = []
matchPairs _            []           = []
matchPairs (be ∷ bids) (ae ∷ asks)  =
  collectMatches (tryMatch be) (ae ∷ asks)
  ++ matchPairs bids []
  -- Simple interpretation: try bid be against all remaining asks in order;
  -- then recurse on remaining bids (which will see no remaining asks).
  -- Practical effect: each bid is tried against each ask once,
  -- but the "at most one match per trader" constraint is NOT enforced here.
  -- Full one-to-one matching is future work.


-- ── Simpler one-to-one matching ───────────────────────────────────────────────
--
-- matchZip: match bid[i] against ask[i] only (strict pairing).
-- This is the ZIT interpretation: each buyer is pre-matched to a seller;
-- the auction just checks if they cross.
-- Useful for the flagship simulation where pairing comes from the seed.

matchZip : List BidEntry → List AskEntry → List Match
matchZip []            _             = []
matchZip _             []            = []
matchZip (be ∷ bids)  (ae ∷ asks)   =
  collectMatches (tryMatch be) [ ae ] ++ matchZip bids asks


-- ── Correctness Notes ────────────────────────────────────────────────────────
--
-- Every Match in the output of matchPairs or matchZip is a certified Match.
-- This holds by the definition of tryMatch:
--   - buyerAdm  came from CertifiedBid.admissible (proved L3-admissible)
--   - sellerAdm came from CertifiedAsk.admissible (proved L3-admissible)
--   - crosses   came from the 'yes' branch of _≤?_ (a proof, not just a Bool)
--
-- THEOREM (informally): for any output match m of matchZip/matchPairs,
--   realizedSurplus {m} ≥ 0.
-- This is already proved as realizedSurplusNonNeg in Trace.agda — it holds
-- for ALL traces, and the output of the batch auction produces valid traces.
