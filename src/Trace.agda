-- Trace.agda
-- Defines the event vocabulary, certified traces, and the key derived view:
-- realized surplus — the sum of surplus across all settled trades.
--
-- New Agda idea: structural induction on List.
-- A proof about all traces is a recursive function on the list structure.
module Trace where

open import Data.Rational           using (ℚ; _+_; 0ℚ; _≤_)
open import Data.Rational.Properties using (≤-refl; +-mono-≤; +-identityˡ)
open import Data.List               using (List; []; _∷_)

-- subst is Leibniz substitution, used in the arithmetic helper below.
open import Relation.Binary.PropositionalEquality using (subst)

open import Agent
open import Proposal
open import Institution using (Match)
open import Surplus     using (surplus; surplusNonNeg)


-- ── Event Vocabulary ──────────────────────────────────────────────────────────
--
-- An event is one atomic step in the history of a market.
-- The trace is the complete record of what happened, in order.
--
-- Crucially: TradeSettled carries a Match, not just prices.
-- A Match is certified — it embeds the L3 proofs by construction.
-- So any trace containing TradeSettled events is automatically certified.
-- There is no separate "certified trace" type needed:
-- the type of Match does the work.
--
-- In Julia: you'd have a struct with fields and runtime checks.
-- In Agda: the type system ensures ill-formed events don't exist.
data Event : Set where
  -- An agent submitted a raw proposal to the institution.
  OrderSubmitted : TraderId → Proposal → Event

  -- The institution rejected the proposal (failed L3 check).
  -- The rejected proposal is recorded for observability.
  OrderRejected  : TraderId → Proposal → Event

  -- The institution accepted the proposal (passed L3 check).
  OrderAccepted  : TraderId → Proposal → Event

  -- A buyer and seller were matched and the trade settled.
  -- The Match record carries the L3 admissibility proofs.
  TradeSettled   : Match → Event

  -- The batch auction cleared at the given price.
  AuctionCleared : ℚ → Event


-- ── Trace ─────────────────────────────────────────────────────────────────────
--
-- A trace is a list of events, ordered earliest-first.
-- List A in Agda is defined:
--
--   data List (A : Set) : Set where
--     []  : List A
--     _∷_ : A → List A → List A
--
-- _∷_ is pronounced "cons" (from Lisp). x ∷ xs is "x prepended to xs".
-- In Julia: comparable to Vector, but immutable and built by prepending.
-- Pattern matching on [] and (x ∷ xs) is exhaustive induction on the list.
Trace : Set
Trace = List Event


-- ── Derived Views ─────────────────────────────────────────────────────────────

-- Extract all settled matches from a trace.
-- This ignores rejected/accepted orders and clearing events.
-- Pattern matching on three cases:
--   []              → empty trace, no trades
--   TradeSettled m  → found a trade, include it
--   anything else   → skip and recurse
--
-- The underscore _ in the last clause is a wildcard: matches any Event
-- that is not TradeSettled. Agda checks that all constructors are covered.
tradesView : Trace → List Match
tradesView []                    = []
tradesView (TradeSettled m ∷ es) = m ∷ tradesView es
tradesView (_             ∷ es) = tradesView es


-- ── Realized Surplus ─────────────────────────────────────────────────────────

-- Sum the surplus of every trade in the match list.
-- This is a structural recursion (fold) on the list.
-- The base case (empty list) gives 0: no trades, no surplus.
-- The inductive case adds the head match's surplus to the recursive result.
sumSurplus : List Match → ℚ
sumSurplus []       = 0ℚ
sumSurplus (m ∷ ms) = surplus m + sumSurplus ms

-- The realized surplus of a full trace.
realizedSurplus : Trace → ℚ
realizedSurplus t = sumSurplus (tradesView t)


-- ── Arithmetic Helper ─────────────────────────────────────────────────────────

-- LEMMA. 0 ≤ a → 0 ≤ b → 0 ≤ a + b.
--
-- PROOF.
--   +-mono-≤ ha hb  :  0 + 0  ≤  a + b
--   +-identityˡ 0ℚ  :  0 + 0  ≡  0
--   subst           :  0      ≤  a + b     ✓
--
-- +-identityˡ : ∀ x → 0 + x ≡ x
-- Applied to 0ℚ: 0 + 0 ≡ 0.
private
  0≤a+b : {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a + b
  0≤a+b {a} {b} ha hb =
    subst (_≤ a + b) (+-identityˡ 0ℚ) (+-mono-≤ ha hb)


-- ── Main Theorem ──────────────────────────────────────────────────────────────
--
-- THEOREM (Non-Negative Realized Surplus).
-- The total surplus of any L3 trace is non-negative:
--   ∀ (ms : List Match),  0 ≤ sumSurplus ms
--
-- PROOF by structural induction on the match list.
--
-- Base case ([]): sumSurplus [] = 0, and 0 ≤ 0 by reflexivity.
--
-- Inductive case (m ∷ ms):
--   sumSurplus (m ∷ ms)  =  surplus m + sumSurplus ms
--   surplusNonNeg m      :  0 ≤ surplus m          [Theorem 2, Surplus.agda]
--   ind. hypothesis      :  0 ≤ sumSurplus ms
--   0≤a+b                :  0 ≤ surplus m + sumSurplus ms  ✓
--
-- In Agda, "proof by induction" IS "definition by recursion."
-- The same syntax that defines a recursive function defines an inductive proof.
-- There is no distinction.
sumSurplusNonNeg : ∀ (ms : List Match) → 0ℚ ≤ sumSurplus ms
sumSurplusNonNeg []       = ≤-refl
sumSurplusNonNeg (m ∷ ms) = 0≤a+b (surplusNonNeg m) (sumSurplusNonNeg ms)

-- The corollary for full traces.
realizedSurplusNonNeg : ∀ (t : Trace) → 0ℚ ≤ realizedSurplus t
realizedSurplusNonNeg t = sumSurplusNonNeg (tradesView t)
