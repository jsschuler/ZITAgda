-- Surplus.agda
-- Defines trade surplus and proves it is non-negative for every L3 match.
--
-- This module introduces two new ideas:
--   1. Propositional equality _≡_ and subst
--   2. Composing lemmas: surplusNonNeg is a one-liner built from valuationChain
module Surplus where

open import Data.Rational           using (ℚ; _≤_; _-_; -_; 0ℚ)
open import Data.Rational.Properties using (≤-trans; +-inverseʳ; +-monoˡ-≤)

-- Propositional equality.
-- a ≡ b is the type of proofs that a and b are *equal*.
-- It has exactly one constructor: refl : a ≡ a (reflexivity).
-- You cannot construct (a ≡ b) unless a and b are definitionally equal
-- or you prove it by other means.
--
-- Crucially: _≡_ is a TYPE. A proof of equality is a VALUE.
-- This is the same Curry-Howard principle as before, applied to equality.
--
-- In Julia: equality is Bool. In Agda: equality is a type,
-- and having a value of that type IS the proof of equality.
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Agent
open import Institution using (Match; BuyerAdmissible; SellerAdmissible; valuationChain)


-- ── Arithmetic Lemma ─────────────────────────────────────────────────────────
--
-- This lemma is not in Data.Rational.Properties for normalized ℚ,
-- so we prove it here.
--
-- LEMMA. For any p q : ℚ,  p ≤ q  →  0 ≤ q - p.
--
-- PROOF (on paper).
--   p ≤ q
--   ⟹  p + (-p) ≤ q + (-p)    [add -p to both sides, monotonicity of +]
--   ⟹  0 ≤ q - p              [since p + (-p) = 0 and q + (-p) = q - p]
--
-- PROOF (in Agda).
-- We need three facts:
--
--   +-monoˡ-≤ (-p) (p ≤ q)  :  p + (-p)  ≤  q + (-p)
--                                      ↑ this is definitionally q - p
--
--   +-inverseʳ p             :  p + (-p)  ≡  0ℚ
--
--   subst P eq t             :  if  eq : a ≡ b  and  t : P a
--                                then  subst P eq t : P b
--
-- subst replaces a with b in the TYPE of t.
-- Here:  a = p + (-p),  b = 0ℚ,  P = (_≤ q - p)
--   t   : p + (-p) ≤ q - p     [from +-monoˡ-≤]
--   eq  : p + (-p) ≡ 0ℚ        [from +-inverseʳ]
-- result: 0ℚ ≤ q - p           ✓
--
-- In mathematics: subst is the substitution rule for equality.
-- If you know a = b and P(a), then P(b).
-- Leibniz's law: indiscernibility of identicals.

p≤q⇒0≤q-p : ∀ {p q : ℚ} → p ≤ q → 0ℚ ≤ q - p
p≤q⇒0≤q-p {p} {q} p≤q =
  subst (_≤ q - p) (+-inverseʳ p) (+-monoˡ-≤ (- p) p≤q)
  --              ^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^
  --              eq : p+(-p) ≡ 0   t : p+(-p) ≤ q-p


-- ── Surplus ──────────────────────────────────────────────────────────────────

-- The gross gains from trade of a match:
--   surplus m  =  v_buyer(1) - v_seller(1)
--
-- This is the total economic value generated if the trade executes.
-- It does not depend on the clearing price — that only determines
-- how the surplus is divided between buyer and seller.

surplus : Match → ℚ
surplus m = ValuationSchedule.unitValue (Agent.valuation (Match.buyer  m))
          - ValuationSchedule.unitValue (Agent.valuation (Match.seller m))


-- ── Main Theorem ──────────────────────────────────────────────────────────────
--
-- THEOREM (Non-Negative Surplus).
-- Every admitted L3 match generates non-negative surplus:
--   ∀ m : Match,  0 ≤ surplus m
--
-- PROOF.
--   valuationChain m  :  v_seller ≤ v_buyer        [Theorem 1, Institution.agda]
--   p≤q⇒0≤q-p        :  v_seller ≤ v_buyer  →  0 ≤ v_buyer - v_seller
--   compose           :  0 ≤ surplus m             ✓
--
-- The proof is a single function application.
-- All the work was already done in valuationChain.
-- This is the payoff of modular proof construction.

surplusNonNeg : ∀ (m : Match) → 0ℚ ≤ surplus m
surplusNonNeg m = p≤q⇒0≤q-p (valuationChain m)
