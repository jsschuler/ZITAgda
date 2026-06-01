-- Proposal.agda
-- Defines raw proposals and the L0/L3 constraint predicates.
--
-- Key idea: a constraint is not a filter function that returns Bool.
-- It is a *type* — specifically, the type of *proofs* that a proposal
-- is admissible. This is the Curry-Howard correspondence:
--
--   Propositions  ↔  Types
--   Proofs        ↔  Values (programs)
--
-- So "a : L3Constraint agent π" means "a is a proof that π satisfies L3
-- for that agent." The institution admits a proposal by producing such a
-- proof. Illegal proposals are not just rejected — they are *untypeable*.
module Proposal where

-- We import Data.Nat but do NOT open it, to avoid name clashes.
-- Instead we rename _<_ to _<ℕ_ so it doesn't conflict with ℚ's _<_.
-- In Julia: like aliasing a method to avoid namespace collision.
open import Data.Nat      using (ℕ; zero) renaming (_<_ to _<ℕ_)

-- _≤_ on ℚ: p ≤ q means there exist integers satisfying p·denom(q) ≤ q·denom(p).
-- We don't need to think about the internals — the stdlib handles it.
open import Data.Rational using (ℚ; _≤_)

-- _×_ is the product type, which encodes logical conjunction.
-- A value of type (A × B) is a pair (a , b) with a : A and b : B.
-- In logic: A × B corresponds to A ∧ B.
-- In Julia: think of Tuple{A,B} but at the type level.
open import Data.Product  using (_×_)

-- ⊤ (pronounced "top" or "unit") is the type with exactly one element, tt.
-- It is always trivially inhabited, so it represents logical True (⊤).
-- L0 constraints will use this: every raw proposal trivially satisfies L0.
open import Data.Unit     using (⊤)

-- Bring Agent's definitions into scope.
-- After this, Role, Buyer, Seller, TraderId, Agent, ValuationSchedule
-- are all directly available.
open import Agent


-- ── Proposal ──────────────────────────────────────────────────────────────────

-- A raw proposal is what an agent submits to the institution.
-- It is "raw" because it may violate L3 constraints — that is allowed.
-- The institution will check admissibility separately.
record Proposal : Set where
  field
    proposer : TraderId   -- who is submitting
    price    : ℚ          -- proposed bid (buyer) or ask (seller)
    role     : Role       -- Buyer submits a bid; Seller submits an ask


-- ── L0 Constraint ─────────────────────────────────────────────────────────────

-- L0: unconstrained random behavior.
-- Any proposal is valid under L0 — the constraint is trivially True.
-- The underscore _ in argument position means "this argument is unused."
-- In Julia: you'd write f(::Agent, ::Proposal) = true
L0Constraint : Agent → Proposal → Set
L0Constraint _ _ = ⊤


-- ── L3 Constraint ─────────────────────────────────────────────────────────────

-- L3: valuation + budget/inventory constraints.
--
-- Mathematically:
--
--   L3(a, π) ≡ case a.role of
--     Buyer  → π.price ≤ v_a(1)  ∧  π.price ≤ a.budget
--     Seller → v_a(1) ≤ π.price  ∧  0 < a.inventory
--
-- where v_a(1) is agent a's unit valuation.
--
-- This is a *type-valued function* — it takes an agent and a proposal and
-- returns a TYPE (an element of Set). The type it returns is different
-- depending on whether the agent is a Buyer or Seller.
-- This is what "dependent types" means: the TYPE depends on a VALUE (role).
--
-- In Julia, you can dispatch on types; in Agda, you can dispatch on values
-- to produce types. This is strictly more expressive.
L3Constraint : Agent → Proposal → Set
L3Constraint a π = go (Agent.role a)
  where
    -- Local abbreviations to keep the constraint formulas readable.
    -- v : the agent's unit valuation  (their private value for one unit)
    -- p : the proposed price
    -- b : the agent's budget (cash on hand)
    -- n : the agent's current inventory
    v : ℚ
    v = ValuationSchedule.unitValue (Agent.valuation a)
    p : ℚ
    p = Proposal.price π
    b : ℚ
    b = Agent.budget a
    n : ℕ
    n = Agent.inventory a

    -- go dispatches on Role and returns the appropriate proposition (type).
    -- Pattern matching on a value to return a TYPE is perfectly valid in Agda.
    -- The two cases are different types — not different Bool values.
    go : Role → Set
    go Buyer  = p ≤ v  -- bid does not exceed valuation
               × p ≤ b  -- bid does not exceed budget
    go Seller = v ≤ p  -- ask is at least the reservation value
               × zero <ℕ n  -- must hold inventory to sell
