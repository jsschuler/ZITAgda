-- Agent.agda
-- Defines the core agent types for the ZIT market simulation.
--
-- In Agda, every file is a module. The module name must match the file path
-- relative to the project root (with dots instead of slashes).
module Agent where

-- "open import" brings a standard library module into scope.
-- Data.Nat gives us the natural numbers ℕ (0, 1, 2, ...).
-- In Julia terms: think of ℕ as UInt with no overflow.
open import Data.Nat using (ℕ)

-- Data.Rational gives us ℚ, the rationals.
-- Prices, valuations, and budgets are all rational numbers.
-- Using ℚ means we never worry about floating-point rounding —
-- every price is exact. This matters for proofs.
open import Data.Rational using (ℚ)


-- ── Role ─────────────────────────────────────────────────────────────────────

-- "data" introduces a new type by listing its constructors.
-- This is like defining a Julia enum or abstract type with concrete subtypes.
--
--   data Role : Set where
--
-- "Set" is the type of small types. In Julia you'd write "::Type" on a
-- type-level variable; in Agda "Set" plays that role.
-- Every ordinary type (ℕ, ℚ, your own data) lives in Set.
data Role : Set where
  Buyer  : Role   -- wants to purchase one unit
  Seller : Role   -- wants to sell one unit


-- ── ValuationSchedule ────────────────────────────────────────────────────────

-- A valuation schedule maps quantity to value.
-- For Phase 1 (one-unit traders) this is just a single rational: v(1).
-- We use a record (named product type) so future multi-unit extension is easy.
--
-- "record" in Agda is like a Julia struct — a named bundle of fields.
-- "field" introduces each field name and its type.
record ValuationSchedule : Set where
  field
    -- The marginal value of the first (and only) unit.
    -- Buyers: maximum willingness to pay.
    -- Sellers: minimum acceptable price (reservation value / cost).
    unitValue : ℚ


-- ── TraderId ─────────────────────────────────────────────────────────────────

-- A trader id is just a natural number.
-- We give it a name so the intent is clear in type signatures.
-- In Julia: const TraderId = Int (a type alias).
-- In Agda, this is a definition: TraderId is defined to equal ℕ.
TraderId : Set
TraderId = ℕ


-- ── Agent ─────────────────────────────────────────────────────────────────────

-- The agent record bundles everything the institution needs to evaluate
-- a proposal: who you are, what you want, and what you can afford.
--
-- Notice that the fields have types from earlier in this file.
-- Agda reads top-to-bottom; you must define things before using them.
record Agent : Set where
  field
    -- Unique identifier for this trader.
    id        : TraderId

    -- Whether this agent is buying or selling.
    role      : Role

    -- The agent's private valuation schedule.
    -- The institution uses this when checking L3 constraints.
    valuation : ValuationSchedule

    -- Cash on hand. Must be sufficient to cover any accepted bid.
    -- For sellers, budget is less critical but we track it for generality.
    budget    : ℚ

    -- Number of units currently held.
    -- Buyers start at 0 (or some positive amount if endowed).
    -- Sellers must have inventory > 0 to submit a valid ask.
    inventory : ℕ
