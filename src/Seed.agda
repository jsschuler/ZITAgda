-- Seed.agda
-- Defines finite oracle tapes that drive all agent behavior.
--
-- Two new stdlib types appear here: Fin and Vec.
-- These are worth understanding deeply — they recur throughout Agda.
module Seed where

open import Data.Nat using (ℕ; suc)

-- Fin n is the canonical finite type with exactly n elements.
-- Its definition in the stdlib is:
--
--   data Fin : ℕ → Set where
--     zero : {n : ℕ} → Fin (suc n)
--     suc  : {n : ℕ} → Fin n → Fin (suc n)
--
-- The elements of Fin 3 are:
--   zero               (representing 0)
--   suc zero           (representing 1)
--   suc (suc zero)     (representing 2)
--
-- Fin 0 is EMPTY — it has no elements. This is not a runtime error;
-- it is a type-level impossibility. You cannot construct a value of Fin 0.
--
-- In Julia terms: Fin n is a type-safe bounded integer.
-- Where Julia checks array bounds at runtime, Agda encodes them in the type.
-- An array index of type Fin n literally cannot be out of bounds.
open import Data.Fin using (Fin)

-- Vec A n is a length-indexed list: a list of exactly n elements of type A.
-- Its definition:
--
--   data Vec (A : Set) : ℕ → Set where
--     []  : Vec A zero
--     _∷_ : A → Vec A n → Vec A (suc n)
--
-- The length n is part of the TYPE. Vec ℕ 3 and Vec ℕ 4 are different types.
-- The compiler will reject a Vec ℕ 3 where Vec ℕ 4 is expected.
--
-- In Julia: like a statically-sized SVector{n, A} from StaticArrays.jl,
-- but the size is tracked by the type system, not just a type parameter.
--
-- lookup : Vec A n → Fin n → A
-- is the key operation: it is TOTAL. No Maybe, no bounds check, no exception.
-- The type Fin n guarantees the index is in range.
open import Data.Vec using (Vec; lookup)


-- ── Price Grid ────────────────────────────────────────────────────────────────

-- The price grid has n ticks. An element of Fin n selects one tick.
-- Interpretation (index → rational price) lives in a later module.
-- Here we only care about the combinatorial structure.
--
-- n is the number of price ticks. We call it Ticks for clarity.
Ticks : Set
Ticks = ℕ


-- ── Seed ─────────────────────────────────────────────────────────────────────

-- A seed is a finite tape of draws.
--
--   n : number of price ticks  (granularity of the price grid)
--   k : number of draws        (length of the tape)
--
-- Each position holds a Fin n value — a uniform draw from {0, …, n−1}.
-- All agent behavior is a deterministic function of the seed.
-- Reproducibility follows: same seed ⟹ same trace.
--
-- Seed n k is just Vec (Fin n) k — a transparent alias, not a new type.
-- Agda unfolds aliases freely, so Seed and Vec (Fin n) can be used interchangeably.
Seed : ℕ → ℕ → Set
Seed n k = Vec (Fin n) k


-- ── Drawing from the Tape ─────────────────────────────────────────────────────

-- drawAt extracts the j-th value from a seed tape.
-- The type signature enforces totality:
--   j : Fin k  ← must be a valid index (0 to k−1), guaranteed by type
-- Returns a Fin n value — a price tick index.
--
-- Curly braces {n k : ℕ} mark IMPLICIT arguments.
-- Agda infers n and k from the types of s and j — you never write them.
-- In Julia: like type parameters inferred from argument types.
drawAt : {n k : ℕ} → Seed n k → Fin k → Fin n
drawAt s j = lookup s j


-- ── Seed Space ───────────────────────────────────────────────────────────────

-- The seed space for parameters (n, k) is the TYPE Seed n k itself.
-- In constructive mathematics, a finite set IS its type.
-- We do not need a separate "list of all seeds" — the type already IS the space.
--
-- Its cardinality (to be proved later):
--   |Seed n k| = n ^ k
--
-- This is the denominator in the probability formula:
--   P(E) = |{ s : Seed n k | s satisfies E }| / n ^ k
--
-- Universal quantification over the seed space is written:
--   ∀ (s : Seed n k) → ...
-- This is a proposition about ALL seeds simultaneously.
-- In Julia: there is no equivalent — Julia cannot express this in types.
SeedSpace : ℕ → ℕ → Set
SeedSpace n k = Seed n k
