-- Probability.agda
-- Finite probability theory: sums over lists and the key comparison lemmas.
-- No measure theory. Probability is counting/summing over a finite list of outcomes.
--
-- New Agda ideas:
--   All  — a proof that every element of a list satisfies a predicate
--   data (inductive relation) — defining the pointwise and strict comparison types
module Probability where

open import Data.Rational           using (ℚ; _+_; _≤_; _<_; 0ℚ)
open import Data.Rational.Properties
  using (≤-refl; +-mono-≤; +-identityˡ; +-mono-<-≤; +-monoʳ-≤)
open import Data.List               using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (subst)

-- All P xs:  a proof that every element of xs satisfies predicate P.
-- Defined inductively — it IS a list of proofs, one per element.
--
-- [] : All P []                  — vacuously true
-- h ∷ hs : All P (x ∷ xs)       — h proves P x, hs proves All P xs
--
-- In Julia: all(P, xs) returns Bool. In Agda, All P xs is a TYPE of proofs.
-- Having a value of this type IS the proof that all elements satisfy P.
open import Data.List.Relation.Unary.All
  using (All) renaming ([] to []-all; _∷_ to _∷-all_)


-- ── Pointwise Comparisons ─────────────────────────────────────────────────────
--
-- Instead of using heavy stdlib machinery, we define our own pointwise
-- comparison types by induction on two lists simultaneously.
-- This is a common Agda pattern: relate two structures by induction on both.

-- Pointwise≤ xs ys: xs[i] ≤ ys[i] for all i.
data Pointwise≤ : List ℚ → List ℚ → Set where
  pw-nil  : Pointwise≤ [] []
  pw-cons : ∀ {x y xs ys} → x ≤ y → Pointwise≤ xs ys
           → Pointwise≤ (x ∷ xs) (y ∷ ys)

-- StrictAt xs ys: xs[i] ≤ ys[i] everywhere, with strict xs[j] < ys[j] at one j.
-- Two constructors: the strict comparison is either "here" (head) or "there" (tail).
data StrictAt : List ℚ → List ℚ → Set where
  here  : ∀ {x y xs ys} → x < y  → Pointwise≤ xs ys → StrictAt (x ∷ xs) (y ∷ ys)
  there : ∀ {x y xs ys} → x ≤ y  → StrictAt xs ys   → StrictAt (x ∷ xs) (y ∷ ys)


-- ── Sum of a List of Rationals ────────────────────────────────────────────────

sumQ : List ℚ → ℚ
sumQ []       = 0ℚ
sumQ (x ∷ xs) = x + sumQ xs

-- ── Arithmetic Helper ─────────────────────────────────────────────────────────

private
  0≤a+b : {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a + b
  0≤a+b {a} {b} ha hb =
    subst (_≤ a + b) (+-identityˡ 0ℚ) (+-mono-≤ ha hb)


-- ── Theorem: Non-Negative Sum ─────────────────────────────────────────────────
--
-- If every element of xs is ≥ 0, then sumQ xs ≥ 0.
-- Proof: induction on xs, using 0≤a+b at each step.

sumQNonNeg : ∀ (xs : List ℚ) → All (0ℚ ≤_) xs → 0ℚ ≤ sumQ xs
sumQNonNeg []       []-all         = ≤-refl
sumQNonNeg (x ∷ xs) (hx ∷-all hxs) = 0≤a+b hx (sumQNonNeg xs hxs)


-- ── Theorem: Pointwise Monotonicity ──────────────────────────────────────────
--
-- If xs ≤ ys at every position, then sumQ xs ≤ sumQ ys.
-- Proof: induction, using +-mono-≤ to add the head inequalities.

sumQMono : ∀ {xs ys} → Pointwise≤ xs ys → sumQ xs ≤ sumQ ys
sumQMono pw-nil          = ≤-refl
sumQMono (pw-cons h hxs) = +-mono-≤ h (sumQMono hxs)


-- ── Theorem: Strict Monotonicity ─────────────────────────────────────────────
--
-- If xs ≤ ys everywhere and xs < ys at one position, then sumQ xs < sumQ ys.
--
-- PROOF by induction on the StrictAt witness.
--
-- Case "here" (strict at head):
--   x < y   and   Pointwise≤ xs ys
--   x + sumQ xs < y + sumQ ys
--   ↑ using +-mono-<-≤ (x < y) (sumQ xs ≤ sumQ ys)
--
-- Case "there" (strict in tail):
--   x ≤ y   and   StrictAt xs ys  →  sumQ xs < sumQ ys (by IH)
--   x + sumQ xs < x + sumQ ys     (by +-monoʳ-≤, right-monotonicity in x)
--   x + sumQ xs ≤ y + sumQ ys ... wait, we need x ≤ y and sumQ xs < sumQ ys
--
-- More carefully for "there":
--   sumQ (x ∷ xs)  =  x + sumQ xs
--                  ≤  x + sumQ ys    [+-monoʳ-≤ holds sumQ xs ≤ sumQ ys...
--                                    but we have STRICT: sumQ xs < sumQ ys]
-- Actually: x + sumQ xs < x + sumQ ys (strict right monotonicity)
--           x + sumQ ys ≤ y + sumQ ys (since x ≤ y, left monotonicity)
-- But the type is sumQ xs < sumQ ys, and we want x + sumQ xs < y + sumQ ys.
-- Use: +-monoʳ-≤ x (IH) gives x + sumQ xs < x + sumQ ys
-- Then: +-mono-<-≤ that gives x + sumQ xs < y + sumQ ys needs x < y or...
-- Actually +-mono-<-≤ : a < b → c ≤ d → a + c < b + d
-- Here I want: x + sumQ xs < y + sumQ ys from (x ≤ y) and (sumQ xs < sumQ ys)
-- That's the "sum is ≤-<-< form": use +-mono-≤-< from Properties

sumQStrict : ∀ {xs ys} → StrictAt xs ys → sumQ xs < sumQ ys
sumQStrict (here  {x} {y} x<y hrest) =
  +-mono-<-≤ x<y (sumQMono hrest)
  --  x < y  →  sumQ xs ≤ sumQ ys  →  x + sumQ xs < y + sumQ ys
sumQStrict (there {x} {y} x≤y hrest) =
  Data.Rational.Properties.+-mono-≤-< x≤y (sumQStrict hrest)
  --  x ≤ y  →  sumQ xs < sumQ ys  →  x + sumQ xs < y + sumQ ys
  where open import Data.Rational.Properties using (+-mono-≤-<)


-- ── Expected Value (Counting Form) ───────────────────────────────────────────
--
-- The expected value of f over a finite outcome space is:
--   E[f] = (1/|Ω|) · Σ_{ω ∈ Ω} f(ω)
--
-- Since we are comparing two expectations with the SAME denominator |Ω|,
-- comparing E[f] vs E[g] is equivalent to comparing Σ f vs Σ g.
-- The theorems above (sumQNonNeg, sumQStrict) are therefore the key lemmas
-- for the flagship theorem.
--
-- The denominator is positive (|Ω| > 0), so dividing preserves order direction.
-- We do not expand this further — the flagship theorem works with sums directly.
