-- Stochastic.agda
-- First-order stochastic dominance for the ZIT simulation.
--
-- We define discrete probability via counting over a finite list of outcomes
-- (the seed space Ω), then prove that in environments where v_buyer ≤ v_seller,
-- the L3 surplus distribution first-order stochastically dominates the L0
-- surplus distribution.
--
-- DEFINITIONS.
--   survivalCount f Ω t  =  |{ s ∈ Ω : f(s) ≥ t }|
--   FSDom f g Ω          =  ∀ t, survivalCount g Ω t ≤ survivalCount f Ω t
--   (read: "f first-order stochastically dominates g over Ω")
--
-- KEY THEOREM (l3FSDom-l0-inverted).
-- In any environment with v_buyer ≤ v_seller (an "inverted" or loss-making market),
-- the L3 surplus distribution FSD-dominates the L0 surplus distribution over any
-- finite seed population Ω.
--
-- PROOF STRATEGY.
-- FSD follows from pointwise dominance (FSD-from-pointwise):
--   ∀ s, L0(s) ≤ 0     [l0Nonpos-inverted: L0 trades destroy value in inverted markets]
--   ∀ s, 0 ≤ L3(s)     [realizedSurplusNonNeg: L3 structural guarantee]
-- Combining: ∀ s, L0(s) ≤ L3(s).  Pointwise dominance → FSD. ✓
--
-- ECONOMIC INTERPRETATION.
-- In the witnessEnv (v_buyer=1, v_seller=2), L0 destroys value (surplus = -1)
-- whenever it trades, while L3 structurally prevents such trades (surplus = 0).
-- The FSD result says: for ANY threshold t, the L3 distribution puts at least as
-- much probability mass above t as L0 does.  In particular, E[L3] ≥ E[L0].
--
-- This is strictly stronger than the pointwise flagship theorem (Theorem 6),
-- which only shows ∃ s where L3 > L0.  FSD is a full distributional comparison.
--
-- New Agda ideas:
--   isYes        — Bool from Dec by pattern matching (isYes (no _) = false reduces ✓)
--   filter-mono  — if predicate p₂ implies p₁ (bool-wise), then
--                  |filter p₂ xs| ≤ |filter p₁ xs|
--   with e in h  — pattern match on e and bind the equation h : e ≡ pat
--   _∘_          — function composition (f ∘ g) x = f (g x)

module Stochastic where

open import Data.Nat       using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Rational  using (ℚ; _≤_; 0ℚ; _⊓_)
import Data.Rational.Properties as ℚP
open import Data.Bool      using (Bool; true; false; T)
open import Data.Unit      using (⊤; tt)
open import Data.Empty     using (⊥; ⊥-elim)
open import Data.List      using (List; []; _∷_; filterᵇ; length; map)
open import Relation.Nullary using (yes; no; isYes)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)
open import Function       using (_∘_)

open import Agent
open import Seed           using (Seed)
open import SimulationModel using (l0RealizedSurplus)
open import L0AgentStrategy using (concreteL0Sim; l0Nonpos-inverted; l0Nonneg-productive; l3LE-l0-productive)
open import FlagshipFull   using (SimEnvironment; concreteSim)
open import Trace          using (realizedSurplus; realizedSurplusNonNeg)
open import Probability    using (sumQ)


-- ── Survival Count ────────────────────────────────────────────────────────────
--
-- survivalCount f Ω t counts how many seeds s ∈ Ω have f(s) ≥ t.
-- This is the empirical upper CDF (survival function) scaled by |Ω|.
--
-- The predicate  λ s → isYes (t ≤? f s)  encodes "t ≤ f(s)" as a Bool:
--   _≤?_ : Dec (t ≤ f s)    — decidable comparison, from Data.Rational.Properties
--   isYes : Dec P → Bool     — yes p ↦ true,  no q ↦ false (by pattern matching)
-- filter retains exactly those s where f(s) ≥ t.
--
-- In Julia: count(s -> t ≤ f(s), Ω)
-- In probability theory: N · P̂(f ≥ t) where P̂ is the empirical measure

survivalCount : {S : Set} → (S → ℚ) → List S → ℚ → ℕ
survivalCount f xs t = length (filterᵇ (λ s → isYes (ℚP._≤?_ t (f s))) xs)


-- ── First-Order Stochastic Dominance ─────────────────────────────────────────
--
-- f FSD-dominates g over Ω means: for every threshold t,
-- at least as many seeds produce f(s) ≥ t as produce g(s) ≥ t.
--
-- FSDom f g Ω  =  ∀ t, survivalCount g Ω t ≤ survivalCount f Ω t
--
-- In economic language: any agent with a monotone utility function (more is
-- better) weakly prefers the f-lottery to the g-lottery.
--
-- Note: survivalCount uses ℕ._≤_ (we renamed it to _≤ℕ_), not ℚ._≤_.

FSDom : {S : Set} → (S → ℚ) → (S → ℚ) → List S → Set
FSDom {S} f g Ω = ∀ (t : ℚ) → survivalCount g Ω t ≤ℕ survivalCount f Ω t


-- ── Private Helpers ───────────────────────────────────────────────────────────

private

  -- T : Bool → Set  is the "truth-value" coercion:
  --   T true  = ⊤   (the unit type, trivially inhabited)
  --   T false = ⊥   (the empty type, uninhabited)
  -- If false ≡ true, then T false = ⊥ is inhabited by:
  --   subst T (sym h) tt  :  T false
  -- because sym h : true ≡ false, and tt : T true = ⊤.
  -- Substituting true ↦ false in the type gives T false = ⊥. QED.
  --
  -- In Julia: you'd test this with an assertion; in Agda it's a proof term.
  bool-false≡true : false ≡ true → ⊥
  bool-false≡true h = subst T (sym h) tt

  -- filter-grows: prepending x to xs can only increase the filter count.
  -- When p x = true,  x is included → count increases by exactly 1.
  -- When p x = false, x is excluded → count stays the same.
  --
  -- In Julia: the list grows by at most 1 when we add one element.
  -- filter-mono: if predicate q implies predicate p (as Bool functions),
  -- then the filterᵇ-p list is at least as long as the filterᵇ-q list.
  --
  -- Proof by induction on xs, case-splitting on both (p x) and (q x).
  -- We split on p x FIRST so that filterᵇ p (x ∷ xs) reduces in the goal:
  --   p x = false → filterᵇ p (x ∷ xs) = filterᵇ p xs        (x skipped)
  --   p x = true  → filterᵇ p (x ∷ xs) = x ∷ filterᵇ p xs    (x kept)
  --
  -- (p x = false, q x = false) → both skip x, reduce to IH.
  -- (p x = false, q x = true)  → contradicts sub (p must agree with q). ⊥-elim.
  -- (p x = true,  q x = false) → p grows by 1, q stays same: IH + m≤n⇒m≤1+n.
  -- (p x = true,  q x = true)  → both include x: s≤s IH.

  filter-mono : {A : Set} (p q : A → Bool) (xs : List A)
    → (∀ x → q x ≡ true → p x ≡ true)
    → length (filterᵇ q xs) ≤ℕ length (filterᵇ p xs)
  filter-mono p q []       _   = z≤n
  filter-mono p q (x ∷ xs) sub with p x in hp | q x in hq
  ... | false | false = filter-mono p q xs sub
  ... | false | true  = ⊥-elim (bool-false≡true (trans (sym hp) (sub x hq)))
  ... | true  | false = ℕP.m≤n⇒m≤1+n (filter-mono p q xs sub)
  ... | true  | true  = s≤s (filter-mono p q xs sub)




-- ── FSD from Pointwise Dominance ─────────────────────────────────────────────
--
-- THEOREM (FSD-from-pointwise).
-- If g(s) ≤ f(s) for every s ∈ Ω, then f FSD-dominates g over Ω.
--
-- PROOF.
-- Fix a threshold t. We need |filter (t ≤? g) Ω| ≤ |filter (t ≤? f) Ω|.
-- By filter-mono, it suffices to show the implication:
--   ∀ s, does (t ≤? g s) = true  →  does (t ≤? f s) = true.
-- Unfolding "does ... = true":  t ≤ g(s)  →  t ≤ f(s).
-- This holds by transitivity:  t ≤ g(s) ≤ f(s)  (using pw s : g(s) ≤ f(s)).  ✓
--
-- MATHEMATICAL NOTE.
-- This is the standard proof that pointwise dominance implies FSD.
-- In measure theory: the pushforward measure of f dominates that of g in FSD.
-- Here we work combinatorially (counting seeds), avoiding all measure theory.

FSD-from-pointwise
  : {S : Set} (f g : S → ℚ) (Ω : List S)
  → (∀ s → g s ≤ f s)
  → FSDom f g Ω
FSD-from-pointwise f g Ω pw t =
  filter-mono
    (λ s → isYes (ℚP._≤?_ t (f s)))
    (λ s → isYes (ℚP._≤?_ t (g s)))
    Ω
    step
  where
    -- step: if t ≤ g(s), then t ≤ f(s).
    -- "isYes (t ≤? g s) = true" means t ≤ g s.
    -- isYes uses pattern matching (not a field), so isYes (no _) reduces to false. ✓
    -- We use transitivity: t ≤ g s ≤ f s.
    step : ∀ s → isYes (ℚP._≤?_ t (g s)) ≡ true
                → isYes (ℚP._≤?_ t (f s)) ≡ true
    step s h with ℚP._≤?_ t (g s)
    ... | no  _   = ⊥-elim (bool-false≡true h)
    ... | yes tgs with ℚP._≤?_ t (f s)
    ...   | yes _ = refl
    ...   | no tfs = ⊥-elim (tfs (ℚP.≤-trans tgs (pw s)))


-- ── Main Theorem: L3 FSD-Dominates L0 in Inverted Markets ────────────────────
--
-- THEOREM (l3FSDom-l0-inverted).
-- For any environment with v_buyer ≤ v_seller and any seed population Ω,
-- the L3 surplus distribution first-order stochastically dominates
-- the L0 surplus distribution:
--
--   FSDom (realizedSurplus ∘ concreteSim env)
--          (l0RealizedSurplus ∘ concreteL0Sim env)
--          Ω
--
-- PROOF.
-- By FSD-from-pointwise it suffices to show:
--   ∀ s, l0RealizedSurplus (concreteL0Sim env s)
--          ≤ realizedSurplus (concreteSim env s)
-- Proof of pointwise bound: by ≤-trans on
--   L0(s) ≤ 0   [l0Nonpos-inverted]
--   0 ≤ L3(s)   [realizedSurplusNonNeg]
--
-- This completes the stochastic analysis of the ZIT flagship in inverted markets.
-- In normal markets (v_buyer ≥ v_seller), the inequality direction flips:
-- L0 trades more often, producing higher total surplus, and L0 FSD-dominates L3.
-- The simulation (Main.agda) demonstrates both cases concretely.

l3FSDom-l0-inverted
  : ∀ {n} (env : SimEnvironment)
  → ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))
    ≤ ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))
  → (Ω : List (Seed (suc n) 2))
  → FSDom (realizedSurplus   ∘ concreteSim    {n} env)
          (l0RealizedSurplus ∘ concreteL0Sim  {n} env)
          Ω
l3FSDom-l0-inverted {n} env h Ω =
  FSD-from-pointwise _ _ Ω
    (λ s → ℚP.≤-trans
              (l0Nonpos-inverted {n} env s h)
              (realizedSurplusNonNeg (concreteSim {n} env s)))


-- ── Expected Value Dominance ──────────────────────────────────────────────────
--
-- THEOREM (l3Expected-l0-inverted).
-- In any inverted market (v_b ≤ v_s), for any seed population Ω,
-- the total L3 surplus is at least the total L0 surplus:
--
--   Σ_{s ∈ Ω} L0(s)  ≤  Σ_{s ∈ Ω} L3(s)
--
-- Since both sides share the same denominator |Ω|, this is equivalent to
-- E[L3 surplus] ≥ E[L0 surplus].
--
-- PROOF. By sumQ-map-mono applied to the pointwise bound:
--   ∀ s, L0(s) ≤ 0 ≤ L3(s)   [l0Nonpos-inverted + realizedSurplusNonNeg]
--
-- RELATIONSHIP TO FSD.
-- Both l3FSDom-l0-inverted (FSD) and l3Expected-l0-inverted (expected value)
-- derive from the same pointwise ingredient. FSD is the stronger result:
-- E[f] ≥ E[g] follows from FSDom f g, but not conversely. Here we derive both
-- directly from pointwise dominance rather than chaining through FSD.

private
  -- If g(s) ≤ f(s) for every s, then the sum of g-values ≤ sum of f-values.
  -- Proof: induction on the list, applying +-mono-≤ at each step.
  sumQ-map-mono
    : {S : Set} (f g : S → ℚ) (xs : List S)
    → (∀ s → g s ≤ f s)
    → sumQ (map g xs) ≤ sumQ (map f xs)
  sumQ-map-mono f g []       _  = ℚP.≤-refl
  sumQ-map-mono f g (x ∷ xs) pw =
    ℚP.+-mono-≤ (pw x) (sumQ-map-mono f g xs pw)

l3Expected-l0-inverted
  : ∀ {n} (env : SimEnvironment)
  → ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))
    ≤ ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))
  → (Ω : List (Seed (suc n) 2))
  → sumQ (map (l0RealizedSurplus ∘ concreteL0Sim {n} env) Ω)
    ≤ sumQ (map (realizedSurplus   ∘ concreteSim  {n} env) Ω)
l3Expected-l0-inverted {n} env h Ω =
  sumQ-map-mono _ _ Ω
    (λ s → ℚP.≤-trans
              (l0Nonpos-inverted {n} env s h)
              (realizedSurplusNonNeg (concreteSim {n} env s)))


-- ── L0 FSD-Dominates L3 in Productive Markets ─────────────────────────────────
--
-- THEOREM (l0FSDom-l3-productive).
-- In any environment with v_s ≤ v_b (productive market), for any seed population Ω,
-- the L0 surplus distribution first-order stochastically dominates
-- the L3 surplus distribution:
--
--   FSDom (l0RealizedSurplus ∘ concreteL0Sim env)
--          (realizedSurplus   ∘ concreteSim  env)
--          Ω
--
-- PROOF. By FSD-from-pointwise, using l3LE-l0-productive (proved in L0AgentStrategy):
--   ∀ s, L3(s) ≤ L0(s)   in productive markets.
--
-- HYPOTHESES (in addition to SimEnvironment's fields):
--   hVS  : 0 ≤ v_s          — non-negative seller valuation
--   hProd: v_s ≤ v_b         — productive market (L0 dominates)
--   hCap : cap ≤ maxP        — buyer effective cap ≤ market ceiling
--
-- ECONOMIC INTERPRETATION.
-- In productive markets (v_b > v_s), the L3 constraint prevents many trades
-- (it forces buyer bids ≤ v_b and seller asks ≥ v_s, a tighter range than L0).
-- L0 trades whenever bid ≥ ask on the full grid; L3 trades less often.
-- When both trade they earn the same v_b - v_s. When only L0 trades, L0 earns
-- more. This is the symmetric counterpart of l3FSDom-l0-inverted.

l0FSDom-l3-productive
  : ∀ {n} (env : SimEnvironment)
  → 0ℚ ≤ ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))
  → ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))
    ≤ ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))
  → (  ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))
     ⊓ Agent.budget (SimEnvironment.buyer env))
    ≤ SimEnvironment.maxP env
  → (Ω : List (Seed (suc n) 2))
  → FSDom (l0RealizedSurplus ∘ concreteL0Sim {n} env)
          (realizedSurplus   ∘ concreteSim  {n} env)
          Ω
l0FSDom-l3-productive {n} env hVS hProd hCap Ω =
  FSD-from-pointwise _ _ Ω
    (λ s → l3LE-l0-productive {n} env s hVS hProd hCap)
