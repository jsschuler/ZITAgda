{-# OPTIONS --guardedness #-}
-- Main.agda
-- Executable ZIT simulation with n=3 (4-tick grid, 16 seeds per environment).
-- Two environments are compared side by side:
--
--   witnessEnv:  v_buyer=1, v_seller=2, maxP=3
--     L0 agents draw from the full range {0, 3/4, 3/2, 9/4}.
--     L3 agents: buyer capped at v=1, seller floored at v=2.
--     Since max_L3_bid = 3/4 < 2 = min_L3_ask, L3 never trades.
--     L0 trades whenever bid >= ask → surplus = v_b - v_s = 1-2 = -1.
--     → L3 dominates L0 (avoids value-destroying trades).
--
--   marketEnv:   v_buyer=3, v_seller=1, budget=4, maxP=4
--     L0 draws from {0, 1, 2, 3}.
--     L3 buyer capped at min(3,4)=3, ticks {0, 3/4, 3/2, 9/4}.
--     L3 seller floored at 1, ticks {1, 7/4, 5/2, 13/4}.
--     L3 crosses only 3/16 seeds (bid=9/4 or 3/2 crossing ask=1 or 7/4).
--     L0 crosses 10/16 seeds (bid >= ask in {0,1,2,3}).
--     Both produce surplus = v_b - v_s = 2 when they trade.
--     → L0 trades more often, producing higher total surplus.
--
-- Compile:  agda --compile src/Main.agda
-- Run:      ./Main  (or src/Main)

module Main where

open import IO
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level          using (0ℓ)
open import Data.String    using (String; _++_)
open import Data.Nat       using (ℕ; suc; zero; s≤s; z≤n) renaming (_<_ to _<ℕ_)
open import Data.Nat.Show  renaming (show to showℕ)
open import Data.Integer   using (+_)
open import Data.Rational  using (ℚ; _/_; _⊓_; _≤_; 0ℚ; 1ℚ)
open import Data.Rational.Properties using (_≤?_)
open import Data.Rational.Show renaming (show to showℚ)
open import Data.Fin       using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Vec       using (Vec) renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List      using (List; []; _∷_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (toWitness)
open import Data.Unit      using () renaming (tt to tt0)

open import Agent
open import Seed             using (Seed; drawAt)
open import L0AgentStrategy  using (concreteL0Sim; witnessEnv; l0Tick)
open import FlagshipFull     using (concreteSim; SimEnvironment)
open import SimulationModel  using (l0RealizedSurplus)
open import Trace            using (realizedSurplus)


-- ── Rational literals ─────────────────────────────────────────────────────────

private
  2ℚ 3ℚ 4ℚ : ℚ
  2ℚ = (+ 2) / 1
  3ℚ = (+ 3) / 1
  4ℚ = (+ 4) / 1


-- ── Market environment ────────────────────────────────────────────────────────
--
-- A second environment where v_buyer > v_seller: trades ARE socially efficient.
-- The buyer values the good at 3, the seller's cost is 1, surplus per trade = 2.
-- maxP = 4 (above buyer's valuation — L0 agents can bid above their own value).
--
-- Under L3: the buyer's L3 grid is capped at min(v,b)=3, seller floored at v=1.
--   L3 buyer bids  ∈ { 0,  3/4,  3/2,  9/4 }  (ticks of [0, 3])
--   L3 seller asks ∈ { 1,  7/4,  5/2, 13/4 }  (ticks of [1, 4])
--   Crossings: (bid=9/4, ask=1), (bid=9/4, ask=7/4), (bid=3/2, ask=1)
--   → 3 of 16 seeds produce L3 trades.
--
-- Under L0: both agents draw from the full grid { 0, 1, 2, 3 } (ticks of [0,4]).
--   Crossing whenever bid >= ask (i_buyer >= i_seller in {0,1,2,3}).
--   → 10 of 16 seeds produce L0 trades.
--
-- Surprise: L0 total surplus (10×2=20) > L3 total surplus (3×2=6).
-- This shows that the flagship theorem does NOT hold in all environments —
-- it depends on the distribution of market conditions.
-- In environments with productive trades (v_b > v_s), L3's constraints
-- PREVENT some efficient trades, hurting total surplus relative to L0.

marketBuyer : Agent
marketBuyer = record
  { id        = 2
  ; role      = Buyer
  ; valuation = record { unitValue = 3ℚ }
  ; budget    = 4ℚ
  ; inventory = 0
  }

marketSeller : Agent
marketSeller = record
  { id        = 3
  ; role      = Seller
  ; valuation = record { unitValue = 1ℚ }
  ; budget    = 0ℚ
  ; inventory = 1
  }

marketEnv : SimEnvironment
marketEnv = record
  { buyer   = marketBuyer
  ; seller  = marketSeller
  ; maxP    = 4ℚ
  ; cap≥0   = toWitness
               {a? = 0ℚ ≤? (ValuationSchedule.unitValue (Agent.valuation marketBuyer)
                            ⊓ Agent.budget marketBuyer)}
               tt0
  ; v≤maxP  = toWitness
               {a? = ValuationSchedule.unitValue (Agent.valuation marketSeller) ≤? 4ℚ}
               tt0
  ; hasInv  = s≤s z≤n
  }


-- ── Fin 4 abbreviations ───────────────────────────────────────────────────────

private
  f0 f1 f2 f3 : Fin 4
  f0 = fzero
  f1 = fsuc fzero
  f2 = fsuc (fsuc fzero)
  f3 = fsuc (fsuc (fsuc fzero))


-- ── All 16 seeds for Seed 4 2 ─────────────────────────────────────────────────
--
-- Seed 4 2 = Vec (Fin 4) 2 — two draws from a 4-element grid.
-- The first draw is the buyer's price index, second is the seller's.
-- There are 4^2 = 16 seeds.

allSeeds4 : List (Seed 4 2)
allSeeds4 =
  (f0 v∷ f0 v∷ v[]) ∷ (f0 v∷ f1 v∷ v[]) ∷ (f0 v∷ f2 v∷ v[]) ∷ (f0 v∷ f3 v∷ v[]) ∷
  (f1 v∷ f0 v∷ v[]) ∷ (f1 v∷ f1 v∷ v[]) ∷ (f1 v∷ f2 v∷ v[]) ∷ (f1 v∷ f3 v∷ v[]) ∷
  (f2 v∷ f0 v∷ v[]) ∷ (f2 v∷ f1 v∷ v[]) ∷ (f2 v∷ f2 v∷ v[]) ∷ (f2 v∷ f3 v∷ v[]) ∷
  (f3 v∷ f0 v∷ v[]) ∷ (f3 v∷ f1 v∷ v[]) ∷ (f3 v∷ f2 v∷ v[]) ∷ (f3 v∷ f3 v∷ v[]) ∷
  []


-- ── Simulation row ────────────────────────────────────────────────────────────
--
-- Print one row: seed indices, L0 bid/ask prices, L0 surplus, L3 surplus.
-- The env parameter determines which environment to simulate.
-- The n=3 instantiation fixes the 4-tick grid.

simRow : SimEnvironment → Seed 4 2 → IO {0ℓ} ⊤
simRow env s =
  let maxP  = SimEnvironment.maxP env
      ib    = toℕ (drawAt s fzero)
      is    = toℕ (drawAt s (fsuc fzero))
      bidP  = l0Tick 3 maxP (drawAt s fzero)
      askP  = l0Tick 3 maxP (drawAt s (fsuc fzero))
      l0sur = l0RealizedSurplus (concreteL0Sim {3} env s)
      l3sur = realizedSurplus   (concreteSim   {3} env s)
  in putStrLn ("  [" ++ showℕ ib ++ "," ++ showℕ is ++ "]"
             ++ "  bid=" ++ showℚ bidP
             ++ "  ask=" ++ showℚ askP
             ++ "  L0=" ++ showℚ l0sur
             ++ "  L3=" ++ showℚ l3sur)


-- ── Print all seeds for one environment ───────────────────────────────────────

printAll : SimEnvironment → List (Seed 4 2) → IO {0ℓ} ⊤
printAll _   []       = pure tt
printAll env (s ∷ ss) = simRow env s >> printAll env ss


-- ── Main ──────────────────────────────────────────────────────────────────────

program : IO {0ℓ} ⊤
program =
  -- Witness environment: v_buyer < v_seller
  putStrLn "=== Environment 1: witness (v_buyer=1, v_seller=2, maxP=3) ===" >>
  putStrLn "  L0 bid/ask from full grid {0, 3/4, 3/2, 9/4}" >>
  putStrLn "  L3 buyer bids in {0, 1/4, 1/2, 3/4}  (cap at v=1)" >>
  putStrLn "  L3 seller asks in {2, 9/4, 5/2, 11/4} (floor at v=2)" >>
  putStrLn "  Result: L3 never trades; L0 trades and destroys value" >>
  putStrLn "" >>
  putStrLn "  seed  bid     ask     L0       L3" >>
  printAll witnessEnv allSeeds4 >>
  putStrLn "" >>

  -- Market environment: v_buyer > v_seller
  putStrLn "=== Environment 2: market (v_buyer=3, v_seller=1, maxP=4) ===" >>
  putStrLn "  L0 bid/ask from full grid {0, 1, 2, 3}" >>
  putStrLn "  L3 buyer bids in {0, 3/4, 3/2, 9/4}    (cap at v=3)" >>
  putStrLn "  L3 seller asks in {1, 7/4, 5/2, 13/4}  (floor at v=1)" >>
  putStrLn "  Result: L3 trades at 3/16 seeds; L0 trades at 10/16 seeds" >>
  putStrLn "" >>
  putStrLn "  seed  bid     ask     L0       L3" >>
  printAll marketEnv allSeeds4

main : Main
main = run program
