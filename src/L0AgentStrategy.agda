-- L0AgentStrategy.agda
-- Concrete L0 (unconstrained) simulation with a negative-surplus witness.
--
-- L0 agents are zero-intelligence WITHOUT the L3 constraint:
-- they draw prices uniformly from the full market range [0, maxP),
-- regardless of their own valuation or budget.
-- A buyer can bid ABOVE their valuation; a seller can ask BELOW their cost.
-- The institution checks only if bid ≥ ask, and trades at the ask price.
-- No BuyerAdmissible or SellerAdmissible evidence is produced.
--
-- This module provides:
--   l0Tick         — full-range price function (analogous to buyerTick/sellerTick)
--   tryL0Match     — attempt a RawMatch from unconstrained bid/ask prices
--   concreteL0Sim  — SimFnL0 using unconstrained strategies
--   witnessEnv     — concrete SimEnvironment with buyerWitness / sellerWitness
--   witnessSeed    — concrete Seed 2 2 that produces a crossing
--   witnessSeedNegSurplus — proof that l0RealizedSurplus is negative at the witness
--   witnessForFlagship    — the Σ-witness enabling concretePointwiseFlagship
--
-- Economic interpretation:
--   Under L0, the buyer (val=1) bids above valuation and the seller (val=2) asks
--   below cost, so they cross. The trade "happens" at a good price for both
--   in terms of market mechanics, yet the social surplus is negative:
--     rawSurplus = v_buyer - v_seller = 1 - 2 = -1 < 0.
--   This is the value-destroying trade that L3 structurally eliminates.
--
-- Connecting to the flagship:
--   witnessSeedNegSurplus hands the Σ-witness to concretePointwiseFlagship
--   (in FlagshipFull.agda), completing the argument that ∃ seed where L3 > L0.
--
-- New Agda ideas:
--   renaming constructors — "open import M renaming ([] to v[])" lets you avoid
--     name clashes when both List and Vec use [] and _∷_
--   explicit implicit arguments — {n} can be given explicitly as {1} at a call site
--     to help Agda resolve unification in complex expressions

module L0AgentStrategy where

open import Data.Nat      using (ℕ; suc; zero; s≤s; z≤n) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Data.Fin      using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Rational using (ℚ; _*_; _-_; _≤_; _<_; 0ℚ; _/_; _⊓_; -_)
open import Data.Rational.Properties
  using (_≤?_; _<?_; ≤-refl; ≤-trans; ≤-reflexive; +-identityʳ; +-inverseʳ; +-monoˡ-≤)
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Integer  using (+_)
open import Data.List     using (List; []; _∷_)
open import Data.Maybe    using (Maybe; just; nothing)
open import Data.Product  using (Σ; _,_)
open import Data.Vec      using (Vec) renaming ([] to v[]; _∷_ to _v∷_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (toWitness)
open import Data.Unit using (tt)

open import Agent
open import Proposal
open import Seed          using (Seed; drawAt)
open import PriceGrid     using (ratio)
open import Flagship      using (RawMatch; rawSurplus; buyerWitness; sellerWitness)
open import SimulationModel using (SimFnL0; l0RealizedSurplus)
open import FlagshipFull  using (SimEnvironment)


-- ── L0 Price Tick ─────────────────────────────────────────────────────────────
--
-- l0Tick n maxP i  =  maxP * (toℕ i / suc n)
--
-- This is the UNCONSTRAINED analog of buyerTick and sellerTick.
-- The full market range [0, maxP) is available to any agent, regardless of
-- their valuation or budget.  Compare:
--
--   buyerTick  n v b   i  =  (v ⊓ b)  *  ratio n i  ← capped at min(v,b)
--   sellerTick n v maxP i  =   v  +  (maxP-v)  *  ratio n i  ← floored at v
--   l0Tick     n maxP   i  =  maxP  *  ratio n i              ← no constraint
--
-- In Julia:  p = maxP * (i / (n+1))  with no bounds check on the agent side.
-- An L0 buyer could draw i = n (highest) and bid maxP*(n/(n+1)) ≈ maxP,
-- far above their own valuation.  An L0 seller could draw i = 0 and ask 0ℚ,
-- far below their cost.

l0Tick : (n : ℕ) → (maxP : ℚ) → Fin (suc n) → ℚ
l0Tick n maxP i = maxP * ratio n i


-- ── Try L0 Match ──────────────────────────────────────────────────────────────
--
-- Given a buyer, their L0 bid price, a seller, and their L0 ask price,
-- return Just m (a RawMatch) if the proposals cross (ask ≤ bid), else Nothing.
--
-- The clearing price is set to the ask price — same convention as tryMatch
-- in BatchAuction.agda.  The priceInRange proof:
--   fst : ask ≤ clearingPrice = ask ≤ ask  → ≤-refl
--   snd : clearingPrice ≤ bid = ask ≤ bid  → crosses
--
-- CONTRAST with tryMatch in BatchAuction:
--   tryMatch  inputs CertifiedBid / CertifiedAsk   →  certified Match
--   tryL0Match inputs plain Agent + ℚ price        →  uncertified RawMatch
--
-- The output RawMatch has no BuyerAdmissible or SellerAdmissible fields.
-- This is the formal encoding of "no L3 constraint": the absence of
-- proof fields IS the absence of the constraint.

tryL0Match : Agent → ℚ → Agent → ℚ → Maybe RawMatch
tryL0Match buyer bidP seller askP
  with askP ≤? bidP
... | yes crosses = just record
      { buyer         = buyer
      ; seller        = seller
      ; bid           = record { proposer = Agent.id buyer  ; price = bidP ; role = Buyer  }
      ; ask           = record { proposer = Agent.id seller ; price = askP ; role = Seller }
      ; crosses       = crosses
      ; clearingPrice = askP
      ; priceInRange  = ≤-refl , crosses
      }
... | no  _       = nothing


-- ── Maybe → List helper ───────────────────────────────────────────────────────

private
  fromMaybe : ∀ {A : Set} → Maybe A → List A
  fromMaybe nothing  = []
  fromMaybe (just x) = x ∷ []


-- ── Run L0 Matches ────────────────────────────────────────────────────────────
--
-- Given a SimEnvironment and a 2-draw seed:
--   draw 0  → buyer's price index   → l0Tick n maxP → bidP
--   draw 1  → seller's price index  → l0Tick n maxP → askP
--
-- Both agents draw from the FULL range [0, maxP).
-- The buyer ignores their own valuation and budget.
-- The seller ignores their own cost.
-- If askP ≤ bidP, a RawMatch is produced; otherwise the list is empty.
--
-- In Julia: this is a function of the form
--   runL0(env, seed) = tryRawMatch(env.buyer, l0Price(env.maxP, seed[1]),
--                                   env.seller, l0Price(env.maxP, seed[2]))
-- The only difference: in Agda, the function is TOTAL and the types track
-- whether a match happened (List with 0 or 1 elements, not a nullable ref).

runL0Matches : ∀ {n} → SimEnvironment → Seed (suc n) 2 → List RawMatch
runL0Matches {n} env s = fromMaybe (tryL0Match buyer bidP seller askP)
  where
    open SimEnvironment env
    i_b  = drawAt s fzero
    i_s  = drawAt s (fsuc fzero)
    bidP = l0Tick n maxP i_b
    askP = l0Tick n maxP i_s


-- ── Concrete L0 Simulation ────────────────────────────────────────────────────
--
-- concreteL0Sim env : SimFnL0 (suc n) 2
--
-- SimFnL0 (suc n) 2 = Seed (suc n) 2 → List RawMatch
--
-- This is the L0 counterpart of concreteSim in FlagshipFull.agda.
-- The TYPE says it is a valid SimFnL0 — the abstract flagship theorems apply.
--
-- Compare:
--   concreteSim   env : SimFnL3 (suc n) 2  ← produces certified Traces
--   concreteL0Sim env : SimFnL0 (suc n) 2  ← produces uncertified RawMatches
--
-- The asymmetry: concreteSim uses CertifiedBid/CertifiedAsk (L3 evidence);
-- concreteL0Sim uses plain prices (no evidence).  The return types differ
-- in exactly this way: Trace (has Match, which has admissibility proofs) vs
-- List RawMatch (no admissibility proofs).

concreteL0Sim : ∀ {n} → SimEnvironment → SimFnL0 (suc n) 2
concreteL0Sim env = λ s → runL0Matches env s


-- ── Witness Definitions ───────────────────────────────────────────────────────
--
-- Private rational literals needed for the witness environment.

private
  2ℚ : ℚ
  2ℚ = (+ 2) / 1

  3ℚ : ℚ
  3ℚ = (+ 3) / 1


-- ── Witness Environment ───────────────────────────────────────────────────────
--
-- The witness environment uses buyerWitness and sellerWitness from Flagship.agda:
--   buyerWitness  : val = 1ℚ,  budget = 3ℚ
--   sellerWitness : val = 2ℚ,  inventory = 1
--   maxP          = 3ℚ
--
-- The KEY FACT: v_buyer = 1 < 2 = v_seller.
-- Therefore rawSurplus = v_buyer - v_seller = 1 - 2 = -1 < 0
-- for ANY match involving these two agents, regardless of what prices they draw.
-- This is the value-destroying scenario that L3 structurally prevents.
--
-- The three proof fields of SimEnvironment are all trivially satisfied:
--
--   cap≥0  : 0 ≤ val_buyer ⊓ budget_buyer
--           = 0 ≤ 1ℚ ⊓ 3ℚ = 0 ≤ 1ℚ          ✓ (proved by computation)
--
--   v≤maxP : val_seller ≤ maxP
--           = 2ℚ ≤ 3ℚ                         ✓ (proved by computation)
--
--   hasInv : 0 <ℕ inventory sellerWitness
--           = 0 <ℕ 1                           ✓ (s≤s z≤n)
--
-- The L0 simulation does NOT USE these proofs — they live in SimEnvironment
-- so that the same environment record can be used for both L3 and L0 sims
-- (enabling direct comparison via concretePointwiseFlagship).

witnessEnv : SimEnvironment
witnessEnv = record
  { buyer   = buyerWitness
  ; seller  = sellerWitness
  ; maxP    = 3ℚ
  ; cap≥0   = toWitness
               {a? = 0ℚ ≤? ( ValuationSchedule.unitValue (Agent.valuation buyerWitness)
                             ⊓ Agent.budget buyerWitness)}
               tt
  ; v≤maxP  = toWitness
               {a? = ValuationSchedule.unitValue (Agent.valuation sellerWitness) ≤? 3ℚ}
               tt
  ; hasInv  = s≤s z≤n   -- proof that 0 < 1 : suc 0 ≤ suc 0
  }


-- ── Witness Seed ─────────────────────────────────────────────────────────────
--
-- witnessSeed : Seed 2 2 = Vec (Fin 2) 2
--
-- A concrete 2-draw tape for a 2-tick grid (n=1, so suc n = 2).
-- Draw 0 = fsuc fzero (index 1 — the HIGH end of the buyer's range)
-- Draw 1 = fzero      (index 0 — the LOW  end of the seller's range)
--
-- Result:
--   bidP = l0Tick 1 3ℚ (fsuc fzero) = 3ℚ * (1/2) = 3/2
--   askP = l0Tick 1 3ℚ fzero        = 3ℚ * (0/2) = 0ℚ
--
-- Crossing check: 0ℚ ≤ 3/2  ✓  → a RawMatch is produced.
-- Raw surplus: v_buyer - v_seller = 1ℚ - 2ℚ = -1ℚ < 0ℚ  ✓
--
-- In Julia: witnessSeed = [Fin(2,2), Fin(2,1)] (second element, first element)
-- using 1-indexed Fin.  In Agda, Fin is 0-indexed (zero, suc zero = index 0, 1).
--
-- Note: the Vec constructor _v∷_ is _∷_ from Data.Vec, renamed here to avoid
-- ambiguity with List._∷_.  The type annotation Seed 2 2 forces Agda to pick
-- the Vec interpretation anyway, but the renaming makes it syntactically unambiguous.

witnessSeed : Seed 2 2
witnessSeed = (fsuc fzero) v∷ fzero v∷ v[]


-- ── Witness: Negative Surplus ─────────────────────────────────────────────────
--
-- THEOREM (L0 Negative Surplus).
-- l0RealizedSurplus (concreteL0Sim witnessEnv witnessSeed) < 0ℚ
--
-- PROOF.
--   Evaluate the chain:
--     drawAt witnessSeed fzero       = fsuc fzero   (buyer's index)
--     drawAt witnessSeed (fsuc fzero) = fzero        (seller's index)
--     bidP = l0Tick 1 3ℚ (fsuc fzero) = 3ℚ * 1/2 = 3/2
--     askP = l0Tick 1 3ℚ fzero        = 3ℚ * 0/2 = 0ℚ
--     askP ≤? bidP = 0ℚ ≤? 3/2 = yes (0 * 2 ≤ 3 * 1 = 0 ≤ 3)
--     tryL0Match → just m
--     rawSurplus m = v_buyer - v_seller = 1ℚ - 2ℚ = -1ℚ
--     l0RealizedSurplus [m] = sumQ [-1ℚ] = -1ℚ + 0ℚ = -1ℚ
--     -1ℚ <? 0ℚ = yes (−1 * 1 < 0 * 1 = −1 < 0)  ✓
-- All steps reduce to concrete rational arithmetic.
-- Agda evaluates the decision procedure at compile time; toWitness extracts
-- the proof from the yes branch.

witnessSeedNegSurplus
  : l0RealizedSurplus (concreteL0Sim {1} witnessEnv witnessSeed) < 0ℚ
witnessSeedNegSurplus =
  toWitness {a? = l0RealizedSurplus (concreteL0Sim {1} witnessEnv witnessSeed) <? 0ℚ} tt


-- ── Full Flagship Witness ─────────────────────────────────────────────────────
--
-- The Σ-type  Σ (Seed 2 2) (λ s₀ → l0RealizedSurplus (concreteL0Sim env s₀) < 0ℚ)
-- is the EXISTENTIAL STATEMENT: there exists a seed where the L0 surplus is negative.
--
-- This is exactly the hypothesis required by flagshipPointwise (SimulationModel.agda)
-- and by concretePointwiseFlagship (FlagshipFull.agda).
--
-- Applying concretePointwiseFlagship:
--   concretePointwiseFlagship witnessEnv (concreteL0Sim {1} witnessEnv) witnessForFlagship
--   : Σ (Seed 2 2) (λ s₀ → l0RealizedSurplus (concreteL0Sim {1} witnessEnv s₀)
--                          < realizedSurplus   (concreteSim {1} witnessEnv s₀))
--
-- In words: there EXISTS a seed (namely witnessSeed) at which the L3 simulation
-- produces strictly more surplus than the L0 simulation.
-- The L3 simulation at that seed trades only if v_buyer ≥ v_seller (which fails
-- for witnessEnv — no trade occurs, surplus = 0); the L0 simulation DOES trade
-- (bid 3/2 > ask 0, so they cross) and produces -1ℚ surplus.
-- 0 > -1, so L3 surplus > L0 surplus at this seed.  QED.

witnessForFlagship
  : Σ (Seed 2 2) (λ s₀ → l0RealizedSurplus (concreteL0Sim {1} witnessEnv s₀) < 0ℚ)
witnessForFlagship = witnessSeed , witnessSeedNegSurplus


-- ── L0 Surplus Non-Positive in Inverted Markets ───────────────────────────────
--
-- THEOREM (l0Nonpos-inverted).
-- In any environment where v_buyer ≤ v_seller, the L0 realized surplus is ≤ 0
-- at every seed.
--
-- PROOF.
-- Case nothing: no trade occurs, surplus = 0 ≤ 0. ✓
-- Case just m:  trade occurs. The match carries buyer = env.buyer, seller = env.seller.
--   rawSurplus m = vB - vS ≤ 0 by the hypothesis.
--   l0RealizedSurplus [m] = rawSurplus m + 0ℚ ≤ rawSurplus m ≤ 0ℚ. ✓
--
-- This is proved here (inside L0AgentStrategy) so that the private helper
-- `fromMaybe` is in scope for the definitional reduction:
--   fromMaybe (just m) = m ∷ []  →  sumQ [rawSurplus m] = rawSurplus m + 0ℚ.

-- Private rational 0ℚ comparison helper used in l0Nonpos-inverted.
-- We case-split on  askP ≤? bidP  which is the same discriminant that tryL0Match uses.
-- This forces the goal to reduce in the yes-branch:
--   concreteL0Sim env s = [ record { buyer = buyer; seller = seller; ... } ]
--   rawSurplus of that record = vB - vS  (field projections reduce immediately).

l0Nonpos-inverted
  : ∀ {n} (env : SimEnvironment) (s : Seed (suc n) 2)
  → ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer env))
    ≤ ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))
  → l0RealizedSurplus (concreteL0Sim {n} env s) ≤ 0ℚ
l0Nonpos-inverted {n} env s h
  with askP ≤? bidP
  where
    open SimEnvironment env
    bidP = l0Tick n maxP (drawAt s fzero)
    askP = l0Tick n maxP (drawAt s (fsuc fzero))
... | no  _        = ≤-refl
... | yes _crosses =
  ≤-trans
    (≤-reflexive (+-identityʳ (vB - vS)))
    (subst ((vB - vS) ≤_) (+-inverseʳ vS) (+-monoˡ-≤ (- vS) h))
  where
    vB = ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.buyer  env))
    vS = ValuationSchedule.unitValue (Agent.valuation (SimEnvironment.seller env))
