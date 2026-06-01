# ZITAgda

A machine-verified formalization of the **Zero Intelligence Trader (ZIT) flagship theorem** in [Agda](https://agda.readthedocs.io/), with a concrete runnable simulation.

---

## What This Is

Zero-Intelligence Traders (Gode & Sunder 1993) are the simplest possible market agents: they draw prices at random, with no strategic reasoning. Yet even these maximally dumb agents, when placed inside a double auction institution, produce near-efficient outcomes. The institution does the work.

The *flagship theorem* asks: **does the institution's rule set matter?** Specifically, does the L3 constraint — buyers don't bid above their valuation, sellers don't ask below their cost — produce better outcomes than the fully unconstrained L0 rule?

This project gives a **formal machine-checked proof** of the structural result, plus a concrete simulation that shows both environments side by side. Everything is written in Agda 2.8.0 using the standard library.

---

## The Core Theorem (Informal)

**L3 constraint:** A buyer with valuation $v_b$ bids at most $v_b$. A seller with cost $v_s$ asks at least $v_s$.

**Key structural result:** Every L3 trade generates non-negative social surplus $v_b - v_s \geq 0$. Under L0, there is no such guarantee — a buyer can bid above their valuation and a seller ask below cost, causing them to cross when they shouldn't.

**Flagship result:** In any market environment where $v_b \leq v_s$ (trades would destroy value), the L3 surplus distribution **first-order stochastically dominates** the L0 surplus distribution over the full seed space.

> For every threshold $t$, the probability that L3 produces surplus $\geq t$ is at least the probability that L0 does.

This is a full distributional statement — stronger than just showing there exists *some* seed where L3 beats L0.

---

## The Counterexample (Also Proved)

The simulation also demonstrates that the theorem does **not** hold in all environments. When $v_b > v_s$ (trades are socially efficient), L0 actually outperforms L3:

| Environment | L0 trades | L3 trades | Result |
|-------------|-----------|-----------|--------|
| `witnessEnv`: $v_b=1$, $v_s=2$, $p_{\max}=3$ | 10/16 seeds (surplus = −1) | 0/16 seeds | **L3 dominates** |
| `marketEnv`: $v_b=3$, $v_s=1$, $p_{\max}=4$ | 10/16 seeds (surplus = +2) | 3/16 seeds | **L0 dominates** |

In the market environment, L3's conservative constraints prevent many beneficial trades. The formalization proves both the positive result (for inverted markets) and exhibits the failure mode (for productive markets) concretely.

---

## Module Structure

The proof is developed across 17 modules, building from primitive types to the final stochastic dominance theorem.

```
Agent.agda           — Agents: roles, valuations, budgets, inventory
Proposal.agda        — Raw proposals; L0 and L3 constraint levels
Seed.agda            — Oracle tape: Vec (Fin n) k, the random number source
Institution.agda     — Batch clearing auction; BuyerAdmissible / SellerAdmissible
Surplus.agda         — Trade surplus definition; proof that 0 ≤ surplus(m) for L3
Trace.agda           — Event log; realizedSurplus; non-negativity theorem
Efficiency.agda      — Efficiency ratio and its non-negativity
Flagship.agda        — L0 witness match (rawSurplus = −1); structural dominance
Probability.agda     — sumQ; non-negative sums; strict monotonicity
SimulationModel.agda — Abstract flagship: Theorems 6 (pointwise) and 7 (expected)
PriceGrid.agda       — Uniform tick grids; ratio ≤ 1 proved from gcd arithmetic
AgentStrategy.agda   — Certified L3 proposals from seed indices
BatchAuction.agda    — tryMatch with decidable crossing; matchZip
FlagshipFull.agda    — Concrete SimFnL3; pointwise flagship instantiated
L0AgentStrategy.agda — Concrete SimFnL0; negative-surplus witness; l0Nonpos-inverted
Stochastic.agda      — survivalCount; FSDom; l3FSDom-l0-inverted (main FSD theorem)
Main.agda            — Executable: runs both environments over all 16 seeds (n=3)
```

---

## The Theorems

### Theorem 1 — Valuation Chain
For any L3 match $m$: $v_s \leq v_b$.

*Proof:* $v_s \leq \text{ask} \leq \text{bid} \leq v_b$ via SellerAdmissible, crossing, BuyerAdmissible.

### Theorem 2 — Non-Negative Surplus
For any L3 match $m$: $0 \leq v_b - v_s$.

*Proof:* From Theorem 1 and the ordered-field law $p \leq q \Rightarrow 0 \leq q - p$.

### Theorem 3 — Non-Negative Realized Surplus
For any L3 trace $t$: $\text{realizedSurplus}(t) \geq 0$.

*Proof:* Induction on the match list; each summand is $\geq 0$ by Theorem 2.

### Theorem 5 — Structural Dominance
$$\underbrace{\forall t,\ 0 \leq \text{realizedSurplus}(t)}_{\text{L3 guarantee}} \times \underbrace{\exists m,\ v_s(m) > v_b(m)}_{\text{L0 failure witness}}$$

### Theorem 6 — Pointwise Flagship
If $\exists s_0$ with $\text{l0Surplus}(s_0) < 0$, then $\exists s_0$ with $\text{l0Surplus}(s_0) < \text{l3Surplus}(s_0)$.

*Proof:* Take the same $s_0$; chain $< 0 \leq \text{l3Surplus}(s_0)$ via `<-≤-trans`.

### Theorem 7 — Expected Flagship (Conditional)
Given additionally that $\text{l0Surplus}(s) \leq \text{l3Surplus}(s)$ for all $s$, and a finite seed list $\Omega \ni s_0$:
$$\mathbb{E}_\Omega[\text{l3Surplus}] > \mathbb{E}_\Omega[\text{l0Surplus}]$$

*Note:* Hypothesis 4 (pointwise dominance) fails in productive markets — the simulation demonstrates this. The formalization makes this gap explicit.

### Theorem (l0Nonpos-inverted)
In any environment where $v_b \leq v_s$: $\forall s,\ \text{l0RealizedSurplus}(\text{concreteL0Sim}(s)) \leq 0$.

*Proof:* Case split on whether L0 trades. No-trade: surplus = 0. Trade: surplus = $v_b - v_s \leq 0$.

### Theorem (FSD — Main Result)
In any environment where $v_b \leq v_s$, for any seed population $\Omega$:
$$\text{FSDom}\bigl(\text{realizedSurplus} \circ \text{concreteSim},\ \text{l0RealizedSurplus} \circ \text{concreteL0Sim},\ \Omega\bigr)$$

*Proof:* By `FSD-from-pointwise`: from $\text{l0Surplus}(s) \leq 0 \leq \text{l3Surplus}(s)$ pointwise.

---

## What "Formal Proof" Means Here

In Agda, proofs and programs are the same thing (Curry–Howard correspondence). A theorem like

```agda
surplusNonNeg : ∀ (m : Match) → 0ℚ ≤ surplus m
surplusNonNeg m = p≤q⇒0≤q-p (valuationChain m)
```

is simultaneously a function definition and a proof. The *type* is the statement; the *term* is the proof. Agda's type-checker accepting the file is equivalent to checking the proof for all matches simultaneously.

Key consequences:
- **No case is missed.** Pattern matching must be exhaustive; the type-checker enforces it.
- **No uncertified trade can enter a Trace.** The `TradeSettled` constructor requires a `Match`, which requires admissibility evidence. You literally cannot construct an ill-formed trace.
- **The witness is concrete.** `witnessSeedNegSurplus` is proved by Agda evaluating `l0RealizedSurplus (concreteL0Sim witnessEnv witnessSeed) <? 0ℚ` to `yes proof` at compile time.

---

## The Probability Model

Rather than measure theory, we use **finite counting**:

$$\text{survivalCount}(f, \Omega, t) = |\{s \in \Omega : f(s) \geq t\}|$$

First-order stochastic dominance:
$$\text{FSDom}(f, g, \Omega) \;\equiv\; \forall t,\ \text{survivalCount}(g, \Omega, t) \leq \text{survivalCount}(f, \Omega, t)$$

The key lemma `FSD-from-pointwise` shows that pointwise dominance $\forall s,\ g(s) \leq f(s)$ implies FSD. Its proof goes through `filter-mono`: if Bool predicate $q$ implies $p$ (i.e., $q(x) = \text{true} \Rightarrow p(x) = \text{true}$), then `|filter q xs| ≤ |filter p xs|`.

---

## Running the Simulation

**Requirements:** Agda 2.8.0, GHC 9.x, agda-stdlib 2.x.

```bash
# Type-check only
agda src/Main.agda

# Compile and run (requires GHC backend)
agda --compile src/Main.agda
./src/Main
```

**Sample output:**

```
=== Environment 1: witness (v_buyer=1, v_seller=2, maxP=3) ===
  L0 bid/ask from full grid {0, 3/4, 3/2, 9/4}
  L3 buyer bids in {0, 1/4, 1/2, 3/4}  (cap at v=1)
  L3 seller asks in {2, 9/4, 5/2, 11/4} (floor at v=2)
  Result: L3 never trades; L0 trades and destroys value

  seed  bid     ask     L0       L3
  [0,0]  bid=0/1  ask=0/1  L0=0/1  L3=0/1
  [1,0]  bid=3/4  ask=0/1  L0=-1/1  L3=0/1
  ...

=== Environment 2: market (v_buyer=3, v_seller=1, maxP=4) ===
  ...
  [2,0]  bid=2/1  ask=0/1  L0=2/1  L3=2/1
  [3,0]  bid=3/1  ask=0/1  L0=2/1  L3=2/1
  ...
```

---

## Key Technical Decisions

**`isYes` vs `does` for decidable comparisons.** The Agda stdlib `Dec` record has a field `does : Bool`. After a `with` abstraction, the field does not reduce. `isYes` is a separate pattern-matching function (`isYes (no _) = false`) that *does* reduce. The `survivalCount` predicate uses `isYes` for this reason.

**Private helpers and definitional opacity.** The `fromMaybe` helper in `L0AgentStrategy` is private. Proofs that depend on its reduction (i.e., `fromMaybe (just m) = m ∷ []`) must live inside the same module. `l0Nonpos-inverted` is therefore proved in `L0AgentStrategy.agda` and exported.

**Case-splitting on the internal discriminant.** Rather than matching on `tryL0Match ... = just m` (which leaves `m` opaque), `l0Nonpos-inverted` matches on `askP ≤? bidP` — the same `with` scrutinee inside `tryL0Match`. This forces the record fields to reduce, making `rawSurplus m = v_b - v_s` definitionally.

---

## References

- Gode, D. K. & Sunder, S. (1993). "Allocative Efficiency of Markets with Zero-Intelligence Traders." *Journal of Political Economy*, 101(1), 119–137.
- Agda documentation: https://agda.readthedocs.io/
- Agda standard library: https://agda.github.io/agda-stdlib/
