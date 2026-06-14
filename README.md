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

The proof is developed across 23 modules, building from primitive types to the final stochastic dominance theorems.

```
Agent.agda                    — Agents: roles, valuations, budgets, inventory
Proposal.agda                 — Raw proposals; L0 and L3 constraint levels
Seed.agda                     — Oracle tape: Vec (Fin n) k, the random number source
Institution.agda              — Batch clearing auction; BuyerAdmissible / SellerAdmissible
Surplus.agda                  — Trade surplus definition; proof that 0 ≤ surplus(m) for L3
Trace.agda                    — Event log; realizedSurplus; non-negativity theorem
Efficiency.agda               — Efficiency ratio and its non-negativity
Flagship.agda                 — L0 witness match (rawSurplus = −1); structural dominance
Probability.agda              — sumQ; non-negative sums; strict monotonicity
SimulationModel.agda          — Abstract flagship: Theorems 6 (pointwise) and 7 (expected)
PriceGrid.agda                — Uniform tick grids; ratio ≤ 1 proved from gcd arithmetic
AgentStrategy.agda            — Certified L3 proposals from seed indices
BatchAuction.agda             — tryMatch with decidable crossing; matchZip
FlagshipFull.agda             — Concrete SimFnL3; pointwise flagship instantiated
L0AgentStrategy.agda          — Concrete SimFnL0; negative-surplus witness; l0Nonpos-inverted
Stochastic.agda               — survivalCount; FSDom; l3FSDom-l0-inverted; l3Expected-l0-inverted; l0FSDom-l3-productive
MultiAgentSim.agda            — k-pair extension; AllInverted/AllProductive; l3FSDom-l0-invertedN; l0FSDom-l3-productiveN; l3ExpectedN-l0-inverted; l0ExpectedN-l3-productive
EfficiencyFSD.agda            — Efficiency ratio FSD; l3EffFSDom-l0-inverted; l0EffFSDom-l3-productive; expected-efficiency corollaries
MultiAgentEffFSD.agda         — k-pair efficiency FSD; l3EffFSDom-l0-invertedN; l0EffFSDom-l3-productiveN; expected corollaries
MixedWelfare.agda             — Oracle-mix welfare; Mixed predicate; mixFSDom-l3; mixFSDom-l0; expected corollaries
MixedEffFSD.agda              — Oracle-mix efficiency FSD; concreteMixEffN; mixEffFSDom-l3; mixEffFSDom-l0; expected corollaries
PureStrategyIncomparable.agda — Negative result: l0NotFSDom-l3-mixed; l3NotFSDom-l0-mixed
Main.agda                     — Executable: runs both environments over all 16 seeds (n=3)
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

### Theorem (Expected Value — Corollary)
In any environment where $v_b \leq v_s$, for any seed population $\Omega$:
$$\mathbb{E}_\Omega[\text{L0 surplus}] \leq \mathbb{E}_\Omega[\text{L3 surplus}]$$

i.e., $\text{sumQ}(\text{map}\ (\text{l0Surplus} \circ \text{concreteL0Sim})\ \Omega) \leq \text{sumQ}(\text{map}\ (\text{l3Surplus} \circ \text{concreteSim})\ \Omega)$.

*Proof:* By `sumQ-map-mono` applied to the same pointwise bound: $\text{l0Surplus}(s) \leq 0 \leq \text{l3Surplus}(s)$.

*Note:* Both the FSD result and this expected-value result derive from the same pointwise ingredient. FSD is strictly stronger — E[f] ≥ E[g] follows from FSD, but not conversely. This theorem closes the gap left by Theorem 7, which required the false hypothesis 4 (pointwise dominance everywhere, including productive markets).

### Theorem (Symmetric FSD — Productive Markets)
In any environment where $v_s \leq v_b$ (productive market), and under the additional conditions $0 \leq v_s$ and $\text{cap} \leq p_{\max}$, for any seed population $\Omega$:
$$\text{FSDom}\bigl(\text{l0RealizedSurplus} \circ \text{concreteL0Sim},\ \text{realizedSurplus} \circ \text{concreteSim},\ \Omega\bigr)$$

i.e., L0 first-order stochastically dominates L3 in productive markets.

*Proof:* By `FSD-from-pointwise` using `l3LE-l0-productive`: the key arithmetic chain shows that if L3 agents cross (L3 ask ≤ L3 bid), then L0 agents also cross (L0 ask ≤ L0 bid), because `L0_ask ≤ L3_ask ≤ L3_bid ≤ L0_bid`. Therefore `∀ s, L3(s) ≤ L0(s)`.

*Economic interpretation:* The L3 constraint forces bids ≤ $v_b$ and asks ≥ $v_s$, a strictly tighter range than L0's unconstrained full grid. Every seed where L3 trades, L0 also trades (for the same surplus $v_b - v_s$). But there are seeds where L0 trades and L3 doesn't — the conservative constraint prevents many value-creating trades. These two FSD results together characterise the crossover: L3 dominates exactly when trades would destroy value, L0 dominates exactly when trades create value.

### Theorem (Multi-Agent FSD — Inverted Markets)
For any $k$ buyer-seller pairs with independent seeds and `AllInverted` conditions ($v_{b,i} \leq v_{s,i}$ for all $i$), and any multi-seed population $\Omega$:
$$\text{FSDom}\bigl(\text{realizedSurplusN}\ \text{envs},\ \text{l0RealizedSurplusN}\ \text{envs},\ \Omega\bigr)$$

where $\text{realizedSurplusN}\ \text{envs}\ \mathbf{s} = \sum_{i=1}^{k} \text{realizedSurplus}(\text{concreteSim}\ e_i\ s_i)$ and similarly for L0.

*Proof:* By `FSD-from-pointwise` applied to the pointwise bound `l0LEL3-invertedN`, which is proved by Vec induction: each pair satisfies `l0Nonpos-inverted` and `realizedSurplusNonNeg`, so `+-mono-≤` lifts the bound to the sum.

### Theorem (Multi-Agent FSD — Productive Markets)
For any $k$ pairs with `AllProductive` conditions ($0 \leq v_{s,i}$, $v_{s,i} \leq v_{b,i}$, $\text{cap}_i \leq p_{\max,i}$ for all $i$), and any $\Omega$:
$$\text{FSDom}\bigl(\text{l0RealizedSurplusN}\ \text{envs},\ \text{realizedSurplusN}\ \text{envs},\ \Omega\bigr)$$

*Proof:* By `FSD-from-pointwise` and `l3LEL0-productiveN`, which applies `l3LE-l0-productive` per pair and lifts by `+-mono-≤`.

### Theorem (Multi-Agent Expected Value — Inverted Markets)
For any $k$ pairs with `AllInverted` conditions and any $\Omega$:
$$\sum_{\mathbf{s} \in \Omega} \text{l0RealizedSurplusN}(\text{envs}, \mathbf{s}) \;\leq\; \sum_{\mathbf{s} \in \Omega} \text{realizedSurplusN}(\text{envs}, \mathbf{s})$$

*Proof:* `sumQ-map-mono` applied to `l0LEL3-invertedN`.

### Theorem (Multi-Agent Expected Value — Productive Markets)
For any $k$ pairs with `AllProductive` conditions and any $\Omega$: the symmetric inequality, $\mathbb{E}_\Omega[\text{L0}] \geq \mathbb{E}_\Omega[\text{L3}]$.

*Extension structure:* `MultiAgentSim.agda` adds all multi-agent results with zero changes to any existing module. The key structural lemma `realizedSurplus-++` (realized surplus splits over trace concatenation) connects the multi-agent `Trace` output to the per-pair sum. The $k=1$ case of each multi-agent theorem recovers the corresponding single-pair result from `Stochastic.agda`.

### Theorem (Efficiency FSD — Inverted Markets)
For any environment with $v_b \leq v_s$, profitable-pair list $\mathit{ps}$ with $\mathit{mfs} > 0$, and seed population $\Omega$:
$$\text{FSDom}\bigl(\text{concreteL3Eff},\ \text{concreteL0Eff},\ \Omega\bigr)$$

where $\text{concreteL3Eff}(s) = \text{realizedSurplus}(\text{concreteSim}(s)) \div \mathit{mfs}$ and similarly for L0.

*Proof:* By `FSD-from-pointwise`. The pointwise bound $\text{concreteL0Eff}(s) \leq \text{concreteL3Eff}(s)$ follows from `l0Nonpos-inverted` ($\text{L0} \leq 0$) and `realizedSurplusNonNeg` ($0 \leq \text{L3}$), each lifted to efficiency ratios via `*-monoʳ-≤-nonNeg (1/ mfs)`. Since $a \div c = a \times (1/c)$ definitionally, the result matches the required efficiency ratio type.

### Theorem (Efficiency FSD — Productive Markets)
For any environment with $v_s \leq v_b$, $0 \leq v_s$, $\text{cap} \leq p_{\max}$, $\mathit{mfs} > 0$, and $\Omega$:
$$\text{FSDom}\bigl(\text{concreteL0Eff},\ \text{concreteL3Eff},\ \Omega\bigr)$$

*Proof:* By `FSD-from-pointwise` using `l3LE-l0-productive` lifted by `*-monoʳ-≤-nonNeg (1/ mfs)`.

*Gode & Sunder connection:* This is the formal analogue of G&S's headline result: unrestricted ZIT agents in productive markets achieve higher (in the FSD sense) efficiency ratios than constrained agents. The institution sets the price; the constraint only restricts when agents can trade.

### Corollary (Expected Efficiency)
Both FSD results yield expected-efficiency corollaries by `sumQ-map-mono`:
- Inverted: $\mathbb{E}_\Omega[\text{L3 efficiency}] \geq \mathbb{E}_\Omega[\text{L0 efficiency}]$
- Productive: $\mathbb{E}_\Omega[\text{L0 efficiency}] \geq \mathbb{E}_\Omega[\text{L3 efficiency}]$

*Note on $\mathit{mfs} > 0$:* In a strictly inverted single-pair market the max feasible surplus is 0, making the efficiency ratio undefined. The inverted theorem carries `mfs > 0` as an explicit hypothesis, satisfied when the profitable-pair list comes from a parallel productive sub-market.

*Extension structure:* `EfficiencyFSD.agda` adds all efficiency-ratio results with zero changes to any existing module. Every proof applies an existing lemma (`l0Nonpos-inverted`, `l3LE-l0-productive`, `realizedSurplusNonNeg`, `FSD-from-pointwise`) composed with the monotonicity of multiplication by a non-negative scalar.

### Theorem (k-Pair Efficiency FSD — Inverted Markets)
For any $k$ pairs with `AllInverted` conditions, $\mathit{mfs} > 0$, and $\Omega$:
$$\text{FSDom}\bigl(\text{concreteL3EffN},\ \text{concreteL0EffN},\ \Omega\bigr)$$

where $\text{concreteL3EffN}(\mathbf{s}) = \text{realizedSurplusN}(\text{envs}, \mathbf{s}) \div \mathit{mfs}$ and similarly for L0.

*Proof:* By `FSD-from-pointwise`. The portfolio raw-surplus bound `l0RealizedSurplusN ≤ realizedSurplusN` (reproved from `MultiAgentSim`'s private `l0LEL3-invertedN` by identical Vec induction), lifted by `*-monoʳ-≤-nonNeg (1/ mfs)`.

### Theorem (k-Pair Efficiency FSD — Productive Markets)
For any $k$ pairs with `AllProductive` conditions, $\mathit{mfs} > 0$, and $\Omega$:
$$\text{FSDom}\bigl(\text{concreteL0EffN},\ \text{concreteL3EffN},\ \Omega\bigr)$$

Plus expected-efficiency corollaries in both directions.

*Extension structure:* `MultiAgentEffFSD.agda` closes the 2×2 table — every combination of (single / k pairs) × (raw surplus / efficiency ratio) now has FSD and expected-value theorems. The module makes zero changes to any existing module. The $k=1$ case recovers the single-pair results from `EfficiencyFSD.agda`.

| | Single pair | k pairs |
|--|-------------|---------|
| Raw surplus FSD | `Stochastic` ✓ | `MultiAgentSim` ✓ |
| Efficiency FSD | `EfficiencyFSD` ✓ | `MultiAgentEffFSD` ✓ |

### Theorem (Oracle Mix Welfare — Mixed Markets)

In a market with $k$ pairs where each is either inverted or productive, the **oracle mix** strategy (L3 on inverted pairs, L0 on productive pairs) FSD-dominates both pure strategies simultaneously:

$$\text{FSDom}\bigl(\text{concreteMixSurplusN},\ \text{realizedSurplusN},\ \Omega\bigr) \qquad \text{(mix dominates pure L3)}$$
$$\text{FSDom}\bigl(\text{concreteMixSurplusN},\ \text{l0RealizedSurplusN},\ \Omega\bigr) \qquad \text{(mix dominates pure L0)}$$

*Oracle mix:* for each pair, use L3 if $v_b \leq v_s$ (prevents value-destroying trades) and L0 if $v_s \leq v_b$ (captures all value-creating trades).

*Proof:* `FSD-from-pointwise` applied to pointwise bounds proved by induction on the `Mixed` predicate:
- `invMix` pair: mix = L3 for both strategies; heads equal (≤-refl) for mix vs L3; `l0Nonpos-inverted` + `realizedSurplusNonNeg` gives L0 ≤ mix.
- `prodMix` pair: mix = L0 for both strategies; `l3LE-l0-productive` gives L3 ≤ mix; heads equal (≤-refl) for mix vs L0.

*Economic interpretation:* Pure L3 leaves productive-market gains on the table. Pure L0 executes inverted-market trades that destroy value. The oracle mix is Pareto-superior to both: it equals L3 where L3 is optimal and equals L0 where L0 is optimal.

*Generalization:* When all pairs are inverted, `concreteMixSurplusN = realizedSurplusN` and `mixFSDom-l0` recovers `l3FSDom-l0-invertedN`. When all pairs are productive, `concreteMixSurplusN = l0RealizedSurplusN` and `mixFSDom-l3` recovers `l0FSDom-l3-productiveN`. `MixedWelfare` therefore strictly generalises `MultiAgentSim`'s FSD results.

Plus expected-welfare corollaries `mixExpected-l3` and `mixExpected-l0`.

### Theorem (Oracle Mix Efficiency FSD — Mixed Markets)

The oracle mix also dominates both pure strategies in the efficiency ratio metric:

$$\text{FSDom}\bigl(\text{concreteMixEffN},\ \text{concreteL3EffN},\ \Omega\bigr) \qquad \text{(mix efficiency dominates L3 efficiency)}$$
$$\text{FSDom}\bigl(\text{concreteMixEffN},\ \text{concreteL0EffN},\ \Omega\bigr) \qquad \text{(mix efficiency dominates L0 efficiency)}$$

where $\text{concreteMixEffN}(\mathbf{s}) = \text{concreteMixSurplusN}(\text{envs}, h, \mathbf{s}) \div \mathit{mfs}$.

*Proof:* The raw-surplus pointwise bounds (`l3LE-mix`, `l0LE-mix`) are lifted by `*-monoʳ-≤-nonNeg (1/ mfs)`, exactly as in Modules 19–20.

Plus expected-efficiency corollaries `mixEffExpected-l3` and `mixEffExpected-l0`.

This completes the full 3D result table:

| | Single pair | k pairs | Mixed market |
|--|-------------|---------|--------------|
| Raw surplus FSD | `Stochastic` ✓ | `MultiAgentSim` ✓ | `MixedWelfare` ✓ |
| Efficiency FSD | `EfficiencyFSD` ✓ | `MultiAgentEffFSD` ✓ | `MixedEffFSD` ✓ |

### Theorem (Pure Strategy Incomparability — Mixed Markets)

In any mixed market, neither pure strategy FSD-dominates the other. Specifically:

$$\lnot\ \text{FSDom}\bigl(\text{l0RealizedSurplusN},\ \text{realizedSurplusN},\ [\mathbf{s}_1]\bigr) \qquad \text{given } \text{L0}(\mathbf{s}_1) < 0$$

$$\lnot\ \text{FSDom}\bigl(\text{realizedSurplusN},\ \text{l0RealizedSurplusN},\ [\mathbf{s}_2]\bigr) \qquad \text{given } \text{L3}(\mathbf{s}_2) < \text{L0}(\mathbf{s}_2)$$

Both hypotheses are satisfiable simultaneously in any market with at least one inverted pair (where L0 can go negative) and at least one productive pair (where L3 is strictly worse than L0).

*Proof (l0NotFSDom-l3-mixed):* At threshold $t = 0$: $\text{survivalCount}(\text{L3}, [\mathbf{s}_1], 0) = 1$ (since L3 $\geq 0$ always, from `realizedSurplusN-nonNeg`) but $\text{survivalCount}(\text{L0}, [\mathbf{s}_1], 0) = 0$ (since L0($\mathbf{s}_1$) $< 0$). FSDom would require $1 \leq 0$ in $\mathbb{N}$ — absurd.

*Proof (l3NotFSDom-l0-mixed):* At threshold $t = \text{L0}(\mathbf{s}_2)$: $\text{survivalCount}(\text{L0}, [\mathbf{s}_2], t) = 1$ (L0 $\geq t$ by $\leq$-refl) but $\text{survivalCount}(\text{L3}, [\mathbf{s}_2], t) = 0$ (L3($\mathbf{s}_2$) $< t$). FSDom would require $1 \leq 0$ — absurd.

*Economic interpretation:* There is no uniformly best pure strategy in mixed markets. The oracle mix from Modules 21–22 is needed to dominate both. This negative result completes the picture: the 3D table shows what *is* true (oracle mix dominates everything), and `PureStrategyIncomparable` shows what is *not* true (pure strategies don't dominate each other).

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

**`÷` in return types and Pi-bound instances.** The standard library `_÷_` operator requires `{{NonZero q}}` at every use site, including inside type signatures. An anonymous Pi-bound instance `→ {{NonZero c}} →` is not reliably found by instance search when `a ÷ c` appears in the same signature's return type. Workaround: since `a ÷ c = a * (1/ c)` definitionally, use `ℚP.*-monoʳ-≤-nonNeg (1/ c)` directly and supply the full instance chain (`>-nonZero`, `positive`, `1/pos⇒pos`, `pos⇒nonNeg`) in the `where` block of each call site. Agda accepts the result by definitional equality.

**Cross-module infix constructor with product argument.** The `AllProductive` constructor `_ap∷_` (defined in `MultiAgentSim`) bundles three conditions as a right-associated product. When imported into another module, the pattern `((hVS , hProd , hCap) ap∷ hs)` on a function LHS causes a parse error — the comma-separated triple conflicts with the infix constructor at the operator precedence level. Solution: match `(hconds ap∷ hs)` and extract components with `proj₁`/`proj₂`.

---

## References

- Gode, D. K. & Sunder, S. (1993). "Allocative Efficiency of Markets with Zero-Intelligence Traders." *Journal of Political Economy*, 101(1), 119–137.
- Agda documentation: https://agda.readthedocs.io/
- Agda standard library: https://agda.github.io/agda-stdlib/
