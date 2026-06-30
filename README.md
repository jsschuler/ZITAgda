# ZITAgda

A machine-verified formalization of the **Zero Intelligence Trader (ZIT) flagship theorem** in [Agda](https://agda.readthedocs.io/), with a concrete runnable simulation.

---

## What This Is

Zero-Intelligence Traders (Gode & Sunder 1993) are the simplest possible market agents: they draw prices at random, with no strategic reasoning. Yet even these maximally dumb agents, when placed inside a double auction institution, produce near-efficient outcomes. The institution does the work.

The *flagship theorem* asks: **does the institution's rule set matter?** Specifically, does the L3 constraint — buyers don't bid above their valuation, sellers don't ask below their cost — produce better outcomes than the fully unconstrained L0 rule?

This project gives a **formal machine-checked proof** of the structural result, plus a concrete simulation that shows both environments side by side. Everything is written in Agda 2.8.0 using the standard library.

---

## Quick Start

**Requirements:** Agda 2.8.0, GHC 9.x, agda-stdlib 2.x.

```bash
# Type-check only
agda src/Main.agda

# Compile and run (requires GHC backend)
agda --compile src/Main.agda
./src/Main
```

---

## Constraint Levels

The formalization distinguishes two bidding regimes:

- **L0 (Unconstrained):** Agents draw from the full price grid $\{0, \Delta, 2\Delta, \ldots, p_{\max}\}$ with no relationship to their valuation or cost.
- **L3 (Budget-constrained):** A buyer with valuation $v_b$ bids at most $v_b$; a seller with cost $v_s$ asks at least $v_s$.

L3 is the constraint that Gode & Sunder impose in their original paper. L0 is the unconstrained baseline that isolates the constraint's role.

---

## The Core Theorem (Informal)

**Key structural result:** Every L3 trade generates non-negative social surplus $v_b - v_s \geq 0$. Under L0, there is no such guarantee — a buyer can bid above their valuation and a seller ask below cost, causing them to cross when they shouldn't.

**Flagship result:** In any market environment where $v_b \leq v_s$ (trades would destroy value), the L3 surplus distribution **first-order stochastically dominates** the L0 surplus distribution over the full seed space.

> For every threshold $t$, the probability that L3 produces surplus $\geq t$ is at least the probability that L0 does.

This is a full distributional statement — stronger than just showing there exists *some* seed where L3 beats L0.

---

## The Counterexample (Also Proved)

The simulation also demonstrates that the theorem does **not** hold in all environments. When $v_b > v_s$ (trades are socially efficient), L0 actually outperforms L3:

| Environment | L0 trades | L3 trades | Result |
|---|---|---|---|
| `witnessEnv`: $v_b=1$, $v_s=2$, $p_{\max}=3$ | 10/16 seeds (surplus = −1) | 0/16 seeds | **L3 dominates** |
| `marketEnv`: $v_b=3$, $v_s=1$, $p_{\max}=4$ | 10/16 seeds (surplus = +2) | 3/16 seeds | **L0 dominates** |

In the market environment, L3's conservative constraints prevent many beneficial trades. The formalization proves both the positive result (for inverted markets) and exhibits the failure mode (for productive markets) concretely.

---

## The Probability Model

Rather than measure theory, we use **finite counting**. This is natural because the seed space is a finite vector of indices into a price grid.

$$\text{survivalCount}(f, \Omega, t) = |\{s \in \Omega : f(s) \geq t\}|$$

**First-order stochastic dominance:**

$$\text{FSDom}(f, g, \Omega) \;\equiv\; \forall t,\; \text{survivalCount}(f, \Omega, t) \geq \text{survivalCount}(g, \Omega, t)$$

That is, $f$ FSD-dominates $g$ if, at every threshold $t$, at least as many seeds clear the threshold under $f$ as under $g$.

**The key lemma — `FSD-from-pointwise`:** If $g(s) \leq f(s)$ for every seed $s$, then $\text{FSDom}(f, g, \Omega)$ for any finite $\Omega$.

*Proof sketch:* Fix any threshold $t$. If $g(s) \geq t$ then $f(s) \geq g(s) \geq t$, so every seed counted in $\text{survivalCount}(g, \Omega, t)$ is also counted in $\text{survivalCount}(f, \Omega, t)$. In Agda this is formalized via `filter-mono`: when a Bool predicate $q$ implies predicate $p$ pointwise (i.e., $q(x) = \mathrm{true} \Rightarrow p(x) = \mathrm{true}$), then `|filter q xs| ≤ |filter p xs|`. The survival counts are `filter`s over the seed list $\Omega$, so monotonicity of `filter` gives the result.

Nearly every FSD theorem in this project is proved by instantiating `FSD-from-pointwise` with an appropriate pointwise bound, making that bound the proof's real content.

---

## The Theorems

The proof is organized in two layers. Theorems 1–4 are purely structural results about individual matches and traces, proved in `Surplus.agda` through `Efficiency.agda`. Theorems 5–7 are the abstract flagship results, proved in `Flagship.agda` and `SimulationModel.agda`. The remaining theorems are the concrete FSD and expected-value results, instantiated against specific simulations in `Stochastic.agda` and later modules.

---

### Theorem 1 — Valuation Chain

**Statement:** For any L3 match $m$: $v_s \leq v_b$.

**Proof:** Three separate facts about an L3 match chain into the result:

1. **`SellerAdmissible`**: the L3 constraint on the seller enforces $v_s \leq \text{ask}$.
2. **Crossing**: a match is only recorded when the bid meets or exceeds the ask, i.e., $\text{ask} \leq \text{bid}$.
3. **`BuyerAdmissible`**: the L3 constraint on the buyer enforces $\text{bid} \leq v_b$.

Combining: $v_s \leq \text{ask} \leq \text{bid} \leq v_b$. Two applications of transitivity (`≤-trans`) then give $v_s \leq v_b$ directly. No arithmetic is required — only the order structure of the rationals.

---

### Theorem 2 — Non-Negative Surplus

**Statement:** For any L3 match $m$: $0 \leq v_b - v_s$.

**Proof:** Theorem 1 establishes $v_s \leq v_b$. The standard library lemma `p≤q⇒0≤q-p` captures the ordered-field identity: whenever $p \leq q$ in $\mathbb{Q}$, we have $0 \leq q - p$. Setting $p := v_s$ and $q := v_b$ and applying this to the conclusion of Theorem 1 gives $0 \leq v_b - v_s$ — which is exactly the surplus — in one step.

In Agda:

```agda
surplusNonNeg : ∀ (m : Match) → 0ℚ ≤ surplus m
surplusNonNeg m = p≤q⇒0≤q-p (valuationChain m)
```

The type `surplus m` unfolds to `v_b - v_s`, so `surplusNonNeg` is the statement itself. The proof term is a single function application: `valuationChain` produces the inequality $v_s \leq v_b$, and `p≤q⇒0≤q-p` converts it.

---

### Theorem 3 — Non-Negative Realized Surplus

**Statement:** For any L3 trace $t$: $\text{realizedSurplus}(t) \geq 0$.

**Proof:** The realized surplus is the sum of per-match surpluses over the entire trade history. The proof proceeds by structural induction on the match list:

- *Base case:* An empty trace has realized surplus 0. Since $0 \leq 0$, the base case holds.
- *Inductive step:* Suppose the tail of the trace already has realized surplus $\geq 0$ (the inductive hypothesis). Appending a new match $m$ adds $\text{surplus}(m) \geq 0$ (by Theorem 2) to that running total. Since the sum of two non-negative rationals is non-negative — formally, `+-mono-≤` applied to $0 \leq \text{surplus}(m)$ and the inductive hypothesis — the extended trace also has non-negative realized surplus.

This proof works because the `Trace` type is an inductive list of `TradeSettled` events, and each `TradeSettled` constructor carries a `Match` — which in turn carries the admissibility evidence needed by Theorem 2. The type system ensures no unevidenced match can enter the list.

---

### Theorem 4 — Non-Negative Efficiency Ratio

**Statement:** For any L3 trace $t$ and max-feasible-surplus $\mathit{mfs} > 0$:

$$\text{efficiencyRatio}(t) = \frac{\text{realizedSurplus}(t)}{\mathit{mfs}} \geq 0$$

**Proof:** The efficiency ratio is defined as $\text{realizedSurplus}(t) \times (1/\mathit{mfs})$. Theorem 3 gives $\text{realizedSurplus}(t) \geq 0$. Since $\mathit{mfs} > 0$, we have $1/\mathit{mfs} > 0$ as well, so $1/\mathit{mfs}$ is a non-negative scalar. Non-negativity is preserved by multiplication by a non-negative scalar: `*-monoʳ-≤-nonNeg (1/ mfs)` applied to $0 \leq \text{realizedSurplus}(t)$ gives $0 \leq \text{realizedSurplus}(t) \times (1/\mathit{mfs})$.

*(Proved in `Efficiency.agda`.)*

---

### Theorem 5 — Structural Dominance

**Statement:** L3 guarantees non-negative surplus on every seed; L0 can produce a match where value is destroyed:

$$\underbrace{\forall t,\; 0 \leq \text{realizedSurplus}(t)}_{\text{L3 guarantee}} \;\times\; \underbrace{\exists m,\; v_s(m) > v_b(m)}_{\text{L0 failure witness}}$$

**Proof:** The left clause is Theorem 3. The right clause is proved constructively: in `witnessEnv` ($v_b = 1$, $v_s = 2$, $p_{\max} = 3$), seed `[1,0]` causes the L0 buyer to draw a bid of $3/4$ and the L0 seller to draw an ask of $0$. These cross ($0 \leq 3/4$), so a trade is recorded at surplus $v_b - v_s = 1 - 2 = -1 < 0$. The match object is constructed explicitly in `Flagship.agda`, and its surplus is evaluated at compile time by the Agda type-checker:

```agda
witnessSeedNegSurplus : l0RealizedSurplus (concreteL0Sim witnessEnv witnessSeed) <ℚ 0ℚ
```

Agda reduces the left-hand side fully and verifies the inequality holds — no separate test is needed.

---

### Theorem 6 — Pointwise Flagship

**Statement:** If $\exists s_0$ with $\text{l0Surplus}(s_0) < 0$, then $\exists s_0$ with $\text{l0Surplus}(s_0) < \text{l3Surplus}(s_0)$.

**Proof:** Take the *same* seed $s_0$ as the witness from the hypothesis. We have $\text{l0Surplus}(s_0) < 0$ by hypothesis and $0 \leq \text{l3Surplus}(s_0)$ by Theorem 3. Combining the strict inequality $\text{l0Surplus}(s_0) < 0$ with the non-strict inequality $0 \leq \text{l3Surplus}(s_0)$ via `<-≤-trans` gives $\text{l0Surplus}(s_0) < \text{l3Surplus}(s_0)$.

The key insight is that no new witness seed is required. The same seed that demonstrates L0's failure (drawing a bid above valuation and trading at a loss) immediately demonstrates L3's pointwise advantage, because L3 is guaranteed to produce $\geq 0$ at every seed.

---

### Theorem 7 — Expected Flagship (Conditional)

**Statement:** Suppose (i) $\exists s_0$ with $\text{l0Surplus}(s_0) < 0$, (ii) $\text{l0Surplus}(s) \leq \text{l3Surplus}(s)$ for all $s$, and (iii) $s_0 \in \Omega$ for some finite seed list $\Omega$. Then:

$$\mathbb{E}_\Omega[\text{l3Surplus}] > \mathbb{E}_\Omega[\text{l0Surplus}]$$

**Proof:** Hypothesis (ii) gives a pointwise bound. Hypothesis (i) together with Theorem 3 gives a strict inequality at $s_0$: $\text{l0Surplus}(s_0) < 0 \leq \text{l3Surplus}(s_0)$. Hypothesis (iii) ensures $s_0$ contributes to the sum. A strict inequality at one term and $\leq$ everywhere else in a finite sum yields a strict inequality of sums — proved in Agda as `sumQ-map-strict-mono`, which requires both the pointwise $\leq$ (hypothesis ii) and the strict witness.

**Caveat:** Hypothesis (ii) — pointwise dominance of L3 over L0 *everywhere* — fails in productive markets ($v_b > v_s$). The `marketEnv` simulation exhibits seeds where L0 produces strictly higher surplus than L3. Theorem 7 is therefore a conditional result. The main FSD theorem below is the unconditional strengthening that avoids this hypothesis entirely.

---

### Theorem: `l0Nonpos-inverted`

**Statement:** In any environment where $v_b \leq v_s$ (an *inverted* market): for all seeds $s$,

$$\text{l0RealizedSurplus}(\text{concreteL0Sim}(s)) \leq 0$$

**Proof:** Case split on whether the L0 agents cross:

- *No trade ($\text{ask} > \text{bid}$):* The realized surplus is 0 (sum over an empty trade list). Since $0 \leq 0$, the bound holds trivially.
- *Trade ($\text{ask} \leq \text{bid}$):* The realized surplus is $v_b - v_s$. The inverted-market hypothesis gives $v_b \leq v_s$, so $v_b - v_s \leq 0$.

**Technical note on the case split:** The proof matches on `askP ≤? bidP` — the internal decidable crossing condition inside `tryL0Match` — rather than on the output of `tryL0Match`. Matching on `tryL0Match ... = just m` would leave the fields of `m` opaque to the type-checker, blocking the simplification `rawSurplus m = v_b - v_s`. Matching on the internal discriminant forces definitional reduction of the record fields, making the arithmetic transparent. This is why `l0Nonpos-inverted` is proved inside `L0AgentStrategy.agda` (where the `fromMaybe` helper is in scope) rather than in a downstream module.

---

### Theorem: FSD — Main Result

**Statement:** In any inverted market ($v_b \leq v_s$), for any seed population $\Omega$:

$$\text{FSDom}\bigl(\text{realizedSurplus} \circ \text{concreteSim},\; \text{l0RealizedSurplus} \circ \text{concreteL0Sim},\; \Omega\bigr)$$

i.e., L3 first-order stochastically dominates L0 in inverted markets.

**Proof:** Apply `FSD-from-pointwise` to the pointwise bound:

$$\text{l0RealizedSurplus}(s) \leq 0 \leq \text{l3RealizedSurplus}(s) \quad \forall s$$

The left inequality is `l0Nonpos-inverted`. The right inequality is `realizedSurplusNonNeg` (Theorem 3). Since both hold for every seed, `FSD-from-pointwise` lifts pointwise dominance to FSD over any finite $\Omega$.

This is the structural core of the result. The proof does not reason about distributions or probabilities directly. Instead, a simple pointwise sandwich — L0 always $\leq 0$, L3 always $\geq 0$ — immediately yields the full distributional dominance. The sandwich holds because the inverted-market hypothesis forbids L0 from profiting on any trade and the L3 constraint forbids L3 from losing on any trade.

---

### Theorem: Expected Value — Corollary

**Statement:** In any inverted market, for any $\Omega$:

$$\mathbb{E}_\Omega[\text{L0 surplus}] \leq \mathbb{E}_\Omega[\text{L3 surplus}]$$

Formally: $\text{sumQ}(\text{map}\ (\text{l0Surplus} \circ \text{concreteL0Sim})\ \Omega) \leq \text{sumQ}(\text{map}\ (\text{l3Surplus} \circ \text{concreteSim})\ \Omega)$.

**Proof:** By `sumQ-map-mono` applied to the same pointwise bound used for FSD: $\text{l0Surplus}(s) \leq 0 \leq \text{l3Surplus}(s)$. Monotonicity of `sumQ` under a pointwise $\leq$ follows from the monotonicity of $+$ over rationals.

**Relationship to FSD:** FSD is strictly stronger than expected-value dominance: $\mathbb{E}[f] \geq \mathbb{E}[g]$ follows from $\text{FSDom}(f, g)$, but not conversely. This corollary is therefore implied by the FSD result above and costs no additional work. It also closes the gap left by Theorem 7, which required the false hypothesis of global pointwise dominance.

---

### Theorem: Symmetric FSD — Productive Markets

**Statement:** In any productive market ($v_s \leq v_b$, with $0 \leq v_s$ and $\text{cap} \leq p_{\max}$), for any $\Omega$:

$$\text{FSDom}\bigl(\text{l0RealizedSurplus} \circ \text{concreteL0Sim},\; \text{realizedSurplus} \circ \text{concreteSim},\; \Omega\bigr)$$

i.e., L0 first-order stochastically dominates L3 in productive markets.

**Proof:** Apply `FSD-from-pointwise` using the pointwise bound `l3LE-l0-productive`: $\text{L3}(s) \leq \text{L0}(s)$ for all seeds $s$.

The key arithmetic chain in `l3LE-l0-productive`: suppose L3 agents cross (i.e., $\text{L3\_ask} \leq \text{L3\_bid}$). Then:

$$\text{L0\_ask} \leq \text{L3\_ask} \leq \text{L3\_bid} \leq \text{L0\_bid}$$

The outer inequalities hold because L0 draws from the full grid while L3 restricts buyers to $[0, v_b]$ and sellers to $[v_s, p_{\max}]$: L0 ask can be as low as 0 (below L3's floor of $v_s$), and L0 bid can be as high as $p_{\max}$ (above L3's cap of $v_b$). So whenever L3 crosses, L0 also crosses — producing the same trade surplus $v_b - v_s$, since the surplus depends only on the environment, not the mechanism. But there are additional seeds where L0 crosses and L3 does not, because L0's wider range captures bid-ask pairs that L3's constraints exclude. Therefore $\text{L3}(s) \leq \text{L0}(s)$ for every seed.

**Economic interpretation:** The L3 constraint is uniformly tighter than L0. In productive markets, this tightness is a liability: it turns away value-creating trades that L0 would execute. The two FSD results together draw a clean crossover: L3 dominates when trades would destroy value ($v_b \leq v_s$), L0 dominates when trades create value ($v_s \leq v_b$).

---

### Theorem: Multi-Agent FSD — Inverted Markets

**Statement:** For any $k$ buyer-seller pairs with independent seeds and `AllInverted` conditions ($v_{b,i} \leq v_{s,i}$ for all $i$), and any multi-seed population $\Omega$:

$$\text{FSDom}\bigl(\text{realizedSurplusN}\ \text{envs},\; \text{l0RealizedSurplusN}\ \text{envs},\; \Omega\bigr)$$

where $\text{realizedSurplusN}\ \text{envs}\ \mathbf{s} = \sum_{i=1}^{k} \text{realizedSurplus}(\text{concreteSim}\ e_i\ s_i)$ and similarly for L0.

**Proof:** Apply `FSD-from-pointwise` to the portfolio-level pointwise bound `l0LEL3-invertedN`:

$$\text{l0RealizedSurplusN}(\text{envs}, \mathbf{s}) \leq \text{realizedSurplusN}(\text{envs}, \mathbf{s}) \quad \forall \mathbf{s}$$

`l0LEL3-invertedN` is proved by induction on the `Vec` of environments:

- *Base case* (empty portfolio): both sums are 0, and $0 \leq 0$.
- *Inductive step*: pair $i$ satisfies `l0Nonpos-inverted` ($\text{L0}_i(s_i) \leq 0$) and `realizedSurplusNonNeg` ($0 \leq \text{L3}_i(s_i)$), giving the single-pair pointwise bound. The inductive hypothesis gives the bound for the remaining pairs. Adding these via `+-mono-≤` lifts to the full portfolio sum.

The key structural lemma `realizedSurplus-++` ensures that realized surplus over a concatenated trace equals the sum of realized surpluses over the component traces. This connects the multi-agent `Trace` output (a single list of all events) to the per-pair sum that the proof reasons about.

---

### Theorem: Multi-Agent FSD — Productive Markets

**Statement:** For any $k$ pairs with `AllProductive` conditions ($0 \leq v_{s,i}$, $v_{s,i} \leq v_{b,i}$, $\text{cap}_i \leq p_{\max,i}$ for all $i$), and any $\Omega$:

$$\text{FSDom}\bigl(\text{l0RealizedSurplusN}\ \text{envs},\; \text{realizedSurplusN}\ \text{envs},\; \Omega\bigr)$$

**Proof:** Apply `FSD-from-pointwise` to `l3LEL0-productiveN`. This bound is proved by the same Vec induction as in the inverted case, but using `l3LE-l0-productive` (the single-pair productive-market result) at each pair and `+-mono-≤` to lift to portfolio sums.

---

### Theorems: Multi-Agent Expected Value

**Inverted markets:** For any $k$ pairs with `AllInverted` conditions and any $\Omega$:

$$\sum_{\mathbf{s} \in \Omega} \text{l0RealizedSurplusN}(\text{envs}, \mathbf{s}) \leq \sum_{\mathbf{s} \in \Omega} \text{realizedSurplusN}(\text{envs}, \mathbf{s})$$

**Productive markets:** For any $k$ pairs with `AllProductive` conditions and any $\Omega$: the symmetric inequality $\mathbb{E}_\Omega[\text{L0}] \geq \mathbb{E}_\Omega[\text{L3}]$.

**Proof (both):** `sumQ-map-mono` applied to the respective portfolio-level pointwise bounds (`l0LEL3-invertedN` and `l3LEL0-productiveN`). Since FSD implies expected-value dominance, both corollaries follow from the FSD results above without additional work.

*Extension structure:* `MultiAgentSim.agda` adds all multi-agent results with zero changes to any existing module. The $k=1$ case of each multi-agent theorem recovers the corresponding single-pair result from `Stochastic.agda`.

---

### Theorems: Efficiency FSD — Inverted and Productive Markets

**Inverted market statement:** For any environment with $v_b \leq v_s$, profitable-pair list $\mathit{ps}$ with $\mathit{mfs} > 0$, and $\Omega$:

$$\text{FSDom}\bigl(\text{concreteL3Eff},\; \text{concreteL0Eff},\; \Omega\bigr)$$

where $\text{concreteL3Eff}(s) = \text{realizedSurplus}(\text{concreteSim}(s)) \div \mathit{mfs}$, and similarly for L0.

**Proof:** Apply `FSD-from-pointwise` to the efficiency-ratio bound $\text{concreteL0Eff}(s) \leq \text{concreteL3Eff}(s)$. This bound follows from the raw surplus bounds $\text{L0}(s) \leq 0 \leq \text{L3}(s)$, lifted to efficiency ratios by `*-monoʳ-≤-nonNeg (1/ mfs)`. The definitional equality $a \div c = a \times (1/c)$ lets the proof avoid the `_÷_` operator's instance-search issues in return types (see Key Technical Decisions).

**Productive market statement:** For any environment with $v_s \leq v_b$, $0 \leq v_s$, $\text{cap} \leq p_{\max}$, $\mathit{mfs} > 0$, and $\Omega$:

$$\text{FSDom}\bigl(\text{concreteL0Eff},\; \text{concreteL3Eff},\; \Omega\bigr)$$

**Proof:** `FSD-from-pointwise` using `l3LE-l0-productive` lifted by `*-monoʳ-≤-nonNeg (1/ mfs)`. Identical in structure to the inverted-market case.

*Gode & Sunder connection:* This is the formal analogue of G&S's headline result: unrestricted ZIT agents in productive markets achieve higher (in the FSD sense) efficiency ratios than constrained agents. The institution sets the price; the L3 constraint only limits *when* agents can trade.

**Corollary — Expected Efficiency:** Both FSD results yield expected-efficiency corollaries by `sumQ-map-mono`:

- Inverted: $\mathbb{E}_\Omega[\text{L3 efficiency}] \geq \mathbb{E}_\Omega[\text{L0 efficiency}]$
- Productive: $\mathbb{E}_\Omega[\text{L0 efficiency}] \geq \mathbb{E}_\Omega[\text{L3 efficiency}]$

*Note on $\mathit{mfs} > 0$:* In a strictly inverted single-pair market the max feasible surplus is 0, making the efficiency ratio undefined. The inverted theorem carries `mfs > 0` as an explicit hypothesis, which is satisfied when the profitable-pair list draws from a parallel productive sub-market.

*Extension structure:* `EfficiencyFSD.agda` adds all efficiency results with zero changes to any existing module. Every proof composes an existing surplus-level lemma with monotonicity of multiplication by a non-negative scalar.

---

### Theorems: k-Pair Efficiency FSD

**Inverted markets:** For any $k$ pairs with `AllInverted` conditions, $\mathit{mfs} > 0$, and $\Omega$:

$$\text{FSDom}\bigl(\text{concreteL3EffN},\; \text{concreteL0EffN},\; \Omega\bigr)$$

where $\text{concreteL3EffN}(\mathbf{s}) = \text{realizedSurplusN}(\text{envs}, \mathbf{s}) \div \mathit{mfs}$, and similarly for L0.

**Proof:** Apply `FSD-from-pointwise` to the portfolio efficiency bound. The bound is the portfolio raw-surplus bound from Multi-Agent FSD (proved by the same Vec induction), lifted by `*-monoʳ-≤-nonNeg (1/ mfs)`.

The symmetric result holds for productive markets. Both have expected-efficiency corollaries by `sumQ-map-mono`.

*Extension structure:* `MultiAgentEffFSD.agda` closes the 2×2 coverage table — every combination of scope (single pair / $k$ pairs) and metric (raw surplus / efficiency ratio) has both FSD and expected-value theorems. The $k=1$ case of each multi-agent theorem recovers the corresponding single-pair result from `EfficiencyFSD.agda`.

|                  | Single pair       | $k$ pairs              |
|------------------|-------------------|------------------------|
| Raw surplus FSD  | `Stochastic` ✓    | `MultiAgentSim` ✓      |
| Efficiency FSD   | `EfficiencyFSD` ✓ | `MultiAgentEffFSD` ✓   |

---

### Theorem: Oracle Mix Welfare — Mixed Markets

**Statement:** In a market with $k$ pairs where each is either inverted or productive, the **oracle mix** strategy — L3 on inverted pairs, L0 on productive pairs — FSD-dominates both pure strategies simultaneously:

$$\text{FSDom}\bigl(\text{concreteMixSurplusN},\; \text{realizedSurplusN},\; \Omega\bigr) \qquad \text{(mix} \succcurlyeq \text{pure L3)}$$

$$\text{FSDom}\bigl(\text{concreteMixSurplusN},\; \text{l0RealizedSurplusN},\; \Omega\bigr) \qquad \text{(mix} \succcurlyeq \text{pure L0)}$$

*Oracle mix:* for each pair $i$, apply L3 if $v_{b,i} \leq v_{s,i}$ and L0 if $v_{s,i} \leq v_{b,i}$.

**Proof:** Apply `FSD-from-pointwise` to the pointwise bounds, proved by induction on the `Mixed` predicate (which classifies each pair as either `invMix` or `prodMix`):

- *`invMix` pair:* The oracle mix uses L3 for this pair. Mix vs. pure L3: both deploy L3, so their contributions are equal ($\leq$-refl, in both directions). Mix vs. pure L0: `l0Nonpos-inverted` gives L0 $\leq 0$ and `realizedSurplusNonNeg` gives $0 \leq$ L3 = mix, so L0 $\leq$ mix.
- *`prodMix` pair:* The oracle mix uses L0 for this pair. Mix vs. pure L0: both deploy L0, so contributions are equal ($\leq$-refl). Mix vs. pure L3: `l3LE-l0-productive` gives L3 $\leq$ L0 = mix.

**Economic interpretation:** Pure L3 leaves productive-market gains on the table. Pure L0 executes inverted-market trades that destroy value. The oracle mix strictly dominates both: it uses each rule precisely where it is optimal. This establishes an impossibility result for pure strategies and a constructive optimality result for the oracle.

*Generalization:* When all pairs are inverted, `concreteMixSurplusN = realizedSurplusN` and `mixFSDom-l0` recovers `l3FSDom-l0-invertedN`. When all pairs are productive, `concreteMixSurplusN = l0RealizedSurplusN` and `mixFSDom-l3` recovers `l0FSDom-l3-productiveN`. `MixedWelfare` therefore strictly generalises `MultiAgentSim`.

Plus expected-welfare corollaries `mixExpected-l3` and `mixExpected-l0`.

---

### Theorem: Oracle Mix Efficiency FSD — Mixed Markets

**Statement:** The oracle mix also dominates both pure strategies in the efficiency ratio metric:

$$\text{FSDom}\bigl(\text{concreteMixEffN},\; \text{concreteL3EffN},\; \Omega\bigr) \quad \text{(mix efficiency} \succcurlyeq \text{L3 efficiency)}$$

$$\text{FSDom}\bigl(\text{concreteMixEffN},\; \text{concreteL0EffN},\; \Omega\bigr) \quad \text{(mix efficiency} \succcurlyeq \text{L0 efficiency)}$$

where $\text{concreteMixEffN}(\mathbf{s}) = \text{concreteMixSurplusN}(\text{envs}, h, \mathbf{s}) \div \mathit{mfs}$.

**Proof:** Lift the raw-surplus pointwise bounds (`l3LE-mix`, `l0LE-mix`) by `*-monoʳ-≤-nonNeg (1/ mfs)`, exactly as in the efficiency modules.

Plus expected-efficiency corollaries `mixEffExpected-l3` and `mixEffExpected-l0`.

This completes the full 3D result table:

|                  | Single pair       | $k$ pairs              | Mixed market      |
|------------------|-------------------|------------------------|-------------------|
| Raw surplus FSD  | `Stochastic` ✓    | `MultiAgentSim` ✓      | `MixedWelfare` ✓  |
| Efficiency FSD   | `EfficiencyFSD` ✓ | `MultiAgentEffFSD` ✓   | `MixedEffFSD` ✓   |

---

### Theorem: Pure Strategy Incomparability — Mixed Markets

**Statement:** In any mixed market, neither pure strategy FSD-dominates the other:

$$\lnot\;\text{FSDom}\bigl(\text{l0RealizedSurplusN},\; \text{realizedSurplusN},\; [\mathbf{s}_1]\bigr) \qquad \text{given } \text{L0}(\mathbf{s}_1) < 0$$

$$\lnot\;\text{FSDom}\bigl(\text{realizedSurplusN},\; \text{l0RealizedSurplusN},\; [\mathbf{s}_2]\bigr) \qquad \text{given } \text{L3}(\mathbf{s}_2) < \text{L0}(\mathbf{s}_2)$$

Both hypotheses can be satisfied simultaneously in any market with at least one inverted pair (where L0 can produce negative surplus) and at least one productive pair (where L3 is strictly worse than L0).

**Proof of `l0NotFSDom-l3-mixed`:** FSDom requires that at *every* threshold the L0 survival count is at least the L3 survival count. We exhibit a threshold that defeats this. Take $t = 0$:

$$\text{survivalCount}(\text{L3}, [\mathbf{s}_1], 0) = 1 \qquad \text{since L3} \geq 0 \text{ always (by \texttt{realizedSurplusN-nonNeg})}$$

$$\text{survivalCount}(\text{L0}, [\mathbf{s}_1], 0) = 0 \qquad \text{since L0}(\mathbf{s}_1) < 0 \text{ by hypothesis}$$

FSDom would require $1 \leq 0$ in $\mathbb{N}$ — a contradiction, since $\mathbb{N}$ is ordered and $1 \not\leq 0$.

**Proof of `l3NotFSDom-l0-mixed`:** Take $t = \text{L0}(\mathbf{s}_2)$:

$$\text{survivalCount}(\text{L0}, [\mathbf{s}_2], t) = 1 \qquad \text{since } \text{L0}(\mathbf{s}_2) \geq t \text{ by } \leq\text{-refl}$$

$$\text{survivalCount}(\text{L3}, [\mathbf{s}_2], t) = 0 \qquad \text{since } \text{L3}(\mathbf{s}_2) < t \text{ by hypothesis}$$

Again FSDom would require $1 \leq 0$ — absurd.

**Economic interpretation:** In a mixed market, no pure strategy is globally best. The oracle mix from `MixedWelfare` and `MixedEffFSD` is the minimal construction that dominates both. `PureStrategyIncomparable` closes the logical picture: the 3D table records what *is* true (oracle mix dominates everything), and this negative result records what is *not* true (no pure strategy achieves global dominance).

---

## Module Structure

The proof develops across 23 modules, building from primitive types to the final stochastic dominance theorems.

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
Stochastic.agda               — survivalCount; FSDom; l3FSDom-l0-inverted;
                                 l3Expected-l0-inverted; l0FSDom-l3-productive
MultiAgentSim.agda            — k-pair extension; AllInverted/AllProductive;
                                 l3FSDom-l0-invertedN; l0FSDom-l3-productiveN;
                                 l3ExpectedN-l0-inverted; l0ExpectedN-l3-productive
EfficiencyFSD.agda            — Efficiency ratio FSD; l3EffFSDom-l0-inverted;
                                 l0EffFSDom-l3-productive; expected-efficiency corollaries
MultiAgentEffFSD.agda         — k-pair efficiency FSD; l3EffFSDom-l0-invertedN;
                                 l0EffFSDom-l3-productiveN; expected corollaries
MixedWelfare.agda             — Oracle-mix welfare; Mixed predicate; mixFSDom-l3;
                                 mixFSDom-l0; expected corollaries
MixedEffFSD.agda              — Oracle-mix efficiency FSD; concreteMixEffN;
                                 mixEffFSDom-l3; mixEffFSDom-l0; expected corollaries
PureStrategyIncomparable.agda — Negative result: l0NotFSDom-l3-mixed; l3NotFSDom-l0-mixed
Main.agda                     — Executable: runs both environments over all 16 seeds (n=3)
```

---

## What "Formal Proof" Means Here

In Agda, proofs and programs are the same thing (Curry–Howard correspondence). A theorem like

```agda
surplusNonNeg : ∀ (m : Match) → 0ℚ ≤ surplus m
surplusNonNeg m = p≤q⇒0≤q-p (valuationChain m)
```

is simultaneously a function definition and a proof. The *type* is the statement; the *term* is the proof. Agda's type-checker accepting the file is equivalent to checking the proof for all matches simultaneously.

**Key consequences:**

- **No case is missed.** Pattern matching must be exhaustive; the type-checker enforces it. A case analysis with a missing branch is a compile error, not a latent bug.
- **No uncertified trade can enter a Trace.** The `TradeSettled` constructor requires a `Match` value, and a `Match` can only be constructed by providing admissibility evidence. It is structurally impossible to build a trace containing an uncertified event.
- **The witness is concrete.** `witnessSeedNegSurplus` is proved by Agda evaluating `l0RealizedSurplus (concreteL0Sim witnessEnv witnessSeed) <? 0ℚ` to `yes proof` at compile time. The computation runs inside the type-checker; no separate test harness is needed.

---

## Sample Output

```
=== Environment 1: witness (v_buyer=1, v_seller=2, maxP=3) ===
  L0 bid/ask from full grid {0, 3/4, 3/2, 9/4}
  L3 buyer bids in {0, 1/4, 1/2, 3/4}  (cap at v=1)
  L3 seller asks in {2, 9/4, 5/2, 11/4} (floor at v=2)
  Result: L3 never trades; L0 trades and destroys value

  seed   bid      ask      L0       L3
  [0,0]  bid=0/1  ask=0/1  L0=0/1   L3=0/1
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

**`isYes` vs `does` for decidable comparisons.** The Agda stdlib `Dec` record has a field `does : Bool`. After a `with` abstraction, `does` does not reduce. `isYes` is a separate pattern-matching function (`isYes (no _) = false`) that *does* reduce. The `survivalCount` predicate uses `isYes` for this reason: definitional reduction is required for the proof that survival counts are computable from their Boolean representations.

**Private helpers and definitional opacity.** The `fromMaybe` helper in `L0AgentStrategy` is private. Proofs that depend on its reduction (`fromMaybe (just m) = m ∷ []`) must live inside the same module. `l0Nonpos-inverted` is therefore proved in `L0AgentStrategy.agda` and exported as a closed term.

**Case-splitting on the internal discriminant.** Rather than matching on `tryL0Match ... = just m` (which leaves `m` opaque), `l0Nonpos-inverted` matches on `askP ≤? bidP` — the same `with` scrutinee inside `tryL0Match`. This forces the record fields to reduce, making `rawSurplus m = v_b - v_s` definitionally, which is what the arithmetic proof requires.

**`÷` in return types and Pi-bound instances.** The standard library `_÷_` operator requires `{{NonZero q}}` at every use site, including inside type signatures. An anonymous Pi-bound instance `→ {{NonZero c}} →` is not reliably found by instance search when `a ÷ c` appears in the same signature's return type. Workaround: since `a ÷ c = a * (1/ c)` definitionally, use `ℚP.*-monoʳ-≤-nonNeg (1/ c)` directly and supply the full instance chain (`>-nonZero`, `positive`, `1/pos⇒pos`, `pos⇒nonNeg`) in the `where` block of each call site. Agda accepts the result by definitional equality.

**Cross-module infix constructor with product argument.** The `AllProductive` constructor `_ap∷_` (defined in `MultiAgentSim`) bundles three conditions as a right-associated product. When imported into another module, the pattern `((hVS , hProd , hCap) ap∷ hs)` on a function LHS causes a parse error — the comma-separated triple conflicts with the infix constructor at the operator precedence level. Solution: match `(hconds ap∷ hs)` and extract components with `proj₁`/`proj₂`.

---

## References

- Gode, D. K. & Sunder, S. (1993). "Allocative Efficiency of Markets with Zero-Intelligence Traders." *Journal of Political Economy*, 101(1), 119–137.
- Agda documentation: <https://agda.readthedocs.io/>
- Agda standard library: <https://agda.github.io/agda-stdlib/>
