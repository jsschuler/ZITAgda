# ZITAgda — Mathematical Development Log

## Primitive Types

| Symbol | Agda | Meaning |
|--------|------|---------|
| $\mathbb{N}$ | `ℕ` | Natural numbers (non-negative integers) |
| $\mathbb{Q}$ | `ℚ` | Rational numbers (exact, no floating-point) |
| $\top$ | `⊤` | Unit type / logical True (one proof: `tt`) |
| $\bot$ | `⊥` | Empty type / logical False (no proofs) |
| $A \wedge B$ | `A × B` | Conjunction; proven by a pair $(a, b)$ |
| $A \vee B$ | `A ⊎ B` | Disjunction; proven by $\text{inl}(a)$ or $\text{inr}(b)$ |

---

## Module 1: Agent

### Definitions

**Role**

$$\text{Role} ::= \text{Buyer} \mid \text{Seller}$$

**Valuation Schedule**

For Phase 1 (one-unit traders), a valuation schedule is simply a unit value:
$$v : \mathbb{Q}$$

**Agent**

$$\text{Agent} = \left\{ (i,\, r,\, v,\, b,\, \text{inv}) \;\middle|\; i \in \mathbb{N},\; r \in \text{Role},\; v \in \mathbb{Q},\; b \in \mathbb{Q},\; \text{inv} \in \mathbb{N} \right\}$$

where:
- $i$ — trader identifier
- $r$ — role (Buyer or Seller)
- $v$ — unit valuation $v(1)$ (private value of one unit)
- $b$ — budget (cash on hand)
- $\text{inv}$ — inventory (units held)

---

## Module 2: Proposal

### Definitions

**Proposal**

A raw proposal is a triple submitted by a trader to the institution:
$$\pi = (i,\, p,\, r) \qquad i \in \mathbb{N},\; p \in \mathbb{Q},\; r \in \text{Role}$$

Proposals are *raw* — they may violate economic constraints. The institution checks admissibility.

---

### Constraint Levels

**L0 — Unconstrained**

$$\text{L0}(a, \pi) \equiv \top$$

Every proposal satisfies L0. Agents draw prices from a distribution with no economic content.

---

**L3 — Valuation + Budget/Inventory Constrained**

$$\text{L3}(a, \pi) \equiv \begin{cases}
\pi.p \leq v_a(1) \;\wedge\; \pi.p \leq b_a & \text{if } a.r = \text{Buyer} \\[4pt]
v_a(1) \leq \pi.p \;\wedge\; \text{inv}_a > 0 & \text{if } a.r = \text{Seller}
\end{cases}$$

Buyers do not bid above their valuation or beyond their budget.
Sellers do not ask below their reservation value and must hold inventory.

**Remark (Dependent Types).** In Agda, $\text{L3}(a, \pi)$ is not a Boolean predicate but a *type*. The type depends on the *value* of $a.\text{role}$ — a Buyer and a Seller have structurally different constraints. A proof that $\pi$ satisfies L3 for agent $a$ is an *element* of the type $\text{L3}(a, \pi)$. This is the **Curry–Howard correspondence**:

$$\text{Propositions} \;\longleftrightarrow\; \text{Types} \qquad \text{Proofs} \;\longleftrightarrow\; \text{Programs}$$

---

## Module 3: Seed

### Definitions

**Finite type $\text{Fin}\, n$**

$$\text{Fin}\, n \;=\; \{0, 1, \ldots, n-1\}$$

Defined inductively in Agda:
$$\text{Fin}\, 0 = \emptyset \qquad \text{Fin}(n+1) = \{\text{zero}\} \cup \{\text{suc}\, i \mid i \in \text{Fin}\, n\}$$

$\text{Fin}\, n$ is the canonical $n$-element type. A value of type $\text{Fin}\, n$ is a proof that an index is in range. Out-of-bounds indexing is a type error, not a runtime error.

**Length-indexed vector $\text{Vec}\, A\, n$**

$$\text{Vec}\, A\, n \;=\; \{(a_0, a_1, \ldots, a_{n-1}) \mid a_i \in A\}$$

The length $n$ is part of the type. `lookup : Vec A n → Fin n → A` is provably total — no bounds check required.

**Seed tape**

$$\text{Seed}(n, k) \;=\; \text{Vec}(\text{Fin}\, n,\, k)$$

A seed is a tape of $k$ draws, each uniformly selected from $\{0, \ldots, n-1\}$.

- $n$ — number of price ticks (granularity of the price grid)
- $k$ — number of draws (length of the tape)

**Seed space**

$$\Sigma(n, k) \;=\; \text{Seed}(n, k)$$

The seed space *is* the type. In constructive mathematics, a finite set and its type are the same object.

**Cardinality** (to be proved):

$$|\Sigma(n, k)| \;=\; n^k$$

**Draw function**

$$\text{drawAt} : \text{Seed}(n, k) \to \text{Fin}\, k \to \text{Fin}\, n$$
$$\text{drawAt}(s, j) \;=\; s[j]$$

Total by construction — $j : \text{Fin}\, k$ cannot be out of bounds.

### Probability

For a predicate $E : \text{Seed}(n,k) \to \text{Set}$ (an event):

$$\mathbb{P}(E) \;=\; \frac{|\{s \in \Sigma(n,k) \mid E(s)\}|}{n^k}$$

No measure theory. The denominator $n^k$ is the cardinality of the finite seed space.

**Universal quantification** over the seed space is the Agda proposition:
$$\forall\, (s : \Sigma(n,k)),\; P(s)$$
This is a type — its proof is a function that, given *any* seed, produces a proof of $P$.

---

## Module 4: Institution (Batch Clearing Auction)

### Definitions

**Buyer admissibility** (L3, buyer side)

For agent $a$ and proposal $\pi$, $a$ is buyer-admissible for $\pi$ if:
$$\text{BuyerAdm}(a, \pi) \;\equiv\; \pi.p \leq v_a(1) \;\wedge\; \pi.p \leq b_a$$

**Seller admissibility** (L3, seller side)

$$\text{SellerAdm}(a, \pi) \;\equiv\; v_a(1) \leq \pi.p \;\wedge\; \text{inv}_a > 0$$

**Match**

A match is a tuple $(a_b, a_s, \pi_b, \pi_s, c)$ with:
- $a_b, a_s$ — buyer and seller agents
- $\pi_b, \pi_s$ — their admitted proposals
- $c \in \mathbb{Q}$ — the clearing price

satisfying:
$$\text{BuyerAdm}(a_b, \pi_b) \quad \text{SellerAdm}(a_s, \pi_s)$$
$$\pi_s.p \leq \pi_b.p \qquad \pi_s.p \leq c \leq \pi_b.p$$

The type `Match` in Agda only contains tuples satisfying all these conditions. An inadmissible match is *unrepresentable*, not merely rejected.

---

### Theorem 1 — Valuation Chain

**Theorem.** For any match $m$:
$$v_{a_s}(1) \leq v_{a_b}(1)$$

**Proof.**
$$v_{a_s}(1) \;\underset{\text{SellerAdm}}{\leq}\; \pi_s.p \;\underset{\text{crosses}}{\leq}\; \pi_b.p \;\underset{\text{BuyerAdm}}{\leq}\; v_{a_b}(1)$$

Each step is an instance of the admissibility or crossing condition. The chain is assembled by two applications of transitivity of $\leq$ on $\mathbb{Q}$. $\square$

**Remark.** This is the entire proof. In Agda it is three lines:
```
≤-trans (≤-trans askAboveValue crosses) bidBelowValue
```
The proof term *is* the inequality chain. The type-checker verifying compilation is equivalent to checking the proof.

**Corollary** (proved in `Surplus.agda`).
$$\text{surplus}(m) \;:=\; v_{a_b}(1) - v_{a_s}(1) \;\geq\; 0$$

This follows from the theorem and the ordered-field axioms of $\mathbb{Q}$: $a \leq b \implies 0 \leq b - a$.

---

## Module 5: Surplus

**Definition.**
$$\text{surplus}(m) \;:=\; v_{a_b}(1) - v_{a_s}(1) \;\in\; \mathbb{Q}$$

**Arithmetic Lemma.**
$$\forall\, p, q \in \mathbb{Q},\quad p \leq q \;\implies\; 0 \leq q - p$$

*Proof.* Add $-p$ to both sides: $p + (-p) \leq q + (-p)$, i.e.\ $0 \leq q - p$. $\square$

In Agda this uses `subst` (Leibniz substitution): if $a = b$ and $P(a)$, then $P(b)$.

**Theorem 2 — Non-Negative Surplus.**
$$\forall\, m : \text{Match},\quad 0 \leq \text{surplus}(m)$$

*Proof.* Theorem 1 gives $v_s \leq v_b$. The arithmetic lemma gives $0 \leq v_b - v_s = \text{surplus}(m)$. $\square$

The Agda proof is a single function application: `p≤q⇒0≤q-p (valuationChain m)`.

---

## Module 6: Trace

### Event Vocabulary

$$\text{Event} ::= \text{OrderSubmitted}(i, \pi) \mid \text{OrderRejected}(i, \pi) \mid \text{OrderAccepted}(i, \pi) \mid \text{TradeSettled}(m) \mid \text{AuctionCleared}(c)$$

where $i \in \mathbb{N}$, $\pi \in \text{Proposal}$, $m \in \text{Match}$, $c \in \mathbb{Q}$.

A **trace** is a finite sequence of events: $\text{Trace} = \text{List}(\text{Event})$.

Because $\text{TradeSettled}(m)$ carries $m : \text{Match}$, and $\text{Match}$ already embeds the L3 proofs, every trace is *automatically certified*. No separate "certified trace" type is needed.

### Derived Views

$$\text{tradesView} : \text{Trace} \to \text{List}(\text{Match})$$

Extracts all $\text{TradeSettled}(m)$ events and returns their matches.

$$\text{sumSurplus} : \text{List}(\text{Match}) \to \mathbb{Q}$$

$$\text{sumSurplus}([]) = 0 \qquad \text{sumSurplus}(m :: ms) = \text{surplus}(m) + \text{sumSurplus}(ms)$$

$$\text{realizedSurplus} : \text{Trace} \to \mathbb{Q}$$

$$\text{realizedSurplus}(t) = \text{sumSurplus}(\text{tradesView}(t))$$

### Theorem 3 — Non-Negative Realized Surplus

**Theorem.** For any list of L3 matches $ms$:
$$\text{sumSurplus}(ms) \geq 0$$

**Proof** by structural induction on $ms$.

- *Base:* $\text{sumSurplus}([]) = 0 \geq 0$. $\square$
- *Step:* Let $ms = m :: ms'$. Then:
$$\text{sumSurplus}(m :: ms') = \underbrace{\text{surplus}(m)}_{\geq\, 0\;\text{(Thm 2)}} + \underbrace{\text{sumSurplus}(ms')}_{\geq\, 0\;\text{(IH)}} \geq 0 \quad\square$$

**Corollary.** $\text{realizedSurplus}(t) \geq 0$ for any trace $t$.

**Remark.** In Agda, proof by induction and definition by recursion are the *same syntactic construction*. The `[]` and `(m ∷ ms)` cases of `sumSurplusNonNeg` are simultaneously the base case and inductive step. There is no separate "by induction" keyword — the recursion structure *is* the induction.

---

## Module 9: Flagship — Structural Dominance

### L0 (Raw Match)

A **raw match** is a crossed pair $(a_b, a_s, \pi_b, \pi_s, c)$ with $\pi_s.p \leq \pi_b.p$ and $c \in [\pi_s.p, \pi_b.p]$, carrying **no admissibility proofs**. Under L0 the institution imposes no constraints; any crossing pair is matched.

**Raw surplus** (can be negative):
$$\text{rawSurplus}(m) := v_{a_b}(1) - v_{a_s}(1) \in \mathbb{Q}$$

### Witness

The following L0 match has $v_s > v_b$:

| Agent | Valuation | Proposal |
|-------|-----------|----------|
| Buyer | $v_b = 1$ | bid $= 3$ (above valuation) |
| Seller | $v_s = 2$ | ask $= 0$ (below cost) |

Crossing: $0 \leq 3$ ✓. Clearing price $c = 1 \in [0, 3]$ ✓.
$$\text{rawSurplus}(\text{witness}) = 1 - 2 = -1 < 0$$

Proved by `toWitness` — Agda evaluates the decision procedure $1 \stackrel{?}{<} 2$ at compile time. A false witness would be a type error.

### Theorem 5 — Structural Dominance

$$\underbrace{\forall\, t : \text{Trace},\quad 0 \leq \text{realizedSurplus}(t)}_{\text{L3 structural guarantee}} \quad\times\quad \underbrace{\exists\, m : \text{RawMatch},\quad v_s(m) > v_b(m)}_{\text{L0 failure witness}}$$

The L3 claim is Theorem 3. The L0 claim is the explicit witness above.

**The flagship efficiency inequality** $\mathbb{E}[\text{Eff}(\text{L3})] > \mathbb{E}[\text{Eff}(\text{L0})]$ follows from this structural separation together with:
- A probability model (uniform draws over the seed space)
- A simulation model (agents drawing prices from seeds)
- Proof that L0 assigns positive probability to negative-surplus events

These are the subjects of modules `Probability.agda`, `SimulationModel.agda`, `PriceGrid.agda`, `AgentStrategy.agda`, `BatchAuction.agda`, and `FlagshipFull.agda`.

---

## Module 10: Probability

**Sum over a list of rationals:**
$$\text{sumQ}([]) = 0 \qquad \text{sumQ}(x :: xs) = x + \text{sumQ}(xs)$$

**Theorem (Non-Negative Sum).** $\text{All}(0 \leq\_)\, xs \implies 0 \leq \text{sumQ}(xs)$

**Theorem (Strict Monotonicity).** If $xs_i \leq ys_i$ for all $i$ and $xs_j < ys_j$ for some $j$, then $\text{sumQ}(xs) < \text{sumQ}(ys)$.

**Expected value** (counting form): $\mathbb{E}_\Omega[f] = \text{sumQ}(\text{map}\, f\, \Omega) / |\Omega|$. Comparing expectations over the same $\Omega$ reduces to comparing sums.

---

## Module 11: SimulationModel

Let $\text{SimFnL3}(n,k) = \text{Seed}(n,k) \to \text{Trace}$ and $\text{SimFnL0}(n,k) = \text{Seed}(n,k) \to \text{List(RawMatch)}$.

### Theorem 6 — Pointwise Flagship

**Theorem.** Given:
1. $\text{simL3}$, $\text{simL0}$ simulation functions
2. $\exists\, s_0 : \text{l0Surplus}(\text{simL0}(s_0)) < 0$

Then $\exists\, s_0 : \text{l0Surplus}(\text{simL0}(s_0)) < \text{realizedSurplus}(\text{simL3}(s_0))$.

*Proof.* Take $s_0$ from (2). Then $\text{l0Surplus}(s_0) < 0 \leq \text{l3Surplus}(s_0)$ by `<-≤-trans`. $\square$

### Theorem 7 — Expected Flagship (Conditional)

**Theorem.** Given additionally:
4. $\forall s : \text{l0Surplus}(\text{simL0}(s)) \leq \text{realizedSurplus}(\text{simL3}(s))$ (pointwise dominance)

Then for any finite seed list $\Omega = s_0 :: \Omega'$:
$$\text{sumQ}(\text{map}\, \text{l0Surplus} \circ \text{simL0}\, \Omega) < \text{sumQ}(\text{map}\, \text{l3Surplus} \circ \text{simL3}\, \Omega)$$

Dividing by $|\Omega| > 0$ gives $\mathbb{E}[\text{Eff}(\text{L3})] > \mathbb{E}[\text{Eff}(\text{L0})]$.

*Proof.* The pointwise dominance plus the strict witness at $s_0$ form `StrictAt` evidence; apply `sumQStrict`. $\square$

**Hypothesis (4)** is stated as an explicit condition, not derived. Verifying it for a concrete auction algorithm is left for `BatchAuction.agda`.

---

---

## Module 12: PriceGrid

### Definitions

**Unit ratio**

For grid resolution $n$ and index $i : \text{Fin}(\text{suc}\, n)$:
$$\text{ratio}(n, i) \;=\; \frac{\text{toℕ}\, i}{\text{suc}\, n} \;\in\; \mathbb{Q}$$

The index ranges over $\{0, 1, \ldots, n\}$, giving ratios $\{0, \tfrac{1}{n+1}, \ldots, \tfrac{n}{n+1}\}$. The grid is strictly below 1 — no agent ever quotes exactly at the ceiling.

**Tick function** (price at cap $c$ and index $i$):
$$\text{tick}(n, c, i) \;=\; c \cdot \text{ratio}(n, i)$$

**Buyer tick** (capped at $\min(v, b)$ where $v$ = valuation, $b$ = budget):
$$\text{buyerTick}(n, v, b, i) \;=\; \text{tick}(n,\, v \sqcap b,\, i)$$

**Seller tick** (offset from valuation $v$ up to market maximum $M$):
$$\text{sellerTick}(n, v, M, i) \;=\; v + (M - v) \cdot \text{ratio}(n, i)$$

### Theorems

**Theorem (ratio ≥ 0).** $0 \leq \text{ratio}(n, i)$ for all $n, i$.

*Proof.* $\text{ratio}(n,i) = \text{normalize}(\text{toℕ}\, i, \text{suc}\, n)$ and `normalize-nonNeg` gives `NonNegative`. $\square$

---

**Theorem (ratio ≤ 1).** $\text{ratio}(n, i) \leq 1$ for all $n, i$.

*Proof.* The ℚ ordering is defined by cross-multiplication:
$$p \leq q \;\iff\; \uparrow\!p \cdot \downarrow\!q \;\leq_\mathbb{Z}\; \uparrow\!q \cdot \downarrow\!p$$
where $\uparrow$ and $\downarrow$ are the (gcd-reduced) numerator and denominator. For $p = \text{ratio}(n,i)$ and $q = 1$, the condition becomes $N \leq D$ where $N = \uparrow(\text{normalize}(m,d))$ and $D = \downarrow(\text{normalize}(m,d))$ with $m = \text{toℕ}\, i$, $d = \text{suc}\, n$.

Let $G = \gcd(m, d)$. The library lemmas give:
$$N \cdot G = m \qquad D \cdot G = d$$
Since $m = \text{toℕ}\, i < \text{suc}\, n = d$, we have $m \leq d$, so $N \cdot G \leq D \cdot G$. Since $G > 0$ (the gcd of $d = \text{suc}\, n > 0$ is positive), we cancel: $N \leq D$. $\square$

**Remark.** This is the only proof in the project that descends into the gcd-reduced internal representation of $\mathbb{Q}$. The key Agda mechanisms are `subst₂` (rewrite in a binary relation), `*-cancelʳ-≤-pos` (cancel a positive factor from both sides of $\leq$), and the `*≤*` constructor (package the cross-multiplication inequality as a $\mathbb{Q}$ ordering proof).

**Theorem (tick ≤ cap).** If $0 \leq c$ then $\text{tick}(n, c, i) \leq c$.

*Proof.* $c \cdot \text{ratio} \leq c \cdot 1 = c$ by `*-monoˡ-≤-nonNeg` and `ratioLeOne`. $\square$

**Theorem (buyerTickBelowValuation).** $\text{buyerTick}(n,v,b,i) \leq v$.

*Proof.* $\text{buyerTick} \leq v \sqcap b \leq v$ by `tickLeOneCap` and `p⊓q≤p`. $\square$

**Theorem (sellerTickAboveValuation).** If $v \leq M$ then $v \leq \text{sellerTick}(n,v,M,i)$.

*Proof.* $\text{sellerTick} = v + (M-v)\cdot\text{ratio} \geq v + 0 = v$ since $M - v \geq 0$ and $\text{ratio} \geq 0$. $\square$

---

## Module 13: AgentStrategy

### Definitions

A **certified bid** for agent $a$ is a pair $(\pi, \text{adm})$ where $\pi$ is a proposal and $\text{adm} : \text{BuyerAdmissible}(a, \pi)$.

A **certified ask** is defined analogously with $\text{SellerAdmissible}$.

**L3 buyer bid** at grid index $i$:
$$\text{makeBuyerBid}(n, a, i) \;=\; \bigl((a.\text{id},\; (v_a \sqcap b_a) \cdot \text{ratio}(n,i),\; \text{Buyer}),\; \text{proof}\bigr)$$

The proof fields are supplied by `buyerTickBelowValuation` and `buyerTickWithinBudget`.

**L3 seller ask** at grid index $i$:
$$\text{makeSellerAsk}(n, a, M, i) \;=\; \bigl((a.\text{id},\; v_a + (M - v_a) \cdot \text{ratio}(n,i),\; \text{Seller}),\; \text{proof}\bigr)$$

The proof fields are supplied by `sellerTickAboveValuation` (for price ≥ $v_a$) and the inventory hypothesis.

### Key Property

Every call to `makeBuyerBid` or `makeSellerAsk` returns a type-certified admissible proposal. No L3-violating proposal can be constructed via these functions — the constraint is enforced at the *type level*, not by a runtime check.

---

## Module 14: BatchAuction

### Algorithm

**tryMatch** attempts to match one certified bid against one certified ask:
$$\text{tryMatch}((\text{buyer}, \text{cb}),\, (\text{seller}, \text{ca})) \;=\; \begin{cases} \text{Just}(m) & \text{if } \pi_s.p \leq \pi_b.p \\ \text{Nothing} & \text{otherwise} \end{cases}$$

The **yes** branch of the decidable $\leq$ test supplies the crossing proof; the resulting `Match` $m$ carries all L3 admissibility evidence.

Clearing price: $c = \pi_s.p$ (ask-price clearing). Then `priceInRange` holds by $\leq$-refl and the crossing proof.

**matchZip** matches bid list against ask list pairwise:
$$\text{matchZip}(\pi_{b,0}, \ldots) \;(\pi_{s,0}, \ldots) \;=\; \text{catMaybes}[\text{tryMatch}(\pi_{b,i}, \pi_{s,i}) \mid i]$$

### Key Property

Every `Match` in the output of `matchZip` is structurally L3-certified: it carries `BuyerAdmissible` and `SellerAdmissible` proofs. `realizedSurplusNonNeg` therefore applies to any trace built from this output.

---

## Module 15: FlagshipFull

### Definitions

A **simulation environment** is a record:
$$\text{SimEnv} = (a_b, a_s, M, \text{cap} \geq 0, v_s \leq M, \text{inv}_s > 0)$$

The **concrete L3 simulation** for environment $e$ and grid resolution $n$:
$$\text{concreteSim}_e : \text{Seed}(\text{suc}\, n, 2) \to \text{Trace}$$
$$\text{concreteSim}_e(s) = \text{matchesToTrace}(\text{matchZip}([\text{bid}(s)],\, [\text{ask}(s)]))$$
where $\text{bid}(s) = \text{makeBuyerBid}(n, a_b, s[0])$ and $\text{ask}(s) = \text{makeSellerAsk}(n, a_s, M, s[1])$.

### Theorems

**Theorem (Concrete Surplus Non-Negativity).**
$$\forall e, s,\quad 0 \leq \text{realizedSurplus}(\text{concreteSim}_e(s))$$

*Proof.* $\text{concreteSim}_e(s)$ is a `Trace`, so `realizedSurplusNonNeg` applies. $\square$

**Theorem (Concrete Pointwise Flagship).** For any L0 simulation $\text{simL0}$ and any witness seed $s_0$ with $\text{l0Surplus}(\text{simL0}(s_0)) < 0$:
$$\exists\, s_0,\quad \text{l0Surplus}(\text{simL0}(s_0)) < \text{realizedSurplus}(\text{concreteSim}_e(s_0))$$

*Proof.* Apply the abstract `flagshipPointwise` from `SimulationModel` to `concreteSim_e`. $\square$

**Remark.** $\text{concreteSim}_e$ satisfies the `SimFnL3` interface *by construction*: its TYPE is `Seed (suc n) 2 → Trace`. The abstract theorems are parameterized over any `SimFnL3`; applying them to the concrete simulation requires no additional proof — just instantiation.

---

## Road Map

| Step | Item | Status |
|------|------|--------|
| 1 | `Agent` — role, valuation, budget, inventory | ✓ |
| 2 | `Proposal` — raw proposals, L0/L3 constraints | ✓ |
| 3 | `Seed` — finite oracle tape over `Fin n` | ✓ |
| 4 | `Institution` — batch auction, matching logic, Valuation Chain | ✓ |
| 5 | `Surplus` — surplus definition, non-negativity theorem | ✓ |
| 6 | `Trace` — event vocabulary, certified traces, realized surplus | ✓ |
| 7 | Theorem: $\text{RealizedSurplus}(\text{L3 trace}) \geq 0$ | ✓ |
| 8 | `Efficiency` — max feasible surplus, efficiency ratio, L3 eff ≥ 0 | ✓ |
| 9 | `Flagship` — L0 witness + dominance theorem | ✓ |
| 10 | `Probability` — sumQ, non-negativity, strict monotonicity | ✓ |
| 11 | `SimulationModel` — Theorems 6 & 7: pointwise and expected flagship | ✓ |
| 12 | `PriceGrid` — uniform tick grids, `ratioLeOne` proved | ✓ |
| 13 | `AgentStrategy` — certified L3 proposals from seed indices | ✓ |
| 14 | `BatchAuction` — `tryMatch` with decidable crossing, `matchZip` | ✓ |
| 15 | `FlagshipFull` — concrete `SimFnL3`, pointwise flagship instantiated | ✓ |
| 16 | `L0AgentStrategy` — concrete `SimFnL0`, negative-surplus witness, `l0Nonpos-inverted` | ✓ |
| 17 | `Stochastic` — `survivalCount`, `FSDom`, `l3FSDom-l0-inverted` | ✓ |

---

## Module 16: L0AgentStrategy

### Definitions

**L0 Tick Function**

The unconstrained price function maps a seed index to a full-range price:
$$\text{l0Tick}(n, p_{\max}, i) \;=\; p_{\max} \cdot \frac{\text{toℕ}(i)}{\text{suc}(n)}, \qquad i : \text{Fin}(\text{suc}(n))$$

No capping or flooring — the entire range $[0, p_{\max})$ is available to any agent, regardless of valuation.

Compare with the constrained L3 variants:
$$\text{buyerTick}(n,v,b,i) = (v \wedge b) \cdot \frac{i}{n+1} \leq \min(v,b) \quad \text{(bid capped at valuation \& budget)}$$
$$\text{sellerTick}(n,v,p_{\max},i) = v + (p_{\max}-v) \cdot \frac{i}{n+1} \geq v \quad \text{(ask floored at cost)}$$
$$\text{l0Tick}(n,p_{\max},i) = p_{\max} \cdot \frac{i}{n+1} \qquad\qquad\quad \text{(no constraint)}$$

**L0 Raw Match**

For agent $B$ (buyer) with bid price $b_p$ and agent $S$ (seller) with ask price $a_p$:
$$\text{tryL0Match}(B, b_p, S, a_p) = \begin{cases} \text{Just}(m) & \text{if } a_p \leq b_p \\ \text{Nothing} & \text{otherwise} \end{cases}$$

where $m$ is a `RawMatch` with no admissibility evidence.

**Concrete L0 Simulation**

Given a `SimEnvironment` $e = (B, S, p_{\max}, \ldots)$ and a 2-draw seed $s$:
$$\text{concreteL0Sim}_e(s) = \text{tryL0Match}(B,\; \text{l0Tick}(n, p_{\max}, s_0),\; S,\; \text{l0Tick}(n, p_{\max}, s_1))$$

where $s_0 = \text{drawAt}(s, 0)$ and $s_1 = \text{drawAt}(s, 1)$.

### Witness Construction

**Witness Environment**

$$e^* = \bigl(\underbrace{B^*}_{\text{val}=1,\,\text{bdg}=3},\; \underbrace{S^*}_{\text{val}=2,\,\text{inv}=1},\; p_{\max} = 3 \bigr)$$

using `buyerWitness` and `sellerWitness` from `Flagship.agda`.

The critical fact: $v_{B^*} = 1 < 2 = v_{S^*}$, so
$$\text{rawSurplus}(m) = v_{B^*} - v_{S^*} = 1 - 2 = -1 < 0$$
for **any** match $m$ involving these agents, regardless of prices.

**Witness Seed**

For grid resolution $n=1$ (2-tick grid, $\text{Seed}(2,2)$):
$$s^* = [\,\underbrace{1}_{\text{buyer draws HIGH}},\; \underbrace{0}_{\text{seller draws LOW}}\,]$$

Evaluation:
$$\text{bidP} = \text{l0Tick}(1, 3, 1) = 3 \cdot \tfrac{1}{2} = \tfrac{3}{2}$$
$$\text{askP} = \text{l0Tick}(1, 3, 0) = 3 \cdot \tfrac{0}{2} = 0$$
$$\text{askP} \leq \text{bidP}?  \quad 0 \leq \tfrac{3}{2} \;\checkmark \quad \Rightarrow \text{ match produced}$$

### Theorems

**Theorem (L0 Negative Surplus).** At the witness environment and seed:
$$\text{l0RealizedSurplus}\bigl(\text{concreteL0Sim}_{e^*}(s^*)\bigr) = -1 < 0$$

*Proof.* The chain evaluates concretely: the seed produces $\text{bidP} = 3/2$, $\text{askP} = 0$; they cross; `rawSurplus` $= 1 - 2 = -1$; `sumQ`$[-1] = -1$. Verified at compile time by `toWitness`. $\square$

**Theorem (Flagship Witness).** There exists a seed with negative L0 surplus:
$$\exists\, s_0 : \text{Seed}(2,2),\quad \text{l0RealizedSurplus}\bigl(\text{concreteL0Sim}_{e^*}(s_0)\bigr) < 0$$

*Proof.* Take $s_0 = s^*$ and apply the theorem above. $\square$

**Corollary (Concrete Pointwise Flagship, fully instantiated).**
$$\exists\, s_0 : \text{Seed}(2,2),\quad \text{l0RealizedSurplus}\bigl(\text{concreteL0Sim}_{e^*}(s_0)\bigr) \;<\; \text{realizedSurplus}\bigl(\text{concreteSim}_{e^*}(s_0)\bigr)$$

*Proof.* Apply `concretePointwiseFlagship` from `FlagshipFull.agda` with `simL0 = concreteL0Sim witnessEnv` and the witness `witnessForFlagship`. $\square$

**Remark.** At $s^* = [1, 0]$, the L3 simulation produces **no trade** (because $v_B = 1 < 2 = v_S$ violates the valuationChain precondition — the L3 institution rejects this pairing), so $\text{realizedSurplus} = 0$. The L0 simulation produces a trade with surplus $-1$. The comparison is $-1 < 0$: L3 strictly dominates L0 at this seed.

---

---

## Module 17: Stochastic

### Motivation

Theorem 6 (Pointwise Flagship) is existential: it finds *one* seed where L3 beats L0. Theorem 7 (Expected Flagship) requires pointwise dominance ($\forall s$, L0 $\leq$ L3), which the simulation shows is FALSE in productive markets ($v_b > v_s$). We need a statement that:

1. Is provable (does not require the false hypothesis 4)
2. Is a genuine distributional comparison (stronger than a single witness)

**Solution:** First-Order Stochastic Dominance (FSD), restricted to inverted environments ($v_b \leq v_s$).

### Definitions

**Survival Count**

For a function $f : S \to \mathbb{Q}$, a finite population $\Omega : \text{List}(S)$, and a threshold $t \in \mathbb{Q}$:
$$\text{survivalCount}(f, \Omega, t) \;=\; |\{s \in \Omega \mid f(s) \geq t\}|$$

This is the empirical upper CDF of $f$ over $\Omega$, scaled by $|\Omega|$. In Agda:
$$\text{survivalCount}(f, \Omega, t) = \text{length}(\text{filterᵇ}(\lambda s \mapsto \text{isYes}(t \leq ? f(s)),\; \Omega))$$

*Remark.* We use `isYes` (pattern-matching function) rather than `does` (record field). After Agda's `with`-abstraction, field projections do not reduce; pattern-matching constructors do. Specifically, `isYes (no _) = false` reduces by $\beta$-reduction; `does (no _)` does not, because `does` is a field selector rather than a case-split.

**First-Order Stochastic Dominance**

$f$ FSD-dominates $g$ over $\Omega$ iff for every threshold $t$:
$$\text{FSDom}(f, g, \Omega) \;\equiv\; \forall t,\quad \text{survivalCount}(g, \Omega, t) \;\leq_\mathbb{N}\; \text{survivalCount}(f, \Omega, t)$$

**Economic interpretation.** Any agent with a monotone utility function (more surplus is better) weakly prefers the $f$-lottery to the $g$-lottery.

### Key Lemmas

**filter-mono.** For Bool-valued predicates $p, q : A \to \text{Bool}$:
$$\bigl(\forall x,\; q(x) = \text{true} \implies p(x) = \text{true}\bigr) \;\implies\; |\text{filter}(q, xs)| \leq_\mathbb{N} |\text{filter}(p, xs)|$$

*Proof* by structural induction on $xs$, splitting on $p(x)$ first (so that `filter p (x ∷ xs)` reduces in the goal):

| $p(x)$ | $q(x)$ | Action |
|--------|--------|--------|
| false | false | Both skip $x$; reduce to IH |
| false | true | Contradicts the implication premise; $\bot$-elim |
| true | false | $p$ grows by 1, $q$ stays; IH $+ m \leq n \Rightarrow m \leq n+1$ |
| true | true | Both include $x$; $s \leq s$ (s≤s IH) |

### Theorems

**Theorem (l0Nonpos-inverted).** For any environment with $v_b \leq v_s$ and any seed $s$:
$$\text{l0RealizedSurplus}(\text{concreteL0Sim}(s)) \leq 0$$

*Proof.* Case split on $\text{askP} \leq? \text{bidP}$ — the same discriminant used inside `tryL0Match`. This forces `tryL0Match` to reduce in the goal.

- *No match* ($\text{ask} > \text{bid}$): $\text{l0RealizedSurplus}([]) = 0 \leq 0$. $\square$
- *Match* ($\text{ask} \leq \text{bid}$): the constructed `RawMatch` has `buyer = env.buyer`, `seller = env.seller` by definitional reduction. So $\text{rawSurplus}(m) = v_b - v_s$.
  $$\text{l0RealizedSurplus}([m]) = (v_b - v_s) + 0 \leq v_b - v_s \leq 0$$
  where the first step uses $\text{+-identityʳ}$ and the second uses $v_b \leq v_s$ and the companion lemma $p \leq q \Rightarrow p - q \leq 0$. $\square$

*Remark (definitional opacity).* `l0Nonpos-inverted` is proved inside `L0AgentStrategy.agda` rather than `Stochastic.agda`, because the private helper `fromMaybe` (used in `runL0Matches`) is only transparent from within its defining module. From outside, Agda will not reduce `fromMaybe (just m)` to `m ∷ []`, blocking the goal reduction. This is a practical constraint of Agda's module system: private definitions are name-scoped, not type-checker opaque, but inter-module `with`-abstractions can fail to trigger reductions they expect.

**Companion Lemma ($p \leq q \Rightarrow p - q \leq 0$).**
$$h : p \leq q \;\implies\; p - q \leq 0$$

*Proof.* Mirror of `p≤q⇒0≤q-p` from `Surplus.agda`:
$$\underbrace{p + (-q) \leq q + (-q)}_{\text{+-monoˡ-≤ } (-q)\; h} \quad \underset{\text{subst with +-inverseʳ } q}{\Longrightarrow} \quad p - q \leq 0 \quad \square$$

**Theorem (FSD-from-pointwise).** If $\forall s \in \Omega,\ g(s) \leq f(s)$, then $\text{FSDom}(f, g, \Omega)$.

*Proof.* Fix $t$. By `filter-mono`, it suffices to show:
$$\forall s,\quad \text{isYes}(t \leq ? g(s)) = \text{true} \;\implies\; \text{isYes}(t \leq ? f(s)) = \text{true}$$

Case split on $t \leq ? g(s)$:
- $\text{no}$: hypothesis is `isYes (no _) ≡ true = false ≡ true`; discharged by `bool-false≡true`.
- $\text{yes}\ (t_{\leq g})$: case split on $t \leq ? f(s)$:
  - $\text{yes}$: return `refl`.
  - $\text{no}\ (\neg t_{\leq f})$: $\neg t_{\leq f}(t_{\leq g} \cdot (g(s) \leq f(s))) : \bot$; `⊥-elim`. $\square$

**Theorem (l3FSDom-l0-inverted — Main Result).** For any environment with $v_b \leq v_s$ and any seed population $\Omega$:
$$\text{FSDom}\bigl(\text{realizedSurplus} \circ \text{concreteSim},\; \text{l0RealizedSurplus} \circ \text{concreteL0Sim},\; \Omega\bigr)$$

*Proof.* By `FSD-from-pointwise` it suffices to show pointwise dominance:
$$\forall s,\quad \text{l0RealizedSurplus}(\text{concreteL0Sim}(s)) \leq \text{realizedSurplus}(\text{concreteSim}(s))$$

Chain via transitivity:
$$\underbrace{\text{l0Surplus}(s) \leq 0}_{\text{l0Nonpos-inverted}} \;\leq\; \underbrace{0 \leq \text{l3Surplus}(s)}_{\text{realizedSurplusNonNeg}} \quad \square$$

### What FSD Gives Us

The pointwise flagship (Theorem 6) says: there *exists* a seed where L3 beats L0.

FSD says: for *every* threshold $t$, L3 has at least as much probability mass above $t$ as L0. In particular:
- $t = 0$: $\mathbb{P}(\text{L3} \geq 0) \geq \mathbb{P}(\text{L0} \geq 0)$ — L3 is at least as likely to be non-negative.
- $t \to -\infty$: trivially both are 1.
- Taking the integral (sum over all $t$): $\mathbb{E}[\text{L3}] \geq \mathbb{E}[\text{L0}]$.

This is a complete distributional comparison, not just a worst-case or best-case comparison. Any monotone criterion prefers L3 to L0 in inverted markets.

### Scope and Limitations

The theorem applies to **inverted environments** ($v_b \leq v_s$). The simulation (Module 16 / `Main.agda`) shows that in **productive environments** ($v_b > v_s$), the inequality reverses: L0 FSD-dominates L3 because L3's conservative bidding suppresses many value-creating trades. A full characterization of when L3 dominates L0 would require analysis over the joint distribution of $v_b$ and $v_s$, which is left for future work.

---

## Key Inequality Chain (Flagship Theorem Preview)

For any trade cleared in a batch auction under L3, the clearing price $c$ satisfies:

$$v_{\text{seller}} \;\leq\; \text{ask} \;\leq\; c \;\leq\; \text{bid} \;\leq\; v_{\text{buyer}}$$

The first inequality is the seller's L3 constraint; the last is the buyer's.
The middle inequalities follow from the auction's matching condition (bid $\geq$ ask) and uniform clearing price.

Therefore every L3 trade generates **non-negative gains from trade**:

$$v_{\text{buyer}} - v_{\text{seller}} \;\geq\; 0$$

Under L0, no such chain holds. A buyer may bid above valuation or a seller ask below cost, making negative-surplus trades possible.

This structural asymmetry between L0 and L3 is the analytic engine of the flagship theorem.
