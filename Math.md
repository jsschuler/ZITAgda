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
| 17 | `Stochastic` — `survivalCount`, `FSDom`, `l3FSDom-l0-inverted`, `l3Expected-l0-inverted`, `l0FSDom-l3-productive` | ✓ |
| 18 | `MultiAgentSim` — k-pair extension; `realizedSurplus-++`; `AllInverted`/`AllProductive`; `l3FSDom-l0-invertedN`; `l0FSDom-l3-productiveN`; `l3ExpectedN-l0-inverted`; `l0ExpectedN-l3-productive` | ✓ |
| 19 | `EfficiencyFSD` — efficiency ratio FSD; `l0EfficiencyRatio`; `l3EffFSDom-l0-inverted`; `l0EffFSDom-l3-productive`; expected-efficiency corollaries | ✓ |
| 20 | `MultiAgentEffFSD` — k-pair efficiency FSD; `concreteL3EffN`; `concreteL0EffN`; `l3EffFSDom-l0-invertedN`; `l0EffFSDom-l3-productiveN`; expected corollaries | ✓ |
| 21 | `MixedWelfare` — oracle-mix welfare; `Mixed` predicate; `concreteMixSurplusN`; `mixFSDom-l3`; `mixFSDom-l0`; expected corollaries | ✓ |
| 22 | `MixedEffFSD` — oracle-mix efficiency FSD; `concreteMixEffN`; `mixEffFSDom-l3`; `mixEffFSDom-l0`; expected corollaries | ✓ |

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

**Theorem (l3Expected-l0-inverted — Expected Value Corollary).** For any environment with $v_b \leq v_s$ and any seed population $\Omega$:
$$\sum_{s \in \Omega} \text{l0RealizedSurplus}(\text{concreteL0Sim}(s)) \;\leq\; \sum_{s \in \Omega} \text{realizedSurplus}(\text{concreteSim}(s))$$

Since both sums share the denominator $|\Omega|$, this is equivalent to $\mathbb{E}_\Omega[\text{L0 surplus}] \leq \mathbb{E}_\Omega[\text{L3 surplus}]$.

*Proof.* By `sumQ-map-mono`: if $g(s) \leq f(s)$ pointwise, then $\text{sumQ}(\text{map}\ g\ \Omega) \leq \text{sumQ}(\text{map}\ f\ \Omega)$. Apply to the same pointwise bound used in the FSD proof:
$$\underbrace{\text{l0Surplus}(s) \leq 0}_{\text{l0Nonpos-inverted}} \leq \underbrace{0 \leq \text{l3Surplus}(s)}_{\text{realizedSurplusNonNeg}} \quad \square$$

*Remark.* Both `l3FSDom-l0-inverted` (FSD) and `l3Expected-l0-inverted` (expected value) derive from the same pointwise bound — they are two consequences of a single structural fact. FSD is the strictly stronger result: $\mathbb{E}[f] \geq \mathbb{E}[g]$ follows from $\text{FSDom}(f, g, \Omega)$, but not conversely. Here both are proved directly from pointwise dominance rather than chaining through FSD.

**Key lemma (sumQ-map-mono).** If $\forall s,\ g(s) \leq f(s)$ then:
$$\text{sumQ}(\text{map}\ g\ xs) \leq \text{sumQ}(\text{map}\ f\ xs)$$

*Proof* by induction on $xs$: base case $\leq$-refl; step case `+-mono-≤ (pw x) IH`. $\square$

### What FSD Gives Us

The pointwise flagship (Theorem 6) says: there *exists* a seed where L3 beats L0.

FSD says: for *every* threshold $t$, L3 has at least as much probability mass above $t$ as L0. In particular:
- $t = 0$: $\mathbb{P}(\text{L3} \geq 0) \geq \mathbb{P}(\text{L0} \geq 0)$ — L3 is at least as likely to be non-negative.
- $t \to -\infty$: trivially both are 1.
- Taking the integral (sum over all $t$): $\mathbb{E}[\text{L3}] \geq \mathbb{E}[\text{L0}]$ — which is exactly `l3Expected-l0-inverted`.

This is a complete distributional comparison, not just a worst-case or best-case comparison. Any monotone criterion prefers L3 to L0 in inverted markets.

### Symmetric Results for Productive Markets

The inverted-market results have complete counterparts. In a **productive environment** ($v_s \leq v_b$), L3's conservative bidding suppresses value-creating trades, so L0 dominates. The theorems below establish this symmetrically.

**Theorem (l0Nonneg-productive).** For any environment with $v_s \leq v_b$ and any seed $s$:
$$0 \leq \text{l0RealizedSurplus}(\text{concreteL0Sim}(s))$$

*Proof.* Case split on $\text{askP} \leq? \text{bidP}$:
- *No match:* $\text{l0RealizedSurplus}([]) = 0$. $\square$
- *Match:* The raw surplus is $v_b - v_s \geq 0$ by hypothesis $v_s \leq v_b$. Apply `p≤q⇒0≤q-p`. $\square$

*Remark.* This is the symmetric counterpart of `l0Nonpos-inverted`: same proof structure, opposite hypothesis.

---

#### Arithmetic Lemmas for the Price-Range Comparison

The key fact needed for productive markets is the **price chain**:
$$\text{L0\_ask} \leq \text{L3\_ask} \leq \text{L3\_bid} \leq \text{L0\_bid}$$

This means: if L3 agents cross (L3 ask $\leq$ L3 bid), then L0 agents also cross (L0 ask $\leq$ L0 bid). The left and right inequalities require separate lemmas.

**Lemma (sum-cancel).** For any $v_s, p_{\max} \in \mathbb{Q}$:
$$v_s + (p_{\max} - v_s) = p_{\max}$$

*Proof.* By ring laws: $v_s + (p_{\max} - v_s) = v_s + p_{\max} - v_s = p_{\max} + (v_s - v_s) = p_{\max} + 0 = p_{\max}$.

In Agda: `+-assoc`, `+-comm`, `+-inverseʳ`, `+-identityʳ`. $\square$

*Remark.* This identity is non-trivial in Agda because the rational number type stores gcd-reduced fractions; `p_{\max} - v_s + v_s` does not reduce to `p_{\max}` by $\beta$-reduction alone. The ring axioms must be invoked explicitly.

**Lemma (l0AskLE-l3Ask).** For $0 \leq v_s$ and $r \leq 1$:
$$p_{\max} \cdot r \;\leq\; v_s + (p_{\max} - v_s) \cdot r$$

*Proof.*
$$p_{\max} \cdot r \;=\; (v_s + (p_{\max} - v_s)) \cdot r \quad \text{(sum-cancel)}$$
$$= v_s \cdot r + (p_{\max} - v_s) \cdot r \quad \text{(*-distribʳ-+)}$$
$$\leq v_s + (p_{\max} - v_s) \cdot r \quad \text{since } v_s \cdot r \leq v_s \cdot 1 = v_s \text{ (as } r \leq 1, v_s \geq 0 \text{)}$$

The last step uses `*-monoˡ-≤-nonNeg` with the `NonNegative vS` instance derived from $0 \leq v_s$. $\square$

**Lemma (l3BidLE-l0Bid).** For $0 \leq r$ and $\text{cap} \leq p_{\max}$:
$$\text{cap} \cdot r \;\leq\; p_{\max} \cdot r$$

*Proof.* Direct application of `*-monoʳ-≤-nonNeg` with `NonNegative r` instance. $\square$

---

**Theorem (l3LE-l0-productive — Pointwise Comparison).** For any environment with $0 \leq v_s$, $v_s \leq v_b$, and $\text{cap} \leq p_{\max}$ (where $\text{cap} = v_b \sqcap b_b$), and any seed $s$:
$$\text{realizedSurplus}(\text{concreteSim}(s)) \;\leq\; \text{l0RealizedSurplus}(\text{concreteL0Sim}(s))$$

*Proof.* Let $r_0 = \text{ratio}(n, s_0)$ (buyer draw), $r_1 = \text{ratio}(n, s_1)$ (seller draw). Define:
$$\text{L3\_bid} = \text{cap} \cdot r_0, \quad \text{L3\_ask} = v_s + (p_{\max} - v_s) \cdot r_1$$
$$\text{L0\_bid} = p_{\max} \cdot r_0, \quad \text{L0\_ask} = p_{\max} \cdot r_1$$

The price chain holds:
$$\underbrace{\text{L0\_ask} \leq \text{L3\_ask}}_{\text{l0AskLE-l3Ask with } 0 \leq v_s,\; r_1 \leq 1} \qquad \underbrace{\text{L3\_bid} \leq \text{L0\_bid}}_{\text{l3BidLE-l0Bid with } 0 \leq r_0,\; \text{cap} \leq p_{\max}}$$

Case split on $\text{L3\_ask} \leq? \text{L3\_bid}$ (the L3 auction discriminant), then on $\text{L0\_ask} \leq? \text{L0\_bid}$:

| L3 trades? | L0 trades? | Argument |
|-----------|-----------|----------|
| No | Either | $\text{L3 surplus} = 0 \leq \text{L0 surplus}$, by `l0Nonneg-productive`. |
| Yes | No | Impossible: L3\_ask $\leq$ L3\_bid $\leq$ L0\_bid and L0\_ask $\leq$ L3\_ask, so L0\_ask $\leq$ L0\_bid — contradicts "No". `⊥-elim`. |
| Yes | Yes | Both surpluses $= v_b - v_s$; `≤-refl`. |

$\square$

*Proof placement remark.* `l3LE-l0-productive` is proved inside `L0AgentStrategy.agda` so that the private `fromMaybe` helper (used in `runL0Matches`) is transparent. The L3 `collectMatches` (private in `BatchAuction.agda`) is also transparent from there because Agda's privacy is name-scoped — case-splitting on `L3_ask ≤? L3_bid` (the exact `with` scrutinee used by `tryMatch`) forces `collectMatches` to reduce definitionally.

---

**Theorem (l0FSDom-l3-productive — Symmetric FSD).** For any environment with $0 \leq v_s$, $v_s \leq v_b$, and $\text{cap} \leq p_{\max}$, and any seed population $\Omega$:
$$\text{FSDom}\bigl(\text{l0RealizedSurplus} \circ \text{concreteL0Sim},\; \text{realizedSurplus} \circ \text{concreteSim},\; \Omega\bigr)$$

i.e., L0 first-order stochastically dominates L3 in productive markets.

*Proof.* By `FSD-from-pointwise` applied to `l3LE-l0-productive`. $\square$

*Economic interpretation.* L3's constraints force bids $\leq v_b$ and asks $\geq v_s$, a strictly tighter range than L0's full $[0, p_{\max})$. Every seed where L3 trades, L0 also trades (for the same surplus $v_b - v_s$). But there are seeds where L0 trades and L3 does not — the conservative constraint prevents many value-creating crossings. Therefore L0's surplus distribution first-order dominates L3's.

---

### Symmetry Summary

Together the two FSD results characterize the crossover completely:

| Environment | Condition | Dominance |
|-------------|-----------|-----------|
| Inverted market | $v_b \leq v_s$ | L3 FSD-dominates L0 (`l3FSDom-l0-inverted`) |
| Productive market | $v_s \leq v_b$ | L0 FSD-dominates L3 (`l0FSDom-l3-productive`) |

The driving mechanism is the same in both cases: the price chain L0\_ask $\leq$ L3\_ask $\leq$ L3\_bid $\leq$ L0\_bid. In inverted markets, neither simulation should trade (surplus would be negative); L3's tighter constraints prevent more harmful trades. In productive markets, both should trade; L3's tighter constraints prevent more beneficial trades.

---

## Module 18: MultiAgentSim

### Motivation

The single-pair theorems in Module 17 prove FSD for one buyer and one seller. Real markets have many traders. This module extends both FSD results to $k$ buyer-seller pairs without changing any existing module.

**Design principle:** every theorem here is an application of an existing lemma. The new proof content is limited to two structural lemmas about lists and one Vec induction per FSD direction.

### Definitions

**Multi-seed**

$$\text{MultiSeed}(n, k) \;=\; \text{Vec}\bigl(\text{Seed}(\text{suc}\,n, 2),\; k\bigr)$$

$k$ independent 2-draw seeds, one per buyer-seller pair. The pairs are fully decoupled.

**Multi-agent trace**

$$\text{concreteSimN}(\text{envs}, \mathbf{s}) \;=\; \text{concreteSim}(e_1, s_1) \,\mathbin{++}\, \cdots \,\mathbin{++}\, \text{concreteSim}(e_k, s_k)$$

The output is a `Trace` (a `List Event`). `realizedSurplusNonNeg` applies immediately — non-negativity of the multi-agent L3 trace is a one-liner.

**Multi-agent surplus sums** (by Vec recursion)

$$\text{realizedSurplusN}(\text{envs}, \mathbf{s}) \;=\; \sum_{i=1}^{k} \text{realizedSurplus}(\text{concreteSim}(e_i, s_i))$$

$$\text{l0RealizedSurplusN}(\text{envs}, \mathbf{s}) \;=\; \sum_{i=1}^{k} \text{l0RealizedSurplus}(\text{concreteL0Sim}(e_i, s_i))$$

**Environment conditions**

$$\text{AllInverted}(\text{envs}) \;\equiv\; \forall i,\; v_{b,i} \leq v_{s,i}$$

$$\text{AllProductive}(\text{envs}) \;\equiv\; \forall i,\; 0 \leq v_{s,i} \;\wedge\; v_{s,i} \leq v_{b,i} \;\wedge\; \text{cap}_i \leq p_{\max,i}$$

Both are inductive predicates on `Vec SimEnvironment k`, proved by providing one condition per position.

### Structural Lemmas

**Lemma (tradesView-++)** (private):
$$\text{tradesView}(t_1 \mathbin{++} t_2) \;=\; \text{tradesView}(t_1) \mathbin{++} \text{tradesView}(t_2)$$

*Proof* by structural induction on $t_1$, case-splitting on each of the five `Event` constructors. The `TradeSettled` case contributes an element; all other four constructors are transparent (their events are ignored by `tradesView`). $\square$

**Lemma (sumSurplus-++)** (private):
$$\text{sumSurplus}(ms_1 \mathbin{++} ms_2) \;=\; \text{sumSurplus}(ms_1) + \text{sumSurplus}(ms_2)$$

*Proof* by induction on $ms_1$:
- Base: $\text{sumSurplus}([]) + \text{sumSurplus}(ms_2) = 0 + \text{sumSurplus}(ms_2) = \text{sumSurplus}(ms_2)$ by `+-identityˡ`. $\square$
- Step: chain via `cong` (IH) then `sym +-assoc`. $\square$

**Lemma (realizedSurplus-++)**:
$$\text{realizedSurplus}(t_1 \mathbin{++} t_2) \;=\; \text{realizedSurplus}(t_1) + \text{realizedSurplus}(t_2)$$

*Proof*: chain `tradesView-++` and `sumSurplus-++` via `cong`. $\square$

**Lemma (realizedSurplusN-eq)**:
$$\text{realizedSurplus}(\text{concreteSimN}(\text{envs}, \mathbf{s})) \;=\; \text{realizedSurplusN}(\text{envs}, \mathbf{s})$$

*Proof* by induction on $k$:
- Base ($k=0$): both sides are $0$. $\square$
- Step: $\text{realizedSurplus}(\text{concreteSim}(e, s) \mathbin{++} \text{concreteSimN}(\text{envs}, \mathbf{s}'))$
  $= \text{realizedSurplus}(\text{concreteSim}(e, s)) + \text{realizedSurplus}(\text{concreteSimN}(\text{envs}, \mathbf{s}'))$ by `realizedSurplus-++`
  $= \text{realizedSurplus}(\text{concreteSim}(e, s)) + \text{realizedSurplusN}(\text{envs}, \mathbf{s}')$ by IH. $\square$

### Theorems

**Theorem (concreteSimNNonNeg).**
$$\forall\, \text{envs},\, \mathbf{s},\quad 0 \leq \text{realizedSurplus}(\text{concreteSimN}(\text{envs}, \mathbf{s}))$$

*Proof*: `realizedSurplusNonNeg (concreteSimN envs seeds)`. $\square$

*Remark.* This one-line proof reflects the extension principle: `concreteSimN` produces a `Trace`, and `realizedSurplusNonNeg` applies to ALL traces. No per-pair reasoning is needed.

---

**Lemma (l0LEL3-invertedN — Pointwise Bound)** (private):
If $\text{AllInverted}(\text{envs})$, then for every multi-seed $\mathbf{s}$:
$$\text{l0RealizedSurplusN}(\text{envs}, \mathbf{s}) \;\leq\; \text{realizedSurplusN}(\text{envs}, \mathbf{s})$$

*Proof* by induction on $k$:
- Base: $0 \leq 0$. $\square$
- Step:
$$\underbrace{\text{l0Surplus}(s) \leq 0}_{\text{l0Nonpos-inverted}} \leq \underbrace{0 \leq \text{l3Surplus}(s)}_{\text{realizedSurplusNonNeg}}$$
Apply `+-mono-≤` to combine the head bound with the IH on the tail. $\square$

**Theorem (l3FSDom-l0-invertedN — Multi-Agent FSD, Inverted).** If $\text{AllInverted}(\text{envs})$, then for any seed population $\Omega$:
$$\text{FSDom}\bigl(\text{realizedSurplusN}(\text{envs}),\; \text{l0RealizedSurplusN}(\text{envs}),\; \Omega\bigr)$$

*Proof*: `FSD-from-pointwise` applied to `l0LEL3-invertedN`. $\square$

---

**Lemma (l3LEL0-productiveN — Pointwise Bound)** (private):
If $\text{AllProductive}(\text{envs})$, then for every multi-seed $\mathbf{s}$:
$$\text{realizedSurplusN}(\text{envs}, \mathbf{s}) \;\leq\; \text{l0RealizedSurplusN}(\text{envs}, \mathbf{s})$$

*Proof* by induction on $k$:
- Base: $0 \leq 0$. $\square$
- Step: apply `l3LE-l0-productive` to the head pair, then `+-mono-≤` with the IH. $\square$

**Theorem (l0FSDom-l3-productiveN — Multi-Agent FSD, Productive).** If $\text{AllProductive}(\text{envs})$, then for any $\Omega$:
$$\text{FSDom}\bigl(\text{l0RealizedSurplusN}(\text{envs}),\; \text{realizedSurplusN}(\text{envs}),\; \Omega\bigr)$$

*Proof*: `FSD-from-pointwise` applied to `l3LEL0-productiveN`. $\square$

---

**Corollary (l3FSDom-l0-invertedN-trace).** The FSD result can equivalently be stated in terms of the `Trace` output of `concreteSimN`:
$$\text{FSDom}\bigl(\text{realizedSurplus} \circ \text{concreteSimN}(\text{envs}),\; \text{l0RealizedSurplusN}(\text{envs}),\; \Omega\bigr)$$

*Proof*: combine `l0LEL3-invertedN` with `≤-reflexive (sym (realizedSurplusN-eq ...))` to get the pointwise bound against `realizedSurplus ∘ concreteSimN`, then apply `FSD-from-pointwise`. $\square$

---

**Key lemma (sumQ-map-mono)** (private, reproved locally from Stochastic):
If $\forall s,\ g(s) \leq f(s)$ then $\text{sumQ}(\text{map}\ g\ \Omega) \leq \text{sumQ}(\text{map}\ f\ \Omega)$.

*Proof* by induction: base `≤-refl`; step `+-mono-≤ (pw x) IH`. $\square$

**Theorem (l3ExpectedN-l0-inverted).** If $\text{AllInverted}(\text{envs})$, then for any $\Omega$:
$$\sum_{\mathbf{s} \in \Omega} \text{l0RealizedSurplusN}(\text{envs}, \mathbf{s}) \;\leq\; \sum_{\mathbf{s} \in \Omega} \text{realizedSurplusN}(\text{envs}, \mathbf{s})$$

*Proof*: `sumQ-map-mono` applied to `l0LEL3-invertedN`. $\square$

**Theorem (l0ExpectedN-l3-productive).** If $\text{AllProductive}(\text{envs})$, then for any $\Omega$:
$$\sum_{\mathbf{s} \in \Omega} \text{realizedSurplusN}(\text{envs}, \mathbf{s}) \;\leq\; \sum_{\mathbf{s} \in \Omega} \text{l0RealizedSurplusN}(\text{envs}, \mathbf{s})$$

*Proof*: `sumQ-map-mono` applied to `l3LEL0-productiveN`. $\square$

*Remark.* Both expected-value theorems derive from the same pointwise bounds as the FSD theorems. FSD is strictly stronger (it implies the expected-value comparison but not conversely); both are proved directly from pointwise dominance rather than chaining through FSD, mirroring the structure of Module 17.

### Extension Summary

| Theorem | Module | Single-pair ingredient |
|---------|--------|----------------------|
| `l3FSDom-l0-invertedN` | 18 | `l0Nonpos-inverted` (mod 16) + `realizedSurplusNonNeg` (mod 6) |
| `l0FSDom-l3-productiveN` | 18 | `l3LE-l0-productive` (mod 16) |
| `l3ExpectedN-l0-inverted` | 18 | same pointwise bound as `l3FSDom-l0-invertedN` |
| `l0ExpectedN-l3-productive` | 18 | same pointwise bound as `l0FSDom-l3-productiveN` |
| FSD theorems use | | `FSD-from-pointwise` (mod 17) |
| Expected theorems use | | `sumQ-map-mono` (reproved locally) |

The $k=1$ case of each multi-agent theorem recovers the corresponding single-pair result from Module 17 exactly.

---

## Module 19: EfficiencyFSD

### Motivation

Modules 17–18 prove FSD on *raw realized surplus*. Gode & Sunder (1993) report their headline result in terms of the **efficiency ratio** — the fraction of the maximum feasible surplus actually realised. This module lifts both FSD directions to the efficiency metric, proving that the distributional dominance carries through the normalisation step.

### Definitions

**Profitable pair and max feasible surplus** (from Module 7)

$$\text{ProfitablePair} = \{(v_b, v_s) \mid v_b \geq v_s\}$$
$$\text{maxFeasibleSurplus}(\mathit{ps}) = \sum_{(v_b,v_s)\in\mathit{ps}} (v_b - v_s)$$

**L3 efficiency ratio**

$$\text{efficiencyRatio}(t, \mathit{ps}, h) = \frac{\text{realizedSurplus}(t)}{\text{maxFeasibleSurplus}(\mathit{ps})}$$

where $h : 0 < \text{mfs}$. (Defined in Module 7; $h$ provides the `NonZero` instance for division.)

**L0 efficiency ratio**

$$\text{l0EfficiencyRatio}(\mathit{ms}, \mathit{ps}, h) = \frac{\text{l0RealizedSurplus}(\mathit{ms})}{\text{mfs}}$$

An L0 analogue that takes raw match list `ms : List RawMatch` rather than a certified `Trace`.

**Concrete efficiency functions**

$$\text{concreteL3Eff}_{n}(\mathit{env}, \mathit{ps}, h)(s) = \text{efficiencyRatio}\bigl(\text{concreteSim}_{n}(\mathit{env}, s),\; \mathit{ps},\; h\bigr)$$
$$\text{concreteL0Eff}_{n}(\mathit{env}, \mathit{ps}, h)(s) = \text{l0EfficiencyRatio}\bigl(\text{concreteL0Sim}_{n}(\mathit{env}, s),\; \mathit{ps},\; h\bigr)$$

Both are functions `Seed (suc n) 2 → ℚ`, the type required by `FSDom`.

### Key Technical Lemma

**Monotonicity of multiplication by $1/\mathit{mfs}$.**

Since $0 < \mathit{mfs}$, we have $\text{Positive}(\mathit{mfs})$, hence $\text{Positive}(1/\mathit{mfs})$ (by `1/pos⇒pos`), hence $\text{NonNeg}(1/\mathit{mfs})$ (by `pos⇒nonNeg`). Then `*-monoʳ-≤-nonNeg (1/ mfs)` gives:

$$a \leq b \;\Longrightarrow\; a \times (1/\mathit{mfs}) \leq b \times (1/\mathit{mfs})$$

Since $a \div \mathit{mfs} = a \times (1/\mathit{mfs})$ definitionally (how `_÷_` is defined in the stdlib), the result type matches the efficiency ratio directly.

*Implementation note:* The lemma is not wrapped as a named `div-mono-≤` because Agda's `_÷_` operator requires `{{NonZero c}}` at the type level when `÷` appears in a function's return type. Rather than introduce a lemma with `÷` in its signature, we call `ℚP.*-monoʳ-≤-nonNeg (1/ mfs)` directly and provide the instance chain (`>-nonZero`, `positive`, `1/pos⇒pos`, `pos⇒nonNeg`) in each theorem's `where` block. Agda accepts the result by definitional equality.

### Theorems

**Theorem (l3EffFSDom-l0-inverted).**
In any environment with $v_b \leq v_s$, profitable-pair list $\mathit{ps}$ with $\mathit{mfs} > 0$, and seed population $\Omega$:

$$\text{FSDom}\bigl(\text{concreteL3Eff},\; \text{concreteL0Eff},\; \Omega\bigr)$$

*Proof.*
By `FSD-from-pointwise`; suffices to show $\forall s,\; \text{concreteL0Eff}(s) \leq \text{concreteL3Eff}(s)$.

$$\underbrace{\text{l0}(s) \leq 0}_{\text{l0Nonpos-inverted}} \;\xrightarrow{\times\,(1/\mathit{mfs})}\; \text{l0}(s)/\mathit{mfs} \leq 0 \leq \underbrace{0 \leq \text{l3}(s)/\mathit{mfs}}_{\text{realizedSurplusNonNeg}\,\times\,(1/\mathit{mfs})}$$

Combined by `≤-trans`. $\square$

**Theorem (l0EffFSDom-l3-productive).**
In any environment with $v_s \leq v_b$, $0 \leq v_s$, $\text{cap} \leq p_{\max}$, $\mathit{mfs} > 0$, and $\Omega$:

$$\text{FSDom}\bigl(\text{concreteL0Eff},\; \text{concreteL3Eff},\; \Omega\bigr)$$

*Proof.*
By `FSD-from-pointwise`; suffices to show $\forall s,\; \text{concreteL3Eff}(s) \leq \text{concreteL0Eff}(s)$.

$$\underbrace{\text{l3}(s) \leq \text{l0}(s)}_{\text{l3LE-l0-productive}} \;\xrightarrow{\times\,(1/\mathit{mfs})}\; \text{l3}(s)/\mathit{mfs} \leq \text{l0}(s)/\mathit{mfs} \quad \square$$

**Corollary (l3EffExpected-l0-inverted).**
Inverted market: $\mathbb{E}_\Omega[\text{L3 eff}] \geq \mathbb{E}_\Omega[\text{L0 eff}]$.

Proof: `sumQ-map-mono` applied to the same pointwise bound as the FSD theorem.

**Corollary (l0EffExpected-l3-productive).**
Productive market: $\mathbb{E}_\Omega[\text{L0 eff}] \geq \mathbb{E}_\Omega[\text{L3 eff}]$.

### Hypothesis Discussion: $\mathit{mfs} > 0$

Both theorems require $\mathit{mfs} = \text{maxFeasibleSurplus}(\mathit{ps}) > 0$ for the efficiency ratio to be defined.

In the *productive* case, $\mathit{mfs} > 0$ iff $v_b > v_s$ strictly — the natural assumption for efficiency to be meaningful.

In the *inverted* case, the single simulation pair $(v_b, v_s)$ with $v_b \leq v_s$ contributes zero or negative value to $\mathit{ps}$, so $\mathit{mfs} > 0$ requires the profitable-pair list to include pairs from a parallel productive sub-market. The theorem is stated for any such list, making the scope explicit.

### Extension table

| Result | Module | Depends on |
|--------|--------|------------|
| `l0EfficiencyRatio` | 19 | `l0RealizedSurplus` (mod 10) |
| `concreteL3Eff` | 19 | `efficiencyRatio` (mod 7) + `concreteSim` (mod 14) |
| `concreteL0Eff` | 19 | `l0EfficiencyRatio` + `concreteL0Sim` (mod 15) |
| `l3EffFSDom-l0-inverted` | 19 | `l0Nonpos-inverted` (mod 15) + `realizedSurplusNonNeg` (mod 6) + `FSD-from-pointwise` (mod 17) |
| `l0EffFSDom-l3-productive` | 19 | `l3LE-l0-productive` (mod 15) + `FSD-from-pointwise` (mod 17) |
| Expected corollaries | 19 | same pointwise bounds + `sumQ-map-mono` (reproved locally) |

Zero changes to any existing module.

---

## Module 20: MultiAgentEffFSD

### Motivation

This module closes the 2×2 table of FSD results:

| | Single pair | k pairs |
|--|-------------|---------|
| Raw surplus FSD | Module 17 (`Stochastic`) | Module 18 (`MultiAgentSim`) |
| Efficiency FSD | Module 19 (`EfficiencyFSD`) | **Module 20** (`MultiAgentEffFSD`) |

The k-pair efficiency ratio divides the total portfolio realized surplus by a shared denominator $\mathit{mfs}$. The proofs combine the Vec-induction structure of Module 18 with the division-by-scalar technique of Module 19.

### Definitions

**Portfolio efficiency functions**

$$\text{concreteL3EffN}_{n,k}(\text{envs}, \mathit{ps}, h)(\mathbf{s}) = \frac{\text{realizedSurplusN}_{n,k}(\text{envs}, \mathbf{s})}{\mathit{mfs}}$$
$$\text{concreteL0EffN}_{n,k}(\text{envs}, \mathit{ps}, h)(\mathbf{s}) = \frac{\text{l0RealizedSurplusN}_{n,k}(\text{envs}, \mathbf{s})}{\mathit{mfs}}$$

where $\mathit{mfs} = \text{maxFeasibleSurplus}(\mathit{ps}) > 0$ (shared denominator for all k pairs).

Both are functions $\text{Vec}(\text{Seed}(\text{suc}\,n, 2), k) \to \mathbb{Q}$, the type required by `FSDom`.

### Private Lemmas

**l0LEL3-invertedN** (reproved from private in MultiAgentSim).
In `AllInverted` markets:
$$\text{l0RealizedSurplusN}(\text{envs}, \mathbf{s}) \leq \text{realizedSurplusN}(\text{envs}, \mathbf{s})$$
Proof: Vec induction, applying `l0Nonpos-inverted` + `realizedSurplusNonNeg` + `+-mono-≤` at each step.

**l3LEL0-productiveN** (reproved from private in MultiAgentSim).
In `AllProductive` markets:
$$\text{realizedSurplusN}(\text{envs}, \mathbf{s}) \leq \text{l0RealizedSurplusN}(\text{envs}, \mathbf{s})$$
Proof: Vec induction, applying `l3LE-l0-productive` + `+-mono-≤`.

*Note:* The `AllProductive` constructor `_ap∷_` bundles three conditions as a product `(0ℚ ≤ vS × vS ≤ vB × cap ≤ maxP)`. Pattern matching on the product in a function LHS causes a parse ambiguity with the infix constructor; projections (`proj₁`, `proj₂`) resolve this.

### Theorems

**Theorem (l3EffFSDom-l0-invertedN).**
For $k$ pairs with `AllInverted` conditions, $\mathit{mfs} > 0$, $\Omega$:
$$\text{FSDom}\bigl(\text{concreteL3EffN},\; \text{concreteL0EffN},\; \Omega\bigr)$$

*Proof.* `FSD-from-pointwise` + `l0LEL3-invertedN` lifted by `*-monoʳ-≤-nonNeg (1/ mfs)`. $\square$

**Theorem (l0EffFSDom-l3-productiveN).**
For $k$ pairs with `AllProductive` conditions, $\mathit{mfs} > 0$, $\Omega$:
$$\text{FSDom}\bigl(\text{concreteL0EffN},\; \text{concreteL3EffN},\; \Omega\bigr)$$

*Proof.* `FSD-from-pointwise` + `l3LEL0-productiveN` lifted by `*-monoʳ-≤-nonNeg (1/ mfs)`. $\square$

**Corollary (l3EffExpectedN-l0-inverted).** $\mathbb{E}_\Omega[\text{L3 portfolio eff}] \geq \mathbb{E}_\Omega[\text{L0 portfolio eff}]$.

**Corollary (l0EffExpectedN-l3-productive).** $\mathbb{E}_\Omega[\text{L0 portfolio eff}] \geq \mathbb{E}_\Omega[\text{L3 portfolio eff}]$.

### Extension table

| Result | Module | Depends on |
|--------|--------|------------|
| `concreteL3EffN` | 20 | `realizedSurplusN` (mod 18) + `maxFeasibleSurplus` (mod 7) |
| `concreteL0EffN` | 20 | `l0RealizedSurplusN` (mod 18) |
| `l0LEL3-invertedN` (local) | 20 | `l0Nonpos-inverted` (mod 15) + `realizedSurplusNonNeg` (mod 6) |
| `l3LEL0-productiveN` (local) | 20 | `l3LE-l0-productive` (mod 15) |
| `l3EffFSDom-l0-invertedN` | 20 | local `l0LEL3-invertedN` + `FSD-from-pointwise` (mod 17) |
| `l0EffFSDom-l3-productiveN` | 20 | local `l3LEL0-productiveN` + `FSD-from-pointwise` (mod 17) |
| Expected corollaries | 20 | same pointwise bounds + `sumQ-map-mono` (reproved locally) |

Zero changes to any existing module. The $k=1$ case recovers the single-pair results from Module 19.

---

## Module 21: MixedWelfare

### Motivation

Modules 17–20 assume all pairs share the same market type (all inverted or all productive). Real markets typically mix both: some buyer-seller pairs have $v_b < v_s$ (trades would destroy value) and others $v_s < v_b$ (trades create value). This module asks: given a mixed portfolio, which agent rule achieves the best welfare?

The answer is the **oracle mix**: use L3 for inverted pairs (to prevent harmful trades) and L0 for productive pairs (to execute beneficial ones). This oracle mix FSD-dominates both pure strategies simultaneously.

### The Mixed Predicate

$$\text{data Mixed} : \forall \{k\} \to \text{Vec SimEnvironment}\, k \to \text{Set}$$

Constructors:
- $\text{mix[]} : \text{Mixed}\, \mathbf{[]}$
- $\text{invMix} : v_b(e) \leq v_s(e) \to \text{Mixed}\, \mathit{es} \to \text{Mixed}\, (e \mathbin{v\!\!:\!:} \mathit{es})$
- $\text{prodMix} : (0 \leq v_s(e) \times v_s(e) \leq v_b(e) \times \text{cap}(e) \leq p_{\max}(e)) \to \text{Mixed}\, \mathit{es} \to \text{Mixed}\, (e \mathbin{v\!\!:\!:} \mathit{es})$

`Mixed` generalises both `AllInverted` (all constructors `invMix`) and `AllProductive` (all `prodMix`).

### Oracle Mix Simulation

$$\text{concreteMixSurplusN}(\text{envs}, h, \mathbf{s}) = \begin{cases}
0 & k = 0 \\
\text{realizedSurplus}(\text{concreteSim}(e, s_1)) + \text{concreteMixSurplusN}(\mathit{es}, h', \mathbf{s'}) & \text{invMix case} \\
\text{l0RealizedSurplus}(\text{concreteL0Sim}(e, s_1)) + \text{concreteMixSurplusN}(\mathit{es}, h', \mathbf{s'}) & \text{prodMix case}
\end{cases}$$

The function recurses on the `Mixed` proof $h$, dispatching to L3 or L0 at each pair.

### Pointwise Bounds (Private)

**l3LE-mix**: $\forall \mathbf{s},\; \text{realizedSurplusN}(\text{envs}, \mathbf{s}) \leq \text{concreteMixSurplusN}(\text{envs}, h, \mathbf{s})$

*Proof by induction on Mixed:*
- `mix[]`: $0 \leq 0$ by `≤-refl`.
- `invMix` case: mix and L3 use the same (L3) strategy for head pair. Head contributions equal; `+-monoʳ-≤ (realizedSurplus ...) IH`.
- `prodMix` case: head L3 surplus ≤ head L0 surplus = mix surplus, by `l3LE-l0-productive`; tail by IH via `+-mono-≤`.

**l0LE-mix**: $\forall \mathbf{s},\; \text{l0RealizedSurplusN}(\text{envs}, \mathbf{s}) \leq \text{concreteMixSurplusN}(\text{envs}, h, \mathbf{s})$

*Proof by induction on Mixed:*
- `invMix` case: head L0 surplus $\leq 0 \leq$ head L3 surplus = mix surplus, by `l0Nonpos-inverted` + `realizedSurplusNonNeg`; tail by IH.
- `prodMix` case: mix uses L0 for head; contributions equal; `+-monoʳ-≤ (l0RealizedSurplus ...) IH`.

*Implementation note:* `+-monoʳ-≤ r h` (stdlib) takes the common addend `r` explicitly. This is necessary for the `≤-refl` cases: `+-mono-≤ ≤-refl h` leaves an implicit metavariable for the common term that Agda cannot infer from an unreduced `realizedSurplusN` goal. Providing `r` explicitly forces the unification.

### Theorems

**Theorem (mixFSDom-l3).** For any Mixed portfolio and $\Omega$:
$$\text{FSDom}\bigl(\text{concreteMixSurplusN}(\text{envs}, h),\; \text{realizedSurplusN}(\text{envs}),\; \Omega\bigr)$$

*Proof:* `FSD-from-pointwise` + `l3LE-mix`. $\square$

**Theorem (mixFSDom-l0).** For any Mixed portfolio and $\Omega$:
$$\text{FSDom}\bigl(\text{concreteMixSurplusN}(\text{envs}, h),\; \text{l0RealizedSurplusN}(\text{envs}),\; \Omega\bigr)$$

*Proof:* `FSD-from-pointwise` + `l0LE-mix`. $\square$

**Corollary (mixExpected-l3).** $\mathbb{E}_\Omega[\text{L3 welfare}] \leq \mathbb{E}_\Omega[\text{oracle mix welfare}]$.

**Corollary (mixExpected-l0).** $\mathbb{E}_\Omega[\text{L0 welfare}] \leq \mathbb{E}_\Omega[\text{oracle mix welfare}]$.

### Special Cases and Generalisation

| Mixed conditions | concreteMixSurplusN | mixFSDom-l3 | mixFSDom-l0 |
|------------------|---------------------|-------------|-------------|
| All `invMix` | = realizedSurplusN | trivial | = `l3FSDom-l0-invertedN` (Mod 18) |
| All `prodMix` | = l0RealizedSurplusN | = `l0FSDom-l3-productiveN` (Mod 18) | trivial |
| Mixed | oracle dominates both | new | new |

Module 21 strictly generalises `MultiAgentSim`'s FSD results. Zero changes to any existing module.

### Extension table

| Result | Module | Depends on |
|--------|--------|------------|
| `Mixed` predicate | 21 | `AllInverted`/`AllProductive` conditions (mod 18) |
| `concreteMixSurplusN` | 21 | `concreteSim` (mod 14) + `concreteL0Sim` (mod 15) |
| `l3LE-mix` (private) | 21 | `l3LE-l0-productive` (mod 15) |
| `l0LE-mix` (private) | 21 | `l0Nonpos-inverted` (mod 15) + `realizedSurplusNonNeg` (mod 6) |
| `mixFSDom-l3`, `mixFSDom-l0` | 21 | `FSD-from-pointwise` (mod 17) |
| `mixExpected-l3`, `mixExpected-l0` | 21 | `sumQ-map-mono` (reproved locally) |

---

## Module 22: MixedEffFSD

### Motivation

Module 21 proves oracle-mix welfare dominance on raw surplus. This module lifts to the efficiency ratio, closing the final cell of the 3D result table:

| | Single pair | k pairs | Mixed market |
|--|-------------|---------|--------------|
| Raw surplus FSD | Mod 17 | Mod 18 | Mod 21 |
| Efficiency FSD | Mod 19 | Mod 20 | **Mod 22** |

### Definition

$$\text{concreteMixEffN}_{n,k}(\text{envs}, h, \mathit{ps}, m, \mathbf{s}) = \frac{\text{concreteMixSurplusN}_{n,k}(\text{envs}, h, \mathbf{s})}{\mathit{mfs}}$$

where $m : 0 < \mathit{mfs}$.

### Private Lemmas

`l3LE-mix` and `l0LE-mix` from Module 21 are reproved locally (they are private there).  The proofs are identical.

### Theorems

**Theorem (mixEffFSDom-l3).**
For any Mixed portfolio, $\mathit{mfs} > 0$, and $\Omega$:
$$\text{FSDom}\bigl(\text{concreteMixEffN},\; \text{concreteL3EffN},\; \Omega\bigr)$$

*Proof:* `FSD-from-pointwise` + `l3LE-mix` lifted by `*-monoʳ-≤-nonNeg (1/ mfs)`. $\square$

**Theorem (mixEffFSDom-l0).**
$$\text{FSDom}\bigl(\text{concreteMixEffN},\; \text{concreteL0EffN},\; \Omega\bigr)$$

*Proof:* `FSD-from-pointwise` + `l0LE-mix` lifted by `*-monoʳ-≤-nonNeg (1/ mfs)`. $\square$

**Corollaries:** `mixEffExpected-l3`, `mixEffExpected-l0` via `sumQ-map-mono`.

Zero changes to any existing module.

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
