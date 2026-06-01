# Verified Institutional Economics in Agda
## Phase 1 Case Study: Zero-Intelligence Traders (ZIT)

### Purpose

This project is not primarily a market simulation.

It is a formalization of economic institutions using dependent type theory.

The first case study is the Gode-Sunder Zero-Intelligence Traders model, but the architecture should support future extensions to housing, land-use, banking, matching markets, and antitrust models.

Core object:

Institution × Seed -> CertifiedTrace

The institution is primary.
Agents generate proposals; institutions determine which proposals become economically meaningful events.

## Technology Choices

- Vanilla Agda only
- No Cubical Agda
- No Univalence
- Rational prices
- One-unit traders
- Oracle-tape seeds
- Constructive finite probability

## Institutions

Phase 1 institutions:

1. Continuous Double Auction (CDA)
2. Batch Clearing Auction

## Constraint Hierarchy

L0: Pure random behavior

L1: Accounting constraints

L2: Inventory constraints

L3: Valuation constraints (constrained ZI)

L4: Strategic behavior (future work)

## Agents

Agents contain:

- trader id
- role
- valuation schedule v(q)
- budget
- inventory

Even with one-unit traders, use valuation schedules to future-proof the design.

## Seeds

Seeds are finite oracle tapes.

All behavior must be reproducible from the seed.

## Raw Proposals

Raw proposals may be invalid.

Examples:

- bid above valuation
- insufficient budget
- infeasible ask

## Institutional Processing

Institution processes raw proposals.

Result:

- Accepted
- Rejected

Accepted actions carry proofs of admissibility.

## Certified Traces

Certified traces are correct-by-construction.

Illegal institutional states cannot appear.

## Event Semantics

Primitive representation is an event trace.

Event vocabulary:

- OrderSubmitted
- OrderRejected
- OrderAccepted
- OrderMatched
- TradeSettled
- AuctionCleared

## Derived Views

bookView : Trace -> OrderBook

tradesView : Trace -> Trades

surplusView : Trace -> Rational

efficiencyView : Trace -> Rational

## Probability

For finite seed space Σ:

P(E) =
count(seeds satisfying E) /
count(Σ)

No measure theory in Phase 1.

## Efficiency

Ex post efficiency is primitive:

RealizedSurplus(trace) /
MaximumFeasibleSurplus(trace)

Ex ante efficiency is derived by averaging over a finite seed space.

## Verification Philosophy

Hybrid approach:

- invalid raw proposals allowed
- institution filters proposals
- certified traces are correct-by-construction

## Initial Theorems

- Feasibility
- Accounting preservation
- Inventory preservation
- Rationality of L3 traders
- Provenance of trades

## Flagship Theorem

Institutional Dominance Theorem:

E[Efficiency(L3)] > E[Efficiency(L0)]

or

E[Efficiency(L3)] > E[Efficiency(L1)]

for a fixed institution and finite seed space.

## Future Extensions

- Multi-unit traders
- Metalog-generated valuations
- Housing markets
- Banking systems
- Land-use models
- Antitrust models
- Cubical Agda equivalence reasoning

## Guidance for Coding Agents

1. Build small compiling modules.
2. Explain every Agda construct.
3. Prove small lemmas first.
4. Keep institutions separate from observables.
5. Treat institutions as primary objects.
