-- PriceGrid.agda
-- Uniform price grids for ZIT simulation.
--
-- A price grid maps a seed index i : Fin (suc n) to a rational price.
-- Two grid families are defined:
--
--   buyerTick  n v b   i  =  (v ⊓ b) * (toℕ i / (suc n))
--     → prices in [0, min(v,b)], ensuring bid ≤ v AND bid ≤ b (L3 buyer)
--
--   sellerTick n v maxP i  =  v + (maxP - v) * (toℕ i / (suc n))
--     → prices in [v, maxP), ensuring ask ≥ v (L3 seller)
--
-- All lemmas are proved formally, including ratioLeOne.
-- The proof of ratioLeOne goes through the GCD-reduction representation:
--   normalize m d stores (m/g, d/g) where g = gcd(m,d).
--   The ↥/↧ properties give N*G = m and D*G = d.
--   Since m < d, we get N*G ≤ D*G, and cancel G to get N ≤ D.
--   This is the ↥ ≤ ↧ condition required by *≤* for ≤ 1ℚ.
--
-- No postulates remain in this module.
--
-- New Agda ideas:
--   *≤*   — direct constructor for ℚ ≤, using cross-multiplication
--   +≤+   — direct constructor for ℤ ≤, lifting ℕ ≤
--   subst₂ — substitute in a binary relation using two equalities
--   import M as N  — qualified access to module M under alias N
module PriceGrid where

open import Data.Nat             using (ℕ; suc)
open import Data.Fin             using (Fin; toℕ)
open import Data.Integer         using (+_)
import Data.Integer.Base         as ℤ
import Data.Integer.Properties   as ℤ
open import Data.Integer.GCD     using (gcd)
import Data.Nat.GCD              as ℕ
import Data.Nat.Properties       as ℕ
open import Data.Fin.Properties  using (toℕ<n)
open import Data.Rational        using (ℚ; _*_; _+_; _-_; _/_; _⊓_; 0ℚ; 1ℚ; _≤_; ↥_; ↧_; *≤*)
open import Data.Rational        using (NonNegative; nonNegative)
open import Data.Rational.Properties
  using ( normalize-nonNeg; nonNegative⁻¹
        ; *-monoˡ-≤-nonNeg; *-identityʳ
        ; ≤-refl; ≤-trans
        ; nonNeg*nonNeg⇒nonNeg
        ; +-monoʳ-≤; +-identityʳ
        ; p⊓q≤p; p⊓q≤q
        ; ↥-normalize; ↧-normalize)
open import Relation.Binary.PropositionalEquality using (subst; sym; subst₂; _≢_; _≡_)
open import Data.Sum.Base        using (inj₂)

open import Surplus using (p≤q⇒0≤q-p)


-- ── Unit Ratio ────────────────────────────────────────────────────────────────
--
-- ratio n i  =  (toℕ i) / (suc n)
-- For i : Fin (suc n), the index ranges 0, 1, ..., n.
-- The ratio ranges 0/(n+1), 1/(n+1), ..., n/(n+1).
-- This is strictly less than 1 (the grid never reaches the cap exactly,
-- which prevents irrational bids equal to valuation under integer arithmetic).
--
-- In Agda:
--   (+ toℕ i) : ℤ  — natural number injected into integers
--   _/_ : ℤ → ℕ → {{NonZero}} → ℚ  — rational from integer and nat
--   suc n is NonZero automatically (instance nonZero from Data.Nat)

ratio : (n : ℕ) → Fin (suc n) → ℚ
ratio n i = (+ toℕ i) / suc n


-- ── Theorem: ratio ≥ 0 ───────────────────────────────────────────────────────
--
-- PROOF.
--   ratio n i = (+ toℕ i) / suc n = normalize (toℕ i) (suc n)
--   normalize-nonNeg (toℕ i) (suc n) : NonNegative (normalize (toℕ i) (suc n))
--   nonNegative⁻¹ extracts the 0ℚ ≤ ratio from the NonNegative evidence.
--
-- The definition (+ m / d) = normalize m d lives in Data.Rational.Base.
-- normalize-nonNeg is the key library lemma for non-negative normalized rationals.

ratioNonNeg : ∀ (n : ℕ) (i : Fin (suc n)) → 0ℚ ≤ ratio n i
ratioNonNeg n i = nonNegative⁻¹ (ratio n i)
  where
    instance
      _ : NonNegative (ratio n i)
      _ = normalize-nonNeg (toℕ i) (suc n)


-- ── Theorem: ratio ≤ 1 ───────────────────────────────────────────────────────
--
-- THEOREM.  ∀ n i, (toℕ i) / (suc n) ≤ 1ℚ.
--
-- PROOF STRATEGY.
-- The ℚ ordering is defined as:
--   p ≤ q  iff  ↥p * ↧q ≤ ↥q * ↧p   (cross-multiplication, in ℤ)
-- where ↥ is the numerator and ↧ the denominator.
--
-- For p = normalize m d (with m = toℕ i, d = suc n) and q = 1ℚ:
--   ↥ 1ℚ = + 1,  ↧ 1ℚ = + 1
-- so the condition reduces to:
--   ↥(normalize m d) ≤ ↧(normalize m d)
--
-- Let N = ↥(normalize m d), D = ↧(normalize m d), G = gcd(+m, +d).
-- The stdlib lemmas ↥-normalize and ↧-normalize give:
--   N * G ≡ + m   and   D * G ≡ + d
-- Since m < d (from toℕ i < suc n), we have + m ≤ + d.
-- Rewriting: N * G ≤ D * G.
-- G is positive (gcd of a positive integer is positive).
-- Cancel G: N ≤ D.
-- Wrap in *≤* with identity rewrites: ratio n i ≤ 1ℚ. □

ratioLeOne : ∀ (n : ℕ) (i : Fin (suc n)) → ratio n i ≤ 1ℚ
ratioLeOne n i = *≤* final
  where
    m = toℕ i
    d = suc n

    -- g : ℕ  — the natural-number gcd of numerator and denominator
    g = ℕ.gcd m d

    -- G : ℤ  — the integer gcd; definitionally equal to + g
    G = gcd (ℤ.+ m) (ℤ.+ d)

    -- g ≠ 0: since d = suc n ≠ 0, the gcd is nonzero
    g≢0 : g ≢ 0
    g≢0 = ℕ.gcd[m,n]≢0 m d (inj₂ λ())

    -- G is a positive integer (gcd of a nonzero denominator)
    -- The positive : ∀ {i} → 0 < i → Positive i constructor lifts ℕ < to ℤ Positive.
    -- ℤ.+<+ : m ℕ.< n → + m ℤ.< + n lifts ℕ strictly-less.
    G-pos : ℤ.Positive G
    G-pos = ℤ.positive (ℤ.+<+ (ℕ.n≢0⇒n>0 g≢0))

    -- Abbreviations for the reduced numerator and denominator
    N = ↥ (ratio n i)
    D = ↧ (ratio n i)

    -- ↥-normalize and ↧-normalize from Data.Rational.Properties:
    --   N * G ≡ + m   (the numerator times the gcd equals the original numerator)
    --   D * G ≡ + d   (the denominator times the gcd equals the original denominator)
    eq-N : N ℤ.* G ≡ ℤ.+ m
    eq-N = ↥-normalize m d

    eq-D : D ℤ.* G ≡ ℤ.+ d
    eq-D = ↧-normalize m d

    -- + m ≤ + d  because  m = toℕ i < suc n = d
    -- +≤+ : m ℕ.≤ n → + m ℤ.≤ + n lifts ℕ ≤ to ℤ ≤.
    -- ℕ.<⇒≤ : m < n → m ≤ n weakens the strict bound.
    m≤d : ℤ.+ m ℤ.≤ ℤ.+ d
    m≤d = ℤ.+≤+ (ℕ.<⇒≤ (toℕ<n i))

    -- Rewrite m ≤ d as N*G ≤ D*G using the two equalities above.
    -- subst₂ P (sym eq1) (sym eq2) h
    --   takes h : P x₁ y₁ and replaces x₁ with x₂ (via eq1 : x₁ ≡ x₂)
    --   and y₁ with y₂ (via eq2 : y₁ ≡ y₂), giving P x₂ y₂.
    NG≤DG : N ℤ.* G ℤ.≤ D ℤ.* G
    NG≤DG = subst₂ ℤ._≤_ (sym eq-N) (sym eq-D) m≤d

    -- Cancel G from both sides.
    -- *-cancelʳ-≤-pos : i * k ≤ j * k → i ≤ j  (when k is Positive)
    N≤D : N ℤ.≤ D
    N≤D = ℤ.*-cancelʳ-≤-pos N D G {{G-pos}} NG≤DG

    -- The ℚ ordering *≤* requires  ↥(ratio) * ↧(1ℚ) ≤ ↥(1ℚ) * ↧(ratio).
    -- Since ↥ 1ℚ = + 1 and ↧ 1ℚ = + 1, this is N * (+ 1) ≤ (+ 1) * D.
    -- *-identityʳ N : N * 1ℤ ≡ N  and  *-identityˡ D : 1ℤ * D ≡ D.
    -- We rewrite N and D in N≤D outward to get the cross-multiplication form.
    final : N ℤ.* ↧ 1ℚ ℤ.≤ ↥ 1ℚ ℤ.* D
    final = subst₂ ℤ._≤_
              (sym (ℤ.*-identityʳ N))
              (sym (ℤ.*-identityˡ D))
              N≤D


-- ── tick: scale ratio to [0, cap] ────────────────────────────────────────────
--
-- tick n cap i  =  cap * ratio n i
-- Interprets seed index i as a price via uniform grid with given ceiling cap.
--
-- In Julia: cap * (i-1)/(n+1) for i ∈ 1:suc n  (0-indexed Agda: i ∈ 0:n)

tick : (n : ℕ) → ℚ → Fin (suc n) → ℚ
tick n cap i = cap * ratio n i


-- ── Theorem: tick ≥ 0 ────────────────────────────────────────────────────────
--
-- When cap ≥ 0, tick is non-negative: product of two non-negatives.
-- The proof assembles NonNegative instances for cap and ratio, then uses
-- nonNeg*nonNeg⇒nonNeg, then extracts the 0ℚ ≤ ... inequality.

tickNonNeg
  : ∀ (n : ℕ) (cap : ℚ) (i : Fin (suc n))
  → 0ℚ ≤ cap
  → 0ℚ ≤ tick n cap i
tickNonNeg n cap i cap≥0 = nonNegative⁻¹ (tick n cap i)
  where
    instance
      nc : NonNegative cap
      nc = nonNegative cap≥0
      nr : NonNegative (ratio n i)
      nr = nonNegative (ratioNonNeg n i)
      nt : NonNegative (tick n cap i)
      nt = nonNeg*nonNeg⇒nonNeg cap (ratio n i)


-- ── Theorem: tick ≤ cap ──────────────────────────────────────────────────────
--
-- PROOF.
--   tick n cap i = cap * ratio n i ≤ cap * 1  [*-monoˡ-≤-nonNeg, ratioLeOne]
--                                 = cap        [*-identityʳ, via subst]

tickLeOneCap
  : ∀ (n : ℕ) (cap : ℚ) (i : Fin (suc n))
  → 0ℚ ≤ cap
  → tick n cap i ≤ cap
tickLeOneCap n cap i cap≥0 =
  subst (tick n cap i ≤_) (*-identityʳ cap)
    (*-monoˡ-≤-nonNeg cap (ratioLeOne n i))
  where
    instance
      _ : NonNegative cap
      _ = nonNegative cap≥0


-- ── buyerTick: grid on [0, min(v,b)] ─────────────────────────────────────────
--
-- For a buyer with valuation v and budget b, the L3 constraint requires
-- both bid ≤ v (no overbidding) and bid ≤ b (budget feasibility).
-- The tightest admissible ceiling is min(v, b) = v ⊓ b.
--
-- In Agda, _⊓_ is min for ℚ from Data.Rational.
-- Properties used: p⊓q≤p and p⊓q≤q from Data.Rational.Properties.

buyerTick : (n : ℕ) → ℚ → ℚ → Fin (suc n) → ℚ
buyerTick n v b i = tick n (v ⊓ b) i


-- ── Theorem: buyerTick ≤ v ───────────────────────────────────────────────────
--
-- PROOF.
--   buyerTick n v b i  ≤  v ⊓ b   [tickLeOneCap, assuming 0 ≤ v ⊓ b]
--                      ≤  v        [p⊓q≤p v b]

buyerTickBelowValuation
  : ∀ (n : ℕ) (v b : ℚ) (i : Fin (suc n))
  → 0ℚ ≤ v ⊓ b
  → buyerTick n v b i ≤ v
buyerTickBelowValuation n v b i vb≥0 =
  ≤-trans (tickLeOneCap n (v ⊓ b) i vb≥0) (p⊓q≤p v b)


-- ── Theorem: buyerTick ≤ b ───────────────────────────────────────────────────
--
-- Same structure, using p⊓q≤q.

buyerTickWithinBudget
  : ∀ (n : ℕ) (v b : ℚ) (i : Fin (suc n))
  → 0ℚ ≤ v ⊓ b
  → buyerTick n v b i ≤ b
buyerTickWithinBudget n v b i vb≥0 =
  ≤-trans (tickLeOneCap n (v ⊓ b) i vb≥0) (p⊓q≤q v b)


-- ── sellerTick: offset grid on [v, maxP) ─────────────────────────────────────
--
-- For a seller with reservation price v (valuation) and market maximum maxP,
-- the L3 constraint requires ask ≥ v.
-- Formula: sellerTick n v maxP i = v + (maxP - v) * ratio n i
-- At i = 0: ask = v + 0 = v.      At i = n: ask ≈ maxP.
--
-- The spread (maxP - v) is non-negative when v ≤ maxP.
-- Adding it to v (scaled by ratio ∈ [0,1)) gives prices ≥ v.

sellerTick : (n : ℕ) → ℚ → ℚ → Fin (suc n) → ℚ
sellerTick n v maxP i = v + (maxP - v) * ratio n i


-- ── Local helper: x ≤ x + y when 0 ≤ y ──────────────────────────────────────
--
-- In ℚ, x = x + 0 ≤ x + y by right-monotonicity of +.
-- subst rewrites x + 0 to x using +-identityʳ.

private
  p≤p+q : ∀ {p q : ℚ} → 0ℚ ≤ q → p ≤ p + q
  p≤p+q {p} {q} 0≤q =
    subst (_≤ p + q) (+-identityʳ p) (+-monoʳ-≤ p 0≤q)


-- ── Theorem: sellerTick ≥ v ──────────────────────────────────────────────────
--
-- PROOF.
--   0 ≤ maxP - v             [v ≤ maxP, by p≤q⇒0≤q-p]
--   0 ≤ ratio n i            [ratioNonNeg]
--   0 ≤ (maxP - v) * ratio   [nonNeg*nonNeg⇒nonNeg]
--   v ≤ v + (maxP-v)*ratio   [p≤p+q above]

sellerTickAboveValuation
  : ∀ (n : ℕ) (v maxP : ℚ) (i : Fin (suc n))
  → v ≤ maxP
  → v ≤ sellerTick n v maxP i
sellerTickAboveValuation n v maxP i v≤maxP = p≤p+q product≥0
  where
    spread≥0 : 0ℚ ≤ maxP - v
    spread≥0 = p≤q⇒0≤q-p v≤maxP
    instance
      ns : NonNegative (maxP - v)
      ns = nonNegative spread≥0
      nr : NonNegative (ratio n i)
      nr = nonNegative (ratioNonNeg n i)
    product≥0 : 0ℚ ≤ (maxP - v) * ratio n i
    product≥0 = nonNegative⁻¹ ((maxP - v) * ratio n i)
      where
        instance
          _ : NonNegative ((maxP - v) * ratio n i)
          _ = nonNeg*nonNeg⇒nonNeg (maxP - v) (ratio n i)
