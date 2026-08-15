import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators

noncomputable section

open Classical

/-- The linear factor indexed by a principal-product pair. -/
def hookLinear (p q : ℕ) : Polynomial ℝ :=
  2 * Polynomial.X + Polynomial.C (p + q + 1 : ℝ)

def hookPrincipal (d : ℕ) : Polynomial ℝ :=
  Polynomial.C (d.factorial : ℝ) *
    ∏ p ∈ Finset.range (d + 1),
      ∏ q ∈ Finset.Ioc p (d + 1), hookLinear p q

def hookDelta (d n ell : ℕ) : Polynomial ℝ :=
  ∏ r ∈ Finset.range (n + ell), hookLinear 0 (d - ell + r)

def hookSelected (d n ell : ℕ) : Polynomial ℝ :=
  (∏ r ∈ Finset.range ell, hookLinear 0 (d - ell + r)) *
    (∏ p ∈ Finset.range n, hookLinear p d)

def hookIsSelected (d n ell p q : ℕ) : Prop :=
  (p = 0 ∧ d - ell ≤ q ∧ q < d) ∨ (q = d ∧ p < n)

def hookRemaining (d n ell : ℕ) : Polynomial ℝ :=
  Polynomial.C (d.factorial : ℝ) *
    ∏ p ∈ Finset.range (d + 1),
      ∏ q ∈ Finset.Ioc p (d + 1),
        if hookIsSelected d n ell p q then 1 else hookLinear p q

/-- Admitted hook-denominator cancellation and positive quotient. -/
def claim1797 : Prop :=
  ∀ (d n ell : ℕ),
    (1 ≤ d ∧ 1 ≤ n ∧ n ≤ d ∧ ell < d) →
      hookDelta d n ell = hookSelected d n ell ∧
      hookPrincipal d = hookDelta d n ell * hookRemaining d n ell ∧
      hookDelta d n ell ∣ hookPrincipal d ∧
      (∀ b : ℝ, 0 < b →
        0 < Polynomial.eval b (hookRemaining d n ell))

end

end MathlibPlus.Open.Research
