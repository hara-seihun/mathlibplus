import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- Claim 13393: the finite Euler coefficient error and its two elementary
prime/integer tail bounds. The cutoff is a positive real; the finite product
uses exactly the primes at most that cutoff. -/
def finiteEulerCoefficientError_13393 : Prop :=
  ∀ (y : ℝ) (k : ℕ),
    0 < y → 2 ≤ k →
      let A : ℝ :=
        ∏ p ∈ Finset.filter (fun p : ℕ => Nat.Prime p)
          (Finset.Icc 2 ⌊y⌋₊),
          (1 - (p : ℝ)⁻¹ ^ k)
      let primeTail : ℝ :=
        ∑' p : {p : ℕ // Nat.Prime p ∧ y < (p : ℝ)},
          ((p.1 : ℝ)⁻¹) ^ k
      let integerTail : ℝ :=
        ∑' n : {n : ℕ // y < (n : ℝ)},
          ((n.1 : ℝ)⁻¹) ^ k
      0 ≤ A - ((riemannZeta (k : ℂ)).re)⁻¹ ∧
        A - ((riemannZeta (k : ℂ)).re)⁻¹ ≤ primeTail ∧
        primeTail ≤ integerTail ∧
        integerTail ≤ (y : ℝ) ^ (1 - (k : ℤ)) / (k - 1 : ℝ)

end MathlibPlus.Open.Analysis
