import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- Negative Li coefficients force a finite-prime energy lower bound on dyadic intervals. -/
def negativeLiCoefficientsForceFinitePrimeEnergy : Prop :=
  ∀ (η S_inf : ℕ → ℝ) (c : ℝ) (N0 : ℕ),
    0 < c →
      (∀ N : ℕ, N0 ≤ N →
        ∀ n : ℕ, n ∈ Finset.Ioc N (2 * N) →
          c * (N : ℝ) * Real.log (N : ℝ) ≤ S_inf n + 1) →
      let S_f : ℕ → ℝ :=
        fun n => Finset.sum (Finset.Icc 1 n)
          (fun j => (Nat.choose n j : ℝ) * η (j - 1))
      let A : ℕ → ℝ := fun n => S_inf n + 1
      let liCoeff : ℕ → ℝ := fun n => S_inf n - S_f n + 1
      let E_N : ℕ → Finset ℕ :=
        fun N => (Finset.Ioc N (2 * N)).filter (fun n => liCoeff n < 0)
      (∀ (N n : ℕ), n ∈ E_N N → S_f n > A n) ∧
        ∀ N : ℕ, max N0 2 ≤ N →
          Finset.sum (Finset.Ioc N (2 * N))
              (fun n => (S_f n) ^ 2 / (n : ℝ)) ≥
            (c ^ 2 / 2) * ((E_N N).card : ℝ) * (N : ℝ) *
              (Real.log (N : ℝ)) ^ 2

end MathlibPlus.Open.Analysis
