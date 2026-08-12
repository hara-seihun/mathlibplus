import Mathlib

namespace MathlibPlus.NumberTheory.Claim1372

/-!
The packet's prime-only Chebyshev difference is expanded here as the finite
sum over natural primes in the interval.  No analytic convention for a
separate `θ` function is introduced.
-/

/-- A positive prime-only logarithmic interval sum contains a prime. -/
theorem positivePrimeIntervalLogSumSuppliesPrime
    {x y : ℝ}
    (h : 0 < Finset.sum
      ((Finset.range (Nat.floor y + 1)).filter
        (fun p : ℕ => Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y))
      (fun p : ℕ => Real.log p)) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  by_contra hNoPrime
  have hEmpty :
      (Finset.range (Nat.floor y + 1)).filter
        (fun p : ℕ => Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p hp hPred
    exact hNoPrime ⟨p, hPred⟩
  rw [hEmpty] at h
  simpa using h

end MathlibPlus.NumberTheory.Claim1372
