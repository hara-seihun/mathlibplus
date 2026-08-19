import Mathlib

namespace MathlibPlus.Algebra.TriangularBinomial

open scoped BigOperators

/-- Claim 852: at one triangular substitution `βᵢ = yᵢ + βᵢ₊₁`, a monomial
factor transforms by the displayed binomial recurrence. -/
theorem monomial_substitution
    {R : Type*} [CommSemiring R] (c y beta : R) (a b : ℕ) :
    c * (y + beta) ^ a * beta ^ b =
      Finset.sum (Finset.range (a + 1)) (fun k =>
        c * (Nat.choose a k : R) * y ^ k * beta ^ (a - k + b)) := by
  rw [add_pow]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    c * (y ^ k * beta ^ (a - k) * (Nat.choose a k : R)) * beta ^ b =
        c * (Nat.choose a k : R) * y ^ k *
          (beta ^ (a - k) * beta ^ b) := by ring
    _ = c * (Nat.choose a k : R) * y ^ k * beta ^ (a - k + b) := by
      rw [← pow_add]

end MathlibPlus.Algebra.TriangularBinomial
