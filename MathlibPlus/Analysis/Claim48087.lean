import Mathlib

namespace MathlibPlus.Analysis.Claim48087

open scoped BigOperators

/-- The finite cyclic quadratic certificate; a cyclic shift is an instance of
an equivalence of the finite index set. -/
theorem finiteUnitaryEulerCertificate {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (σ : ι ≃ ι) :
    2 * ∑ i, v i ^ 2 + ∑ i, v i * v (σ i) =
      ∑ i, v i ^ 2 + (1 / 2 : ℝ) * ∑ i, (v i + v (σ i)) ^ 2 := by
  have hperm : (∑ i, v (σ i) ^ 2) = ∑ i, v i ^ 2 := by
    simpa using (Equiv.sum_comp σ (fun i => v i ^ 2))
  have hexpand :
      (∑ i, (v i + v (σ i)) ^ 2) =
        ∑ i, v i ^ 2 + 2 * ∑ i, v i * v (σ i) +
          ∑ i, v (σ i) ^ 2 := by
    calc
      (∑ i, (v i + v (σ i)) ^ 2) =
          ∑ i, (v i ^ 2 + 2 * (v i * v (σ i)) + v (σ i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = ∑ i, v i ^ 2 + 2 * ∑ i, v i * v (σ i) +
          ∑ i, v (σ i) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            congr 1
            rw [← Finset.mul_sum]
  rw [hexpand, hperm]
  ring

end MathlibPlus.Analysis.Claim48087
