import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim17587

open scoped BigOperators

/-- Claim 17587: a positive rank-one transmission term is positive semidefinite. -/
theorem rankOneTransmissionTerm_posSemidef_claim17587
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ι → ℝ) :
    Matrix.PosSemidef (fun i j => (1 / 4 : ℝ) * h i * h j) := by
  have hherm : Matrix.IsHermitian (fun i j => (1 / 4 : ℝ) * h i * h j) := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp
    ring
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
  intro x
  rw [show star x = x by rfl]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hfactor :
      (∑ a, ∑ b, x a * ((1 / 4 : ℝ) * h a * h b * x b)) =
        (1 / 4 : ℝ) *
          ((∑ a, h a * x a) * (∑ b, h b * x b)) := by
    rw [Fintype.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hfactor]
  apply mul_nonneg
  · norm_num
  · simpa only [pow_two] using sq_nonneg (∑ a, h a * x a)

end MathlibPlus.LinearAlgebra.Claim17587
