import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim17558

noncomputable section

/-- The rational lower-triangular matrix from claim 17558. -/
def lowerTriangularFactor (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j =>
    if j ≤ i then
      (Nat.choose i.val j.val : ℚ) * (Nat.factorial (2 * j.val) : ℚ) /
        (Nat.factorial (i.val + j.val) : ℚ)
    else 0

theorem lowerTriangularFactor_isLowerTriangular_claim17558 (n : ℕ) :
    (lowerTriangularFactor n).IsLowerTriangular := by
  intro i j hij
  simp only [lowerTriangularFactor]
  have hji : ¬j ≤ i := by
    exact not_le_of_gt (show i < j from hij)
  simp [hji]

theorem lowerTriangularFactor_diag_claim17558 (n : ℕ) (i : Fin n) :
    lowerTriangularFactor n i i = 1 := by
  have h : 2 * i.val = i.val + i.val := by omega
  simp [lowerTriangularFactor, h, Nat.factorial_ne_zero]

end

end MathlibPlus.LinearAlgebra.Claim17558
