import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim4903

open scoped Kronecker

/-- The Kronecker product of two symmetric square matrices is symmetric. -/
theorem kronecker_isSymm
    {R ι κ : Type*} [Mul R]
    {D : Matrix ι ι R} {M : Matrix κ κ R}
    (hD : D.IsSymm) (hM : M.IsSymm) :
    (D ⊗ₖ M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.kronecker_apply]
  rw [hD.apply, hM.apply]

/-- The historical diagonal used in the exact three-level check. -/
theorem historicalDiagonal_isSymm :
    (Matrix.diagonal ![1, -(1 / 2 : ℚ), (1 / 72 : ℚ)]).IsSymm := by
  exact Matrix.isSymm_diagonal _

end MathlibPlus.LinearAlgebra.Claim4903
