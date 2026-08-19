import Mathlib

namespace MathlibPlus.Analysis.ContiguousMinorSymmetry

/-- Symmetry of an off-diagonal contiguous minor of a symmetric kernel. -/
theorem tau_swap
    (N a b : ℕ) (g : ℕ → ℕ → ℝ)
    (h_symm : ∀ i j, g i j = g j i) :
    Matrix.det (fun i j : Fin N => g (a + (i : ℕ)) (b + (j : ℕ))) =
      Matrix.det (fun i j : Fin N => g (b + (i : ℕ)) (a + (j : ℕ))) := by
  have h_transpose :
      (fun i j : Fin N => g (a + (i : ℕ)) (b + (j : ℕ))) =
        Matrix.transpose (fun i j : Fin N =>
          g (b + (i : ℕ)) (a + (j : ℕ))) := by
    funext i j
    exact h_symm (a + (i : ℕ)) (b + (j : ℕ))
  calc
    Matrix.det (fun i j : Fin N => g (a + (i : ℕ)) (b + (j : ℕ))) =
        Matrix.det (Matrix.transpose (fun i j : Fin N =>
          g (b + (i : ℕ)) (a + (j : ℕ)))) := congrArg Matrix.det h_transpose
    _ = Matrix.det (fun i j : Fin N => g (b + (i : ℕ)) (a + (j : ℕ))) :=
      Matrix.det_transpose _

end MathlibPlus.Analysis.ContiguousMinorSymmetry
