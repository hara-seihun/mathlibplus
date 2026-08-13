import Mathlib

namespace MathlibPlus.Analysis.Claim7317

/-- The oriented confluent Hankel minor, with the empty minor normalized to one
by the determinant convention. -/
noncomputable def orientedConfluentHankelMinor_claim7317
    (F : ℝ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m * (m - 1) / 2) *
    Matrix.det (fun i j : Fin m => iteratedDeriv (i + j) F t)

@[simp] theorem orientedConfluentHankelMinor_zero_claim7317
    (F : ℝ → ℝ) (t : ℝ) :
    orientedConfluentHankelMinor_claim7317 F 0 t = 1 := by
  unfold orientedConfluentHankelMinor_claim7317
  have hdet : Matrix.det
      (fun i j : Fin 0 => iteratedDeriv (i + j) F t) = (1 : ℝ) := by
    exact Matrix.det_fin_zero
  rw [hdet]
  norm_num

end MathlibPlus.Analysis.Claim7317
