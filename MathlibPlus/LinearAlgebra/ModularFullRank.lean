import Mathlib

namespace MathlibPlus.LinearAlgebra

/--
Claim 20258: a nonzero determinant modulo the fixed prime certifies that an
integer square minor has nonzero determinant over both `ℤ` and `ℚ`, and hence
that its selected columns are linearly independent over `ℚ`.  The selected
minor is exposed as the matrix `A` because the source does not provide a larger
ambient matrix or a column-selection map.
-/
theorem modularMinorCertificate
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hmod : (A.det : ZMod 1000003) ≠ 0) :
    A.det ≠ 0 ∧
      (A.det : ℚ) ≠ 0 ∧
        LinearIndependent ℚ ((A.map (fun x : ℤ => (x : ℚ))).col) := by
  have hdet : A.det ≠ 0 := by
    intro hzero
    apply hmod
    rw [hzero]
    simp
  have hdetQ : (A.map (fun x : ℤ => (x : ℚ))).det ≠ 0 := by
    rw [← Int.cast_det A]
    exact_mod_cast hdet
  exact ⟨hdet, by exact_mod_cast hdet,
    Matrix.linearIndependent_cols_of_det_ne_zero hdetQ⟩

end MathlibPlus.LinearAlgebra
