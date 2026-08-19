import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim4899

/-- A symplectic matrix has a symmetric Cayley form.  The inverse is expressed
by the canonical nonsingular matrix inverse, with invertibility of `W + 1`
explicitly retained. -/
theorem symplecticCayleyForm_symmetric_claim4899
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (J W : Matrix ι ι R)
    (hJ : J.transpose = -J)
    (hW : W.transpose * J * W = J)
    (hInv : IsUnit (W + 1).det) :
    (J * (W - 1) * (W + 1)⁻¹).transpose = J * (W - 1) * (W + 1)⁻¹ := by
  let A : Matrix ι ι R := W + 1
  let V : Matrix ι ι R := A⁻¹
  have hInvA : IsUnit A.det := by simpa [A] using hInv
  have hright : A * V = 1 := by
    dsimp [V]
    exact Matrix.mul_nonsing_inv A hInvA
  have hleft : V * A = 1 := by
    dsimp [V]
    exact Matrix.nonsing_inv_mul A hInvA
  have hleftT : V.transpose * A.transpose = 1 := by
    rw [← Matrix.transpose_mul, hright, Matrix.transpose_one]
  have hArel : A.transpose * J * A = A.transpose * J + J * A := by
    dsimp [A]
    calc
      (W + 1).transpose * J * (W + 1) =
          W.transpose * J * W + W.transpose * J + J * W + J := by
            simp [Matrix.transpose_add]
            noncomm_ring
      _ = (W + 1).transpose * J + J * (W + 1) := by
            rw [hW]
            simp [Matrix.transpose_add]
            noncomm_ring
  have hrel : J = J * V + V.transpose * J := by
    calc
      J = 1 * J * 1 := by simp
      _ = (V.transpose * A.transpose) * J * (A * V) := by
        rw [hleftT, hright]
      _ = V.transpose * (A.transpose * J * A) * V := by
        noncomm_ring
      _ = V.transpose * (A.transpose * J + J * A) * V := by rw [hArel]
      _ = (V.transpose * A.transpose) * J * V + V.transpose * J * (A * V) := by
        noncomm_ring
      _ = J * V + V.transpose * J := by rw [hleftT, hright]; simp
  have hM : J * (W - 1) * V = V.transpose * J - J * V := by
    calc
      J * (W - 1) * V = J * (A - 2) * V := by
        dsimp [A]
        congr 1
        noncomm_ring
      _ = J * A * V - 2 * (J * V) := by noncomm_ring
      _ = J - 2 * (J * V) := by
        rw [Matrix.mul_assoc, hright, Matrix.mul_one]
      _ = (J * V + V.transpose * J) - 2 * (J * V) := by
        congr 1
      _ = V.transpose * J - J * V := by noncomm_ring
  change (J * (W - 1) * V).transpose = J * (W - 1) * V
  rw [hM, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    hJ, Matrix.transpose_transpose]
  noncomm_ring

end MathlibPlus.LinearAlgebra.Claim4899
