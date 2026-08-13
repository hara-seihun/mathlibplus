import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 7355: multiplying the displacement identity on the left and right by
an inverse of `G` gives the displayed inverse displacement identity. -/
theorem inverseDisplacementIdentity_claim7355
    {n : ℕ} {𝕜 : Type*} [CommRing 𝕜]
    (G Z U J : Matrix (Fin n) (Fin n) 𝕜) [Invertible G]
    (h : Z * G - G * Z.transpose = U * J * U.transpose) :
    G⁻¹ * Z - Z.transpose * G⁻¹ =
      G⁻¹ * U * J * U.transpose * G⁻¹ := by
  calc
    G⁻¹ * Z - Z.transpose * G⁻¹ =
        G⁻¹ * (Z * G - G * Z.transpose) * G⁻¹ := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
          simp [Matrix.mul_assoc]
    _ = G⁻¹ * (U * J * U.transpose) * G⁻¹ := by rw [h]
    _ = G⁻¹ * U * J * U.transpose * G⁻¹ := by
      simp only [Matrix.mul_assoc]

end MathlibPlus.LinearAlgebra
