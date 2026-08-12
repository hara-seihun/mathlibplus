import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace MathlibPlus.LinearAlgebra.RelativeVandermondePerturbation

/-- The relative perturbation identity from claim 18082. -/
theorem relativeVandermondePerturbation_claim18082
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (y : ι → R) (j : ι → ℕ) (P : ℕ → R → R)
    (hV : IsUnit (Matrix.det (fun i k : ι => (y i) ^ (2 * j k)))) :
    let V : Matrix ι ι R := fun i k => (y i) ^ (2 * j k)
    let E : Matrix ι ι R := fun i k => P (j k) (y i)
    let B : Matrix ι ι R := V⁻¹ * (E - V)
    E = V * (1 + B) := by
  dsimp
  let V : Matrix ι ι R := fun i k => (y i) ^ (2 * j k)
  let E : Matrix ι ι R := fun i k => P (j k) (y i)
  have hV' : IsUnit V.det := by simpa [V] using hV
  change E = V * (1 + V⁻¹ * (E - V))
  rw [Matrix.mul_add]
  simp only [Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv V hV']
  simp

end MathlibPlus.LinearAlgebra.RelativeVandermondePerturbation
