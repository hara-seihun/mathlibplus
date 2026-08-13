import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim57915

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- The quadratic midpoint residue of a symmetric positive-semidefinite bilinear form. -/
theorem psdQuadraticMidpointResidue
    (Q : V →ₗ[ℝ] (V →ₗ[ℝ] ℝ))
    (hQsymm : ∀ x y : V, Q x y = Q y x)
    (_hQpsd : ∀ x : V, 0 ≤ Q x x)
    (ρA ρB ρC : V)
    (hrel : ρA - (2 : ℝ) • ρB + ρC = 0) :
    Q ρA ρA - 2 * Q ρB ρB + Q ρC ρC =
      2 * Q (ρA - ρB) (ρA - ρB) := by
  have hC : ρC = (2 : ℝ) • ρB - ρA := by
    apply eq_of_sub_eq_zero
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hrel
  rw [hC]
  simp [sub_eq_add_neg]
  rw [hQsymm ρA ρB]
  ring

end MathlibPlus.LinearAlgebra.Claim57915
