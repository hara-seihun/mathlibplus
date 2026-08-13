import Mathlib

namespace MathlibPlus.Algebra.TriangularCoordinate

/-- Claim 40116: after the fibre coordinate change `z = χ(h) x`, the
triangular affine map has the displayed affine form.  The packet leaves
`a(h)` implicit; it is the coefficient induced by that coordinate change. -/
theorem triangularCoordinateChange_claim40116
    {H : Type*} (χ : H → ℝ) (σ : H → H) (lamfun τ : H → ℝ) (h : H) (z : ℝ)
    (hχ : χ h ≠ 0) :
    let a : H → ℝ := fun k => χ (σ k) * lamfun k / χ k
    let d : H → ℝ := fun k => χ (σ k) * τ k
    (χ (σ h) * (lamfun h * (z / χ h) + τ h), σ h) =
      (a h * z + d h, σ h) := by
  dsimp
  congr 1
  field_simp [hχ]

end MathlibPlus.Algebra.TriangularCoordinate
