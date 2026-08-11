import Mathlib

/-!
# Cubic local-factor algebra

The identity from admitted claim 13771 depends only on the displayed values of
`z`, `α`, and `T`.  The prime-power parametrization in the source is therefore
left as the source of these variables rather than assigned a new convention for
complex powers here.
-/

namespace MathlibPlus.Algebra.CubicLocalFactor

/-- The cubic local factor identity, with the nonvanishing of `α` made explicit
because the source uses `α⁻¹`. -/
theorem identity (z α T : ℂ) (hα : α ≠ 0)
    (hT : T = 1 + α + α⁻¹) :
    (1 - z) * (1 - α * z) * (1 - α⁻¹ * z) =
      1 - T * z + T * z ^ 2 - z ^ 3 := by
  rw [hT]
  field_simp [hα]
  ring

end MathlibPlus.Algebra.CubicLocalFactor
