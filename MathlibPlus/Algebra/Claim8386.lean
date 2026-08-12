import Mathlib

/-!
# Regular local-factor correction

The source's prime-power parametrization supplies the three complex values `α`,
`ρ`, and `z`.  The displayed local-factor identities are algebraic once those
values are fixed; the second identity requires the denominator to be nonzero.
-/

namespace MathlibPlus.Algebra.RegularLocalFactor

/-- Exact algebraic correction for the regular local factor in admitted claim
8386 (K-0088). -/
theorem correction (α ρ z : ℂ) (hden : (1 - α) * (1 - ρ * z) ≠ 0) :
    let A := 1 - α + α * z - ρ * z
    let H := A * (1 - α * z) / ((1 - α) * (1 - ρ * z))
    (A * (1 - α * z) - (1 - α) * (1 - ρ * z) =
        α * z * (1 - z) * (α - ρ)) ∧
      H = 1 + α * z * (1 - z) * (α - ρ) / ((1 - α) * (1 - ρ * z)) := by
  dsimp
  constructor
  · ring
  · apply (div_eq_iff hden).2
    calc
      (1 - α + α * z - ρ * z) * (1 - α * z) =
          (1 - α) * (1 - ρ * z) + α * z * (1 - z) * (α - ρ) := by ring
      _ = (1 + α * z * (1 - z) * (α - ρ) /
          ((1 - α) * (1 - ρ * z))) * ((1 - α) * (1 - ρ * z)) := by
        rw [add_mul, div_mul_cancel₀ _ hden]
        simp

end MathlibPlus.Algebra.RegularLocalFactor
