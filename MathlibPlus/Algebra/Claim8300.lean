import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim8300

/-- The numerator subtraction in claim 8300 is an exact polynomial identity. -/
theorem localCancellation_claim8300 {R : Type*} [CommRing R]
    (α ρ z : R) :
    (1 - α + α * z - ρ * z) * (1 - α * z) -
        (1 - α) * (1 - ρ * z) =
      α * z * (1 - z) * (α - ρ) := by
  ring

/-- Under the displayed nonvanishing hypotheses, the local factor has the
stated correction form.  The source-specific Euler parameters are not
reconstructed here; the algebraic identity is retained over any field. -/
theorem localFactor_formula_claim8300 {K : Type*} [Field K]
    (α ρ z : K) (hα : 1 - α ≠ 0) (hρ : 1 - ρ * z ≠ 0) :
    (1 - α + α * z - ρ * z) * (1 - α * z) /
        ((1 - α) * (1 - ρ * z)) =
      1 + α * z * (1 - z) * (α - ρ) /
        ((1 - α) * (1 - ρ * z)) := by
  have hden : (1 - α) * (1 - ρ * z) ≠ 0 := mul_ne_zero hα hρ
  have hnum :
      (1 - α + α * z - ρ * z) * (1 - α * z) =
        (1 - α) * (1 - ρ * z) + α * z * (1 - z) * (α - ρ) := by
    ring
  rw [hnum, add_div, div_self hden]

end MathlibPlus.Algebra.Claim8300
