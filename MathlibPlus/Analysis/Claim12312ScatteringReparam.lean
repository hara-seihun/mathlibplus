import Mathlib

namespace MathlibPlus.Analysis.Claim12312

/-- The substitution `u=(s+1)/2` in claim 12312 sends the displayed
completed-scattering quotient to `Λζ(s)/Λζ(s+1)`. -/
theorem reparameterizedScatteringCoefficient_claim12312
    (Lambda : ℂ → ℂ) (s : ℂ) :
    let phi : ℂ → ℂ := fun u =>
      Lambda (2 * u - 1) / Lambda (2 * u)
    phi ((s + 1) / 2) = Lambda s / Lambda (s + 1) := by
  dsimp
  have hnum : 2 * ((s + 1) / 2) - 1 = s := by ring
  have hden : 2 * ((s + 1) / 2) = s + 1 := by ring
  rw [hnum, hden]

end MathlibPlus.Analysis.Claim12312
