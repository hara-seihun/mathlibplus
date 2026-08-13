import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

/-- The exact residual-degree profile claimed for the stacked `(U₁₀₂,H_NCD)`
map and the corresponding `U₁₀₂` tail.  The actual matrix carriers and the
finite-field nullity computation are intentionally parameters of the eventual
faithful instantiation, not silently invented here. -/
def hiddenCornerJointNullityProfile_claim39579
    (stackedNullity : Fin 7 → ℕ) (u102Nullity : Fin 3 → ℕ) : Prop :=
  stackedNullity = ![1, 0, 1, 1, 1, 1, 2] ∧
    u102Nullity = ![19, 45, 91]

end MathlibPlus.Open.LinearAlgebra
