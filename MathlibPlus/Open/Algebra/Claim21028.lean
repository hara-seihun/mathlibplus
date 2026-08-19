import Mathlib

namespace MathlibPlus.Open.Algebra.R0406

/-- Claim 21028: the exact scalar equality-layer balance with all centered
coordinates retained. -/
def scalarEqualityLayerBalances_claim21028
    {R : Type*} [CommRing R]
    (t N b₁₂ b₁₃ b₂₃ c d a₁ a₂ a₃
      u₁₂ u₁₃ u₂₃ e : R) : Prop :=
  t = 2 * N + 6 ∧
    b₁₂ = 3 + u₁₂ ∧
    b₁₃ = 3 + u₁₃ ∧
    b₂₃ = 3 + u₂₃ ∧
    c = N - 2 + e ∧
    d = u₁₂ + u₁₃ + u₂₃ + 2 * e ∧
    a₁ = N + 2 - u₁₂ - u₁₃ - e ∧
    a₂ = N + 2 - u₁₂ - u₂₃ - e ∧
    a₃ = N + 2 - u₁₃ - u₂₃ - e

end MathlibPlus.Open.Algebra.R0406
