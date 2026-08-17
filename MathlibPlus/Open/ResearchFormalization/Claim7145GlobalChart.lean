import MathlibPlus.Open.Algebra.NormalizedFactorizationClaim7144

namespace MathlibPlus.Open.ResearchFormalization.Claim7145

noncomputable section

open MathlibPlus.Open.Algebra.NormalizedFactorizationClaim7144

/-- The displayed three-variable coordinate formula. -/
def chartCoordinates (a y z : ℂ) : Coordinate :=
  ![a,
    1 + a * y,
    1 - (3 / 2 : ℂ) * a * y + a ^ 2 * z,
    (1 / 2 : ℂ) * y - a * z + (3 / 2 : ℂ) * a * y ^ 2 -
      a ^ 2 * y * z,
    -2 * z + 4 * y ^ 2 - 4 * a * y * z + 3 * a * y ^ 3 -
      2 * a ^ 2 * y ^ 2 * z]

/-- Claim 7145: the displayed polynomial chart is a global map into the
reviewed normalized factorization variety. -/
def claim7145_globalPolynomialChart : Prop :=
  ∃ φ : ℂ → ℂ → ℂ →
      {p : Coordinate // p ∈ normalizedFactorizationVariety},
    ∀ a y z, (φ a y z).1 = chartCoordinates a y z

end

end MathlibPlus.Open.ResearchFormalization.Claim7145
