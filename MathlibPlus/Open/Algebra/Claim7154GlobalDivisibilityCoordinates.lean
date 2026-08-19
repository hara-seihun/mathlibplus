import MathlibPlus.Open.Algebra.NormalizedFactorizationClaim7144

namespace MathlibPlus.Open.Algebra.Claim7154

noncomputable section

open MathlibPlus.Open.Algebra.NormalizedFactorizationClaim7144

/-- The first normal coordinate `y=2bd-ae`. -/
def yCoordinate7154 (p : Coordinate) : ℂ :=
  2 * p 1 * p 3 - p 0 * p 4

/-- The corrected second normal coordinate. -/
def zCoordinate7154 (p : Coordinate) : ℂ :=
  2 * p 3 ^ 2 + p 2 * p 4 + 6 * p 1 * p 3 ^ 2 +
    3 * p 1 * p 2 * p 4 - (9 / 2 : ℂ) * p 4

/-- Claim 7154: the two global divisibility identities hold on the exact
normalized factorization variety, with the corrected second coordinate. -/
def claim7154_globalDivisibilityCoordinates : Prop :=
  ∀ p : {p : Coordinate // p ∈ normalizedFactorizationVariety},
    p.1 1 - 1 = p.1 0 * yCoordinate7154 p.1 ∧
      p.1 2 - 1 + (3 / 2 : ℂ) * p.1 0 * yCoordinate7154 p.1 =
        p.1 0 ^ 2 * zCoordinate7154 p.1

end

end MathlibPlus.Open.Algebra.Claim7154
