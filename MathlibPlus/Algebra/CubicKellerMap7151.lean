import MathlibPlus.Open.Algebra.NormalizedFactorizationClaim7144

namespace MathlibPlus.Algebra.CubicKellerMap7151

noncomputable section

abbrev Coordinate := MathlibPlus.Open.Algebra.NormalizedFactorizationClaim7144.Coordinate
abbrev TargetCoordinate := MathlibPlus.Open.Algebra.NormalizedFactorizationClaim7144.TargetCoordinate

/-- The literal chart tuple `(a,b,c,d,e)` in the `(a,y,z)` coordinates. -/
def chartCoordinates7151 (a y z : ℂ) : Coordinate :=
  ![a,
    1 + a * y,
    1 - (3 / 2 : ℂ) * a * y + a ^ 2 * z,
    (1 / 2 : ℂ) * y - a * z + (3 / 2 : ℂ) * a * y ^ 2 - a ^ 2 * y * z,
    -2 * z + 4 * y ^ 2 - 4 * a * y * z + 3 * a * y ^ 3 -
      2 * a ^ 2 * y ^ 2 * z]

/-- The displayed three-coordinate polynomial map. -/
def cubicKellerMap7151 (a y z : ℂ) : TargetCoordinate :=
  ![a - (3 / 2 : ℂ) * a ^ 2 * y + a ^ 3 * z,
    (1 / 2 : ℂ) * y - 3 * a * z + 6 * a * y ^ 2 - 6 * a ^ 2 * y * z +
      (9 / 2 : ℂ) * a ^ 2 * y ^ 3 - 3 * a ^ 3 * y ^ 2 * z,
    -2 * z + 4 * y ^ 2 - 6 * a * y * z + 7 * a * y ^ 3 -
      6 * a ^ 2 * y ^ 2 * z + 3 * a ^ 2 * y ^ 4 - 2 * a ^ 3 * y ^ 3 * z]

/-- The explicit chart is a point of the normalized factorization variety and
its normalized multiplication map is exactly the displayed cubic map. -/
def claim7151_explicitCubicKellerMap : Prop :=
  ∀ a y z : ℂ,
    ∃ p : {p : Coordinate //
      p ∈ MathlibPlus.Open.Algebra.NormalizedFactorizationClaim7144.normalizedFactorizationVariety},
      p.1 = chartCoordinates7151 a y z ∧
        MathlibPlus.Open.Algebra.NormalizedFactorizationClaim7144.normalizedFactorizationMap p =
          cubicKellerMap7151 a y z

end

end MathlibPlus.Algebra.CubicKellerMap7151
