import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch01_01a001be

namespace MathlibPlus.Open.Algebra.NormalizedFactorizationClaim7144

noncomputable section

abbrev Coordinate := Fin 5 → ℂ
abbrev CubicCoordinate := Fin 4 → ℂ
abbrev TargetCoordinate := Fin 3 → ℂ

/-- The resultant polynomial on the five coefficient coordinates. -/
def rho (p : Coordinate) : ℂ :=
  p 0 ^ 2 * p 4 - p 0 * p 1 * p 3 + p 2 * p 1 ^ 2

/-- The complex affine-five point carrier of the normalized factorization variety. -/
def normalizedFactorizationVariety : Set Coordinate :=
  {p |
    p 0 * p 3 + p 1 * p 2 = 1 ∧
      rho p = 1}

/-- The coefficient multiplication map with the marked linear and quadratic factors. -/
def normalizedFactorizationMap :
    {p : Coordinate // p ∈ normalizedFactorizationVariety} → TargetCoordinate :=
  fun p => ![p.1 0 * p.1 2,
    p.1 0 * p.1 4 + p.1 1 * p.1 3,
    p.1 1 * p.1 4]

/-- The four homogeneous binary-cubic coefficients of the product. -/
def binaryCubicCoefficientMap (p : Coordinate) : CubicCoordinate :=
  ![p 0 * p 2,
    p 0 * p 3 + p 1 * p 2,
    p 0 * p 4 + p 1 * p 3,
    p 1 * p 4]

/-- The dehomogenized cubic represented by the target coordinates after the
normalized `T^2 S` coefficient has been inserted. -/
def normalizedCubic (q : TargetCoordinate) : Polynomial ℂ :=
  Polynomial.C (q 0) * Polynomial.X ^ 3 +
    Polynomial.C 1 * Polynomial.X ^ 2 +
    Polynomial.C (q 1) * Polynomial.X + Polynomial.C (q 2)

/-- Claim 7144: the displayed affine-five locus and three-coordinate map are
exactly the normalized binary-cubic factorization carrier. -/
def normalizedFactorizationVarietyAndMapClaim7144 : Prop :=
  ∀ p : {p : Coordinate // p ∈ normalizedFactorizationVariety},
    binaryCubicCoefficientMap p.1 =
        ![(normalizedFactorizationMap p) 0, 1,
          (normalizedFactorizationMap p) 1,
          (normalizedFactorizationMap p) 2] ∧
      MathlibPlus.Open.ResearchFormalizationBatch.Claim7149.coefficientProduct
          (p.1 0) (p.1 1) (p.1 2) (p.1 3) (p.1 4) =
        normalizedCubic (normalizedFactorizationMap p) ∧
      Polynomial.resultant
          (MathlibPlus.Open.ResearchFormalizationBatch.Claim7149.linearForm
            (p.1 0) (p.1 1))
          (MathlibPlus.Open.ResearchFormalizationBatch.Claim7149.quadraticForm
            (p.1 2) (p.1 3) (p.1 4))
          1 2 = 1

end

end MathlibPlus.Open.Algebra.NormalizedFactorizationClaim7144
