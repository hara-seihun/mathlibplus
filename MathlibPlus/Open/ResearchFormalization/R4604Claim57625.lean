import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4604Claim57625

/-- Claim 57625: the two explicit monic quadratic products agree in their top
 two coefficients but differ in the constant coefficient, and the same remains
 true after multiplication by the common centroid factor X. -/
def topCoefficientTruncationNoninjective_claim57625 : Prop :=
  let P₁ : Polynomial ℤ :=
    (Polynomial.X + 1) * (Polynomial.X + 4)
  let P₂ : Polynomial ℤ :=
    (Polynomial.X + 2) * (Polynomial.X + 3)
  let XP₁ : Polynomial ℤ := Polynomial.X * P₁
  let XP₂ : Polynomial ℤ := Polynomial.X * P₂
  P₁ = Polynomial.X ^ 2 + 5 * Polynomial.X + 4 ∧
    P₂ = Polynomial.X ^ 2 + 5 * Polynomial.X + 6 ∧
    P₁.Monic ∧
    P₂.Monic ∧
    P₁.natDegree = 2 ∧
    P₂.natDegree = 2 ∧
    P₁.coeff 1 = 5 ∧
    P₂.coeff 1 = 5 ∧
    P₁.coeff 0 = 4 ∧
    P₂.coeff 0 = 6 ∧
    P₁ ≠ P₂ ∧
    XP₁ = Polynomial.X ^ 3 + 5 * Polynomial.X ^ 2 + 4 * Polynomial.X ∧
    XP₂ = Polynomial.X ^ 3 + 5 * Polynomial.X ^ 2 + 6 * Polynomial.X ∧
    XP₁.coeff 2 = XP₂.coeff 2 ∧
    XP₁.coeff 1 ≠ XP₂.coeff 1

end MathlibPlus.Open.ResearchFormalization.R4604Claim57625
