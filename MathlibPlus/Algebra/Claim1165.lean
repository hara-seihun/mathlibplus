import Mathlib

namespace MathlibPlus.Algebra

noncomputable section

/-- The rational polynomial `q(b)=b^2-b+1` from Claim 1165. -/
def pointwiseQuadratic1165 : Polynomial ℚ :=
  Polynomial.X ^ 2 - Polynomial.X + 1

/-- The visible center factor `2b+d+1`, represented as a polynomial. -/
def visibleCenterFactor1165 (d : ℕ) : Polynomial ℚ :=
  2 * Polynomial.X + (d : Polynomial ℚ) + 1

/-- The factored polynomial `\widetilde P_d`. -/
def pointwiseFactoredPolynomial1165 (d : ℕ) : Polynomial ℚ :=
  visibleCenterFactor1165 d * pointwiseQuadratic1165

/-- Coefficientwise nonnegativity for the exact polynomial carrier. -/
def coefficientwiseNonnegative1165 (p : Polynomial ℚ) : Prop :=
  ∀ n : ℕ, 0 ≤ p.coeff n

/-- Claim 1165: the displayed positive quadratic, its positive visible-factor
family, and the two explicit negative coefficient witnesses. -/
def pointwisePositivityNotCoefficientwise : Prop :=
  (∀ b : ℝ,
    b ^ 2 - b + 1 = ((2 * b - 1) ^ 2 + 3) / 4) ∧
    (∀ b : ℝ, 0 < b ^ 2 - b + 1) ∧
    (∀ d : ℕ, ∀ b : ℝ, 0 ≤ b →
      0 < (2 * b + (d : ℝ) + 1) * (b ^ 2 - b + 1)) ∧
    (∀ d : ℕ,
      visibleCenterFactor1165 d ∣ pointwiseFactoredPolynomial1165 d) ∧
    pointwiseQuadratic1165.coeff 1 = (-1 : ℚ) ∧
    ¬ coefficientwiseNonnegative1165 pointwiseQuadratic1165 ∧
    (2 * Polynomial.X * pointwiseQuadratic1165).coeff 2 = (-2 : ℚ) ∧
    (2 * Polynomial.X * pointwiseQuadratic1165 : Polynomial ℚ) =
      2 * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X ∧
    ¬ coefficientwiseNonnegative1165
      (2 * Polynomial.X * pointwiseQuadratic1165)

end

end MathlibPlus.Algebra
