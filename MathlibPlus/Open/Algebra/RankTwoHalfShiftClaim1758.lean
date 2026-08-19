import Mathlib

namespace MathlibPlus.Open.Algebra

private def coefficientwiseNonnegativeMv
    (p : MvPolynomial (Fin 2) ℚ) : Prop :=
  ∀ m ∈ p.support, 0 ≤ p.coeff m

private def coefficientwiseNonnegativePolynomial
    (p : Polynomial ℚ) : Prop :=
  ∀ n ∈ p.support, 0 ≤ p.coeff n

/-- Claim 1758: the generic rank-two expression has a negative constant
coefficient, whereas the unit-spaced half-shift is the coefficientwise
nonnegative polynomial `2b`. -/
def arithmeticSpecializationEssential_claim1758 : Prop :=
  let x₀ : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 0
  let x₁ : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 1
  let generic : MvPolynomial (Fin 2) ℚ :=
    x₀ + x₁ - MvPolynomial.C 2
  let b : Polynomial ℚ := Polynomial.X
  let shiftedX₀ : Polynomial ℚ := b + Polynomial.C (1 / 2 : ℚ)
  let shiftedX₁ : Polynomial ℚ := b + Polynomial.C (3 / 2 : ℚ)
  let specialized : Polynomial ℚ :=
    shiftedX₀ + shiftedX₁ - Polynomial.C 2
  (¬ coefficientwiseNonnegativeMv generic) ∧
    specialized = 2 * b ∧
      coefficientwiseNonnegativePolynomial specialized

end MathlibPlus.Open.Algebra
