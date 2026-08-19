import Mathlib

namespace MathlibPlus.Open.Algebra

/-- Claim 25124: for the exact specialized quotient carrier, nonzero factors
have additive x₁-degree, and a zero x₁-derivative forces both factors to be
x₁-free. -/
def characteristicZeroDegreeConsequence_claim25124 : Prop :=
  ∀ (rhoQ rhoR : MvPolynomial (Option ℕ) ℤ),
    rhoQ ≠ 0 →
    rhoR ≠ 0 →
      MvPolynomial.degreeOf (some 1) (rhoQ * rhoR) =
          MvPolynomial.degreeOf (some 1) rhoQ +
            MvPolynomial.degreeOf (some 1) rhoR ∧
        (MvPolynomial.pderiv (R := ℤ) (σ := Option ℕ) (some 1)
            (rhoQ * rhoR) = 0 →
          MvPolynomial.degreeOf (some 1) (rhoQ * rhoR) = 0 ∧
            MvPolynomial.degreeOf (some 1) rhoQ = 0 ∧
              MvPolynomial.degreeOf (some 1) rhoR = 0)

end MathlibPlus.Open.Algebra
