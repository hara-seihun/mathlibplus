import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0855Claim29610

open MvPolynomial

/-- Claim 29610: the explicit rational-polynomial cross-ratio identity and
its non-affine coefficient-vector witness are retained before specialization.
The first point is zero, so affine collinearity is stated as scalar
proportionality of the other two points. -/
def crossRatioAndNonCollinearity_claim29610 : Prop :=
  let p : MvPolynomial (Fin 2) ℚ := X 0
  let q : MvPolynomial (Fin 2) ℚ := X 1
  let a : MvPolynomial (Fin 2) ℚ := 0
  let b : MvPolynomial (Fin 2) ℚ := p * (p + q)
  let c : MvPolynomial (Fin 2) ℚ := q * (p + q)
  let d : MvPolynomial (Fin 2) ℚ := 2 * p * q
  (a - d) * (b - c) = 2 * (a - c) * (b - d) ∧
    (∀ r s : ℚ, r • b + s • c = 0 → r = 0 ∧ s = 0) ∧
    ¬ ∃ r : ℚ, b = r • c

end MathlibPlus.Open.ResearchFormalization.R0855Claim29610
