import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0832Claim27109

noncomputable section

private def eulerDeriv (P : Polynomial ℚ) : Polynomial ℚ :=
  Polynomial.X * P.derivative

private def eulerPower : ℕ → Polynomial ℚ → Polynomial ℚ
  | 0, P => P
  | j + 1, P => eulerPower j (eulerDeriv P)

private def polynomialOperator (P Q : Polynomial ℚ) : Polynomial ℚ :=
  ∑ j ∈ P.support, P.coeff j • eulerPower j Q

private def lambdaMoment (M r s : ℕ) (P : Polynomial ℚ) : ℚ :=
  Polynomial.eval 1
    (polynomialOperator P
      (Polynomial.X ^ r * (1 - Polynomial.X) ^ s *
        (1 + Polynomial.X) ^ (M - 2 * r - s)))

private def fallingFactorialPolynomial (j : ℕ) : Polynomial ℚ :=
  ∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℚ))

private def wedgeParameters (n r : ℕ) : Prop :=
  r + 3 ≤ n ∧ n ≤ 2 * r ∧ 2 * n ≥ 3 * r + 4

private def wedgeM (n : ℕ) : ℕ := Nat.choose n 2
private def wedgeEll (n r : ℕ) : ℕ := n - r - 2
private def wedgeQ (n r : ℕ) : ℕ := 2 * r - n + 2

private def degreeAtMost (P : Polynomial ℚ) (ell : ℕ) : Prop :=
  ∀ d, d ∈ P.support → d < ell

private def binomialTest (N r : ℕ) (P Q : Polynomial ℚ) : ℚ :=
  ∑ j ∈ Finset.range N,
    (Nat.choose (N - 1) j : ℚ) *
      Polynomial.eval (r + j : ℚ) P * Polynomial.eval (r + j : ℚ) Q

/-- Claim 27109: in the exact three-halves-wedge degree range, the falling-
    factorial moment rows have the displayed triangular values and nonzero
    diagonal. -/
def triangularFallingFactorialMoments_claim27109 : Prop :=
  ∀ n r : ℕ, wedgeParameters n r →
    let M := wedgeM n
    let ell := wedgeEll n r
    (∀ s : ℕ, s < ell → ∀ j : ℕ, j < ell →
      (j < s →
        lambdaMoment M r s (fallingFactorialPolynomial j) = 0) ∧
      (s ≤ j →
        lambdaMoment M r s (fallingFactorialPolynomial j) =
          (j.factorial : ℚ) * (-1 : ℚ) ^ s *
            ((1 + Polynomial.X) ^ r *
              (2 + Polynomial.X) ^ (M - 2 * r - s)).coeff (j - s)) ∧
      lambdaMoment M r s (fallingFactorialPolynomial s) ≠ 0)


end

end MathlibPlus.Open.ResearchFormalization.R0832Claim27109
