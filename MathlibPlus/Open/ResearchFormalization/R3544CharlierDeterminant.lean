import Mathlib
import MathlibPlus.Open.Research.Batch01Analysis

namespace MathlibPlus.Open.ResearchFormalization.R3544

noncomputable section

open MathlibPlus.Open.Research

/-- The polynomial `C_r` formed from the even central Charlier indices,
with the source's positive-rank domain represented by `ℕ+`. -/
def centralCharlierDetPolynomial (r : ℕ+) : Polynomial ℝ :=
  Matrix.det (fun i j : Fin r =>
    iteratedPolynomialDerivative (i : ℕ)
      (centralCharlier (2 * (j : ℕ))))

def shiftedCentralCharlierC14 : Polynomial ℝ :=
  (centralCharlierDetPolynomial (14 : ℕ+)).comp
    (Polynomial.X + Polynomial.C (49 / 2 : ℝ))

def strictlyPositiveCoefficients (p : Polynomial ℝ) : Prop :=
  ∀ i : ℕ, i ≤ p.natDegree → 0 < p.coeff i

/-- Claim 46845: the exact rank-fourteen wall coefficient is negative, so the
shifted determinant is not coefficientwise strictly positive. -/
def claim46845 : Prop :=
  let coefficient := shiftedCentralCharlierC14.coeff 0
  coefficient =
      (-(10899121613412185253683390047794374595183786451959265502910125686863549885776079952150609564149180772600354934063024156905168592576567124877922633204992800195181427222485951022097865402357177734375 : ℝ) /
        (33554432 : ℝ)) ∧
    coefficient < 0 ∧
    ¬ strictlyPositiveCoefficients shiftedCentralCharlierC14

end

end MathlibPlus.Open.ResearchFormalization.R3544
