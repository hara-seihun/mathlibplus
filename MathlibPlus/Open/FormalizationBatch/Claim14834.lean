import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.Claim14834

open scoped BigOperators

noncomputable section

/-- The finite reciprocal-zero product with the exact carrier used by the
centered factorial-scaled Toeplitz minor. -/
def reciprocalZeroPolynomial (x : Fin 13 → ℚ) : Polynomial ℚ :=
  ∏ i : Fin 13, (Polynomial.C 1 + Polynomial.C (x i) * Polynomial.X)

/-- The factorial-scaled coefficient attached to a reciprocal-zero product. -/
def factorialScaledCoefficient (p : Polynomial ℚ) (k : ℕ) : ℚ :=
  (Nat.factorial k : ℚ) * p.coeff k

/-- The order-four centered minor at the first structurally interior shift. -/
def centeredOrderFourDeterminant (x : Fin 13 → ℚ) : ℚ :=
  Matrix.det (fun i j : Fin 4 =>
    factorialScaledCoefficient (reciprocalZeroPolynomial x)
      (3 + (j : ℕ) - (i : ℕ)))

/-- Power sums of the reciprocal-zero tuple. -/
def reciprocalPowerSum (x : Fin 13 → ℚ) (k : ℕ) : ℚ :=
  ∑ i : Fin 13, (x i) ^ k

/-- The homogeneous reciprocal-zero power-sum polynomial normalized in the
source by `D₄ = 12 P`. -/
def homogeneousPowerSum (x : Fin 13 → ℚ) : ℚ :=
  let q₂ := reciprocalPowerSum x 2
  let q₃ := reciprocalPowerSum x 3
  let q₄ := reciprocalPowerSum x 4
  let q₅ := reciprocalPowerSum x 5
  let q₆ := reciprocalPowerSum x 6
  q₂ ^ 6 - 12 * q₂ ^ 4 * q₄ + 8 * q₂ ^ 3 * q₃ ^ 2 +
    20 * q₂ ^ 3 * q₆ - 48 * q₂ ^ 2 * q₃ * q₅ +
    21 * q₂ ^ 2 * q₄ ^ 2 + 24 * q₂ * q₃ ^ 2 * q₄ -
    60 * q₂ * q₄ * q₆ + 48 * q₂ * q₅ ^ 2 -
    12 * q₃ ^ 4 + 40 * q₃ ^ 2 * q₆ -
    48 * q₃ * q₄ * q₅ + 18 * q₄ ^ 3

/-- The parenthesis in the reciprocal-scale specialization. -/
def reciprocalScaleParenthesis (t : ℚ) : ℚ :=
  9075 * t ^ 8 + 9900 * t ^ 6 + 2640 * t ^ 5 +
    3410 * t ^ 4 + 880 * t ^ 3 + 300 * t ^ 2 + 160 * t - 1

/-- Two reciprocal zeros equal to one and eleven equal to `t`. -/
def twoUnitElevenScale (t : ℚ) : Fin 13 → ℚ :=
  fun i => if (i : ℕ) < 2 then 1 else t

/-- The normalized witness with reciprocal zeros `162,162,1,...,1`. -/
def witnessReciprocalZeros : Fin 13 → ℚ :=
  fun i => if (i : ℕ) < 2 then 162 else 1

/-- Claim 14834: the reciprocal-scale parenthesis is negative at `1/162`,
the homogeneous power sum takes the exact witness value, and the centered
order-four determinant is twelve times that power sum. -/
def claim14834 : Prop :=
  reciprocalScaleParenthesis (1 / 162) < 0 ∧
    homogeneousPowerSum witnessReciprocalZeros = -43990822437711732 ∧
    centeredOrderFourDeterminant witnessReciprocalZeros =
      12 * homogeneousPowerSum witnessReciprocalZeros ∧
    centeredOrderFourDeterminant witnessReciprocalZeros =
      -527889869252540784

end

end MathlibPlus.Open.FormalizationBatch.Claim14834
