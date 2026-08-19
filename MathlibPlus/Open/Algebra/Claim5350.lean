import Mathlib

namespace MathlibPlus.Open.Algebra.Claim5350

open scoped BigOperators

noncomputable section

/-- The coefficient predicted by the closed rational Hilbert-series formula. -/
def predictedCoefficient (k : ℕ) : ℕ :=
  (k + 1) * (k + 3)

/-- The three summands in the displayed coefficient decomposition. -/
def decomposedCoefficient (k : ℕ) : ℕ :=
  Nat.choose (k + 2) 2 + Nat.choose (k + 1) 2 + 2 * (k + 1)

/-- The formal power series `(3 - t) / (1 - t)^3`. -/
def candidateHilbertSeries : PowerSeries ℚ :=
  (PowerSeries.C 3 - PowerSeries.X) *
    (PowerSeries.invOneSubPow ℚ 3).val

/-- Claim 5350: every coefficient of the displayed rational series is the
closed formula and has the stated binomial decomposition. -/
def claim5350 : Prop :=
  ∀ k : ℕ,
    PowerSeries.coeff k candidateHilbertSeries =
        (predictedCoefficient k : ℚ) ∧
      predictedCoefficient k = decomposedCoefficient k

end
end MathlibPlus.Open.Algebra.Claim5350
