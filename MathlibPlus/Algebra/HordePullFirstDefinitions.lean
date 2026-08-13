import MathlibPlus.Basic

open BigOperators
open MeasureTheory
open scoped BigOperators
noncomputable section

namespace MathlibPlus.Algebra.HordePullFirstDefinitions

/-- Claim 14122: the generalized Laguerre polynomial written in the packet's
coefficient convention. -/
def generalizedLaguerreSquared (d : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (d + 1),
    Polynomial.C
        (((-1 : ℚ) ^ k) * (Nat.choose (d + 2) (d - k) : ℚ) /
          (Nat.factorial k : ℚ)) * Polynomial.X ^ k

/-- The leading coefficient of the displayed generalized Laguerre expansion. -/
theorem generalizedLaguerreSquared_leadingCoefficient (d : ℕ) :
    (generalizedLaguerreSquared d).coeff d =
      ((-1 : ℚ) ^ d) * (Nat.choose (d + 2) (d - d) : ℚ) /
        (Nat.factorial d : ℚ) := by
  classical
  simp [generalizedLaguerreSquared]

/-- Claim 39330: the arm polynomial in the connected-subtree spider formula. -/
def spiderArmPolynomial (a : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (a + 1),
    Polynomial.C (a - k + 1 : ℤ) * Polynomial.X ^ k

/-- Claim 39330: the geometric-series factor for an arm. -/
def spiderArmSeries (a : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (a + 1), Polynomial.X ^ k

/-- Claim 39330: the connected-subtree size polynomial of the four-arm spider. -/
def fourArmSpiderConnectedSubtreePolynomial (A : Fin 4 → ℕ) : Polynomial ℤ :=
  (∑ i : Fin 4, spiderArmPolynomial (A i)) +
    Polynomial.X * ∏ i : Fin 4, spiderArmSeries (A i)

/-- Claim 19413: cell-averaging the `j`th kernel polynomial over the `n`th cell. -/
def cellAveragedKernel
    {ι α : Type*} [MeasurableSpace α]
    (cells : ι → Set α) (measures : ι → Measure α)
    (kernels : ι → α → ℝ) (n j : ι) : ℝ :=
  ∫ y, kernels j y ∂(measures n).restrict (cells n)

end MathlibPlus.Algebra.HordePullFirstDefinitions
