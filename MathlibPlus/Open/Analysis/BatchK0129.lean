import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis.ArbitraryFilling

/-- The physical scale appearing in the lifted coordinate. -/
def physicalScale (n : ℕ) : ℝ :=
  Real.log (n : ℝ) / (2 * Real.pi * (n : ℝ))

/-- The lifted coordinate associated with an equilibrium coordinate. -/
def physicalLiftedCoordinate (n : ℕ) (z : ℝ) : ℝ :=
  physicalScale n * z

/-- The derivative identity for the determinant main term. -/
def determinantMainTerm (n : ℕ) (k : ℝ) : ℝ :=
  2 * k *
    (Real.log (Real.log (n : ℝ) / (2 * Real.pi * (n : ℝ))) + 1 +
      Real.log (Real.pi * (n : ℝ) / (4 * k)))

def determinantMainTermDerivative : Prop :=
  ∀ (n : ℕ) (k : ℝ),
    1 < n → 0 < k →
      (1 / 2 : ℝ) *
          deriv (fun x : ℝ => determinantMainTerm n x) k =
        Real.log (Real.log (n : ℝ) / (8 * k))

end MathlibPlus.Open.Analysis.ArbitraryFilling
