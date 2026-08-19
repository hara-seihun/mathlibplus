import Mathlib

open scoped BigOperators ArithmeticFunction.Moebius
noncomputable section

namespace MathlibPlus.Open.Analysis.Claim13334MobiusField

noncomputable def mobiusPartialSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x),
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)

noncomputable def criticalLogNormalization (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.exp (u / 2) * g (Real.exp u)

/-- Claim 13334: the positive-index real Mobius partial-sum field and its
critical logarithmic normalization. -/
def claim13334_mobiusPartialSumField
    (g q : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, g x = mobiusPartialSum x) ∧
    (∀ u : ℝ, q u = criticalLogNormalization g u)

end MathlibPlus.Open.Analysis.Claim13334MobiusField
