import Mathlib

namespace MathlibPlus.Open.Analysis.NR2

noncomputable section
open Classical
open scoped BigOperators

/-- The exact Chebyshev-weighted discrepancy appearing in claim 4050.  The
finite range is written with the exact cutoff `m ≤ exp t`. -/
noncomputable def weightedPrimeDiscrepancy (t : ℝ) : ℝ :=
  (Finset.Icc 1 (Nat.floor (Real.exp t))).sum
    (fun (m : ℕ) => if (m : ℝ) ≤ Real.exp t then
      (ArithmeticFunction.vonMangoldt m : ℝ) / (m : ℝ) else 0) - t

def claim4050_weightedPrimeCountingDiscrepancy : Prop :=
  ∃ (C₀ c₀ T₀ : ℝ) (ε : ℝ → ℝ),
    0 < C₀ ∧ 0 < c₀ ∧
      ∀ t : ℝ, T₀ ≤ t →
        weightedPrimeDiscrepancy t = -Real.eulerMascheroniConstant + ε t ∧
          |ε t| ≤ C₀ * Real.exp
            (-c₀ * (Real.rpow t (3 / 5 : ℝ)) /
              Real.rpow (Real.log t) (1 / 5 : ℝ))

end
end MathlibPlus.Open.Analysis.NR2
