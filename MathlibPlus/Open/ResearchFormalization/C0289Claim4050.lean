import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C0289Claim4050

open scoped BigOperators

noncomputable section

/-- The literal weighted prime-power sum through the real cutoff `exp t`. -/
noncomputable def weightedPrimeDiscrepancy (t : ℝ) : ℝ :=
  (Finset.Icc 1 (Nat.floor (Real.exp t))).sum
    (fun (m : ℕ) =>
      if (m : ℝ) ≤ Real.exp t then
        (ArithmeticFunction.vonMangoldt m : ℝ) / (m : ℝ)
      else 0) - t

/-- Claim 4050: after a sufficiently large threshold, the literal
von-Mangoldt discrepancy is centered at `-gamma` with the stated
Vinogradov--Korobov error, with the error function pinned by that equality. -/
def claim4050_weightedPrimeCountingDiscrepancy : Prop :=
  ∃ (C₀ c₀ T₀ : ℝ) (ε : ℝ → ℝ),
    0 < C₀ ∧ 0 < c₀ ∧
      ∀ t : ℝ, T₀ ≤ t →
        weightedPrimeDiscrepancy t =
            -Real.eulerMascheroniConstant + ε t ∧
          |ε t| ≤ C₀ * Real.exp
            (-c₀ * Real.rpow t (3 / 5 : ℝ) /
              Real.rpow (Real.log t) (1 / 5 : ℝ))

end

end MathlibPlus.Open.ResearchFormalization.C0289Claim4050
