import Mathlib

namespace MathlibPlus.Open.Analysis.CompletedTheta

noncomputable section

open MeasureTheory Set

/-- Claim 368: for every retained shell and moment order, the tail beyond
`u = 4` obeys the displayed incomplete-gamma majorant. -/
def retainedShellIntegrationTailBound : Prop :=
  ∀ (n k : ℕ), 1 ≤ n → n ≤ 4 →
    let shell : ℝ → ℝ := fun u ↦
      2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) *
        (2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u) - 3) *
        Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
    let α : ℝ := Real.pi * (n : ℝ) ^ 2 * Real.exp 8
    let lambda : ℝ := 2 * α - 9 / 2
    IntegrableOn (fun u : ℝ ↦ u ^ k * shell u) (Set.Ici 4) ∧
      2 * ∫ u : ℝ in Set.Ici 4, u ^ k * shell u ≤
        8 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (18 - α) *
          ∑ r ∈ Finset.range (k + 1),
            (Nat.choose k r : ℝ) * 4 ^ (k - r) * Nat.factorial r /
              lambda ^ (r + 1)

end

end MathlibPlus.Open.Analysis.CompletedTheta
