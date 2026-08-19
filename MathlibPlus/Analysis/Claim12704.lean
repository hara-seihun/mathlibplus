import Mathlib

namespace MathlibPlus.Analysis.Claim12704

open scoped Topology
open Filter

noncomputable section

/-- The positive-integer arithmetic state count in claim 12704. -/
def arithmeticStateCount_claim12704 : Prop :=
  let PositiveNat := {n : ℕ // 0 < n}
  let N_ar : ℝ → ℕ := fun E =>
    Set.ncard {n : PositiveNat | Real.log (n.1 : ℝ) ≤ E}
  ∀ E : ℝ, N_ar E = ⌊Real.exp E⌋₊

/-- The consecutive positive-integer logarithmic gaps in claim 12704. -/
def shrinkingLogGaps_claim12704 : Prop :=
  let PositiveNat := {n : ℕ // 0 < n}
  Filter.Tendsto
    (fun n : PositiveNat =>
      Real.log ((n.1 + 1 : ℕ) : ℝ) - Real.log (n.1 : ℝ))
    atTop (𝓝 0)

/-- The complete conjunction of the exact count and shrinking-gap assertions
in claim 12704. -/
def exactArithmeticStateCountAndShrinkingGaps_claim12704 : Prop :=
  arithmeticStateCount_claim12704 ∧ shrinkingLogGaps_claim12704

end

end MathlibPlus.Analysis.Claim12704
