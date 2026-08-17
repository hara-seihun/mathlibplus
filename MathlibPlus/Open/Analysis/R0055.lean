import Mathlib

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.R0055

noncomputable section

/-- The finite-prime atomic jump measure, with one atom for each prime power
jump and the displayed coefficient. -/
def claim17543 : Prop :=
  ∀ (P : Finset ℕ),
    (∀ p ∈ P, Nat.Prime p) →
      let νP : Measure ℝ :=
        ∑ p ∈ P, Measure.sum (fun r : {r : ℕ // 0 < r} =>
          (ENNReal.ofReal
              (Real.rpow (p : ℝ) (-((r.1 : ℝ) / 2)) / (r.1 : ℝ))) •
            Measure.dirac ((r.1 : ℝ) * Real.log (p : ℝ)))
      (∀ A : Set ℝ, 0 ≤ νP A) ∧
        Measure.support νP ⊆ Set.Ioi 0

end

end MathlibPlus.Open.Analysis.R0055
