import Mathlib

namespace MathlibPlus.Open.Analysis.SuperheatCutoff

open Set

noncomputable section

/-- Claim 13045: the two explicitly extended quotient cutoffs are endpoint-flat
Gevrey cutoffs of order 5/4. -/
def claim13045 : Prop :=
  ∀ j : ℕ, (j = 1 ∨ j = 3) →
    let ρ : ℝ → ℝ := fun t =>
      Real.exp (-((t - 1 / 2) ^ 4)⁻¹) /
        (Real.exp (-((t - 1 / 2) ^ 4)⁻¹) +
          Real.exp (-(j : ℝ) * ((1 - t) ^ 4)⁻¹))
    let χ : ℝ → ℝ := fun t =>
      if t ≤ 1 / 2 then 1 else if t < 1 then 1 - ρ t else 0
    χ (1 / 2) = 1 ∧ χ 1 = 0 ∧
      (∀ n : ℕ, 0 < n →
        iteratedDeriv n χ (1 / 2) = 0 ∧
          iteratedDeriv n χ 1 = 0) ∧
      ContDiff ℝ ⊤ χ ∧
      (∃ C A : ℝ, 0 < C ∧ 0 < A ∧
        ∀ n : ℕ, ∀ t : ℝ, t ∈ Set.Icc (1 / 2) 1 →
          ‖iteratedDeriv n χ t‖ ≤
            C * A ^ n *
              Real.rpow (Nat.factorial n : ℝ) (5 / 4 : ℝ))

end

end MathlibPlus.Open.Analysis.SuperheatCutoff
