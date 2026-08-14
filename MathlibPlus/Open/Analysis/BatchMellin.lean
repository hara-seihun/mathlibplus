import Mathlib

namespace MathlibPlus.Open.Analysis.BatchMellin

noncomputable def positiveComplexPower (a : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log a : ℂ))

noncomputable def M (s : ℂ) : ℂ :=
  if s = 0 then
    ((2 * Real.log 2 - Real.log 3 : ℝ) : ℂ)
  else
    ((2 : ℂ) * positiveComplexPower 2 s - positiveComplexPower 3 s - 1) / s

def uniform_reflected_mellin_asymptotic_and_zero_free_cells : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, 3 ≤ m₀ ∧
    (∀ m : ℕ, m₀ ≤ m → Odd m →
      ∀ s : ℂ, ‖s - (m : ℂ)‖ ≤ (1 / 3 : ℝ) →
        ∃ e : ℂ,
          ‖e‖ ≤ C * ((1 / 2 : ℝ) ^ m) ∧
            M (1 - s) = (1 / (s - 1)) * (1 + e)) ∧
    (∀ m : ℕ, m₀ ≤ m → Odd m →
      ∀ s : ℂ, ‖s - (m : ℂ)‖ ≤ (1 / 3 : ℝ) → M (1 - s) ≠ 0)

end MathlibPlus.Open.Analysis.BatchMellin
