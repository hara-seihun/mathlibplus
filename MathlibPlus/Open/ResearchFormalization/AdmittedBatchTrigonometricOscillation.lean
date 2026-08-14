import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.TrigonometricOscillation

noncomputable def trigonometricSequence (θ : ℝ) (C : ℂ) (n : ℕ) : ℝ :=
  2 * (C * Complex.exp (-((n : ℂ) * (θ : ℂ) * Complex.I))).re

def nonzeroFrequencyChangesSign : Prop :=
  ∀ (θ : ℝ) (C : ℂ),
    0 < θ → θ < Real.pi → C ≠ 0 →
      ∃ ε : ℝ, 0 < ε ∧
        (∀ N : ℕ, ∃ n : ℕ,
          N ≤ n ∧ ε ≤ trigonometricSequence θ C n) ∧
        (∀ N : ℕ, ∃ n : ℕ,
          N ≤ n ∧ trigonometricSequence θ C n ≤ -ε)

end MathlibPlus.Open.ResearchFormalization.TrigonometricOscillation
