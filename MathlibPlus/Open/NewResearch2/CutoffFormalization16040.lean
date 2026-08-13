import Mathlib

namespace MathlibPlus.Open.NewResearch2.CutoffFormalization16040

/-- Claim 16040: the literal moving-cutoff parameters and cutoff formula. -/
def claim16040 : Prop :=
  let t : ℝ := 551 / 5000
  let y : ℝ := 7 / 50
  let P : ℕ := 32768
  let N₀ : ℕ := 690988
  (∃ U : ℝ → ℝ, ∀ N : ℝ, U N = N ^ 2 - t / 16) ∧
    y = 7 / 50 ∧ P = 32768 ∧ N₀ = 690988

end MathlibPlus.Open.NewResearch2.CutoffFormalization16040
