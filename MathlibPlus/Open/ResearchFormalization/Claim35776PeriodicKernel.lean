import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim35776

open scoped BigOperators

noncomputable section

/-- The period-six ternary word has the displayed moments and its exact
periodic weighted series cancels. -/
def periodSixWeightedKernel_claim35776 : Prop :=
  let c : Fin 6 → ℤ := ![-1, 0, 1, 1, 0, -1]
  let A : ℤ :=
    ∑ r : Fin 6, c r * (2 : ℤ) ^ (5 - r.1)
  let B : ℤ :=
    ∑ r : Fin 6,
      ((r.1 + 1 : ℕ) : ℤ) * c r * (2 : ℤ) ^ (5 - r.1)
  let weightedBlock : ℕ → ℝ := fun k =>
    ((6 * k + 3 : ℕ) : ℝ) / (2 : ℝ) ^ (6 * k + 3) +
      ((6 * k + 4 : ℕ) : ℝ) / (2 : ℝ) ^ (6 * k + 4) -
      ((6 * k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (6 * k + 1) -
      ((6 * k + 6 : ℕ) : ℝ) / (2 : ℝ) ^ (6 * k + 6)
  c = ![-1, 0, 1, 1, 0, -1] ∧
    A = -21 ∧
    B = 2 ∧
    63 * B + 6 * A = 0 ∧
    Summable weightedBlock ∧
    ∑' k : ℕ, weightedBlock k = 0

end

end MathlibPlus.Open.ResearchFormalization.Claim35776
