import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.ClockBounds

noncomputable section

/-- The trigamma function, written in its defining series on the half-plane used here. -/
noncomputable def trigamma (z : ℂ) : ℂ :=
  ∑' n : ℕ, (z + (n : ℂ))⁻¹ ^ 2

/-- The shifted clock from the admitted statement. -/
noncomputable def kappa (m : ℕ) (σ t : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
    (trigamma ((m : ℂ) + ((σ : ℂ) - Complex.I * (t : ℂ)) / 2)).re

def inStrip (σ : ℝ) : Prop := 1 / 2 ≤ σ ∧ σ ≤ 1

noncomputable def kappaSup (m : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ σ t : ℝ, inStrip σ ∧ r = kappa m σ t}

def claim_12913 : Prop :=
  (∀ (m : ℕ), 1 ≤ m →
    ∀ (σ t : ℝ), inStrip σ →
      0 < kappa m σ t ∧
      kappa m σ t ≤
        (1 / 4 : ℝ) * (trigamma ((m : ℂ) + (σ : ℂ) / 2)).re ∧
      (1 / 4 : ℝ) * (trigamma ((m : ℂ) + (σ : ℂ) / 2)).re ≤
        (1 / 4 : ℝ) * (trigamma ((m : ℂ) + (1 / 4 : ℝ))).re) ∧
  Filter.Tendsto kappaSup Filter.atTop (nhds 0) ∧
  (∀ (m : ℕ), 1 ≤ m →
    ∃ (C T : ℝ), 0 < T ∧ 0 ≤ C ∧
      ∀ (σ : ℝ), inStrip σ →
        ∀ t : ℝ, T ≤ t →
          |kappa m σ t - (m + (σ - 1) / 2) / t ^ 2| ≤ C / t ^ 4)

end
end MathlibPlus.Open.ResearchFormalization.ClockBounds
