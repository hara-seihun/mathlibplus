import MathlibPlus.Open.ResearchFormalization.BatchO0078

namespace MathlibPlus.Open.ResearchFormalization.ShiftedClockBounds12116

noncomputable section

/-- Claim 12116: uniform shifted-clock bounds and vanishing supremum, together
with the fixed-m large-shift expansion. -/
def claim12116 : Prop :=
  (∀ (m : ℕ), 1 ≤ m →
    ∀ (σ t : ℝ),
      (1 / 2 : ℝ) ≤ σ →
      σ ≤ 1 →
      0 < MathlibPlus.Open.ResearchFormalization.BatchO0078.shiftedClock m σ t ∧
        MathlibPlus.Open.ResearchFormalization.BatchO0078.shiftedClock m σ t ≤
          (1 / 4 : ℝ) *
            (MathlibPlus.Open.ResearchFormalization.BatchO0078.trigamma
              ((m : ℂ) + (σ : ℂ) / 2)).re ∧
          (1 / 4 : ℝ) *
              (MathlibPlus.Open.ResearchFormalization.BatchO0078.trigamma
                ((m : ℂ) + (σ : ℂ) / 2)).re ≤
            (1 / 4 : ℝ) *
              (MathlibPlus.Open.ResearchFormalization.BatchO0078.trigamma
                ((m : ℂ) + ((1 / 4 : ℝ) : ℂ))).re) ∧
  Filter.Tendsto
    (fun m : ℕ =>
      sSup {r : ℝ |
        ∃ (σ t : ℝ),
          (1 / 2 : ℝ) ≤ σ ∧ σ ≤ 1 ∧
            r = MathlibPlus.Open.ResearchFormalization.BatchO0078.shiftedClock m σ t})
    Filter.atTop (nhds 0) ∧
  (∀ (m : ℕ), 1 ≤ m →
    ∃ (C T : ℝ),
      0 < T ∧ 0 ≤ C ∧
        ∀ (σ : ℝ),
          (1 / 2 : ℝ) ≤ σ →
          σ ≤ 1 →
          ∀ t : ℝ, T ≤ t →
            |MathlibPlus.Open.ResearchFormalization.BatchO0078.shiftedClock m σ t -
                ((m : ℝ) + (σ - 1) / 2) * t⁻¹ ^ 2| ≤
              C * t⁻¹ ^ 4)

end

end MathlibPlus.Open.ResearchFormalization.ShiftedClockBounds12116
