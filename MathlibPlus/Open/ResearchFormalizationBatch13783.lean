import MathlibPlus.Open.ResearchFormalizationBatch13782_13785

open Filter
open scoped Topology

namespace MathlibPlus.Open.ResearchFormalizationBatch13782_13785

noncomputable section

/-- The finite harmonic partial sum on the positive square-Möbius support. -/
noncomputable def harmonicPartial (x : ℝ) (N : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (N + 1),
    if r = 0 then 0 else weightedSquareCoefficient x r / (r : ℝ)

/-- Claim 13783: ordinary harmonic convergence to zero is uniform on every
fixed compact spectral-height interval. -/
def claim13783 : Prop :=
  (∀ x : ℝ,
    Tendsto (fun N : ℕ => harmonicPartial x N)
      atTop (𝓝 (0 : ℝ))) ∧
  (∀ (T ε : ℝ), 0 ≤ T → 0 < ε →
    ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → ∀ x : ℝ, |x| ≤ T →
        |harmonicPartial x N| < ε)

end

end MathlibPlus.Open.ResearchFormalizationBatch13782_13785
