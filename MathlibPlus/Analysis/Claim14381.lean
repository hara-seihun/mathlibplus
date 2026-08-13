import Mathlib

open Filter
open scoped Topology

namespace MathlibPlus.Analysis.Claim14381

/-- The exact scalar Gaussian-energy bound from claim 14381. -/
theorem gaussianEnergy_bound_claim14381 {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε) :
    (1 - Real.exp (-c * ε ^ 2)) / (2 * ε) ≤ (c / 2) * ε := by
  have ha : 0 ≤ c * ε ^ 2 := by positivity
  have hexp : 1 - Real.exp (-c * ε ^ 2) ≤ c * ε ^ 2 := by
    have h := Real.add_one_le_exp (-c * ε ^ 2)
    linarith
  have hden : 0 < 2 * ε := by positivity
  apply (div_le_iff₀ hden).2
  rw [show (c / 2) * ε * (2 * ε) = c * ε ^ 2 by ring]
  exact hexp

/-- Along positive scales tending to zero, the scalar energy in claim 14381
squeezes to zero. -/
theorem gaussianEnergy_tendsto_claim14381 {c : ℝ} (hc : 0 ≤ c)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hεpos : ∀ j, 0 < ε j) :
    Tendsto (fun j => (1 - Real.exp (-c * (ε j) ^ 2)) / (2 * ε j))
      atTop (𝓝 0) := by
  have hupper : Tendsto (fun j => (c / 2) * ε j) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hε)
  refine squeeze_zero ?_ ?_ hupper
  · intro j
    have ha : 0 ≤ c * (ε j) ^ 2 := by positivity
    have hnonneg : 0 ≤ 1 - Real.exp (-c * (ε j) ^ 2) := by
      have hle : Real.exp (-c * (ε j) ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      linarith
    exact div_nonneg hnonneg (le_of_lt (mul_pos (by norm_num) (hεpos j)))
  · intro j
    exact gaussianEnergy_bound_claim14381 hc (hεpos j)

end MathlibPlus.Analysis.Claim14381
