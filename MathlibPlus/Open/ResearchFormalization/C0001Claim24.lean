import Mathlib

open Filter
open scoped Topology

namespace MathlibPlus.Open.ResearchFormalization.C0001Claim24

/-- Positive successive-ratio growth gives the limiting fraction carried by the
last increment of the cumulative sum. -/
def positiveIncrementRatio_claim24 : Prop :=
  ∀ (d : ℕ → ℝ) (r : ℝ),
    (∀ n : ℕ, 0 < d n) →
    Tendsto (fun n : ℕ => d (n + 1) / d n) atTop (𝓝 r) →
    1 < r →
    Tendsto
      (fun n : ℕ => d n / ∑ k ∈ Finset.range (n + 1), d k)
      atTop (𝓝 (1 - r⁻¹))

end MathlibPlus.Open.ResearchFormalization.C0001Claim24
