import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.K0124

open Filter
open scoped Topology

/-- Claim 8872: reciprocal-quantile regularity of a decreasing positive lattice. -/
def claim8872 (z : ℕ → ℕ → ℝ) : Prop :=
  (∀ n i : ℕ, 1 ≤ i →
    0 < z n i ∧ z n (i + 1) < z n i) ∧
    ∀ δ R : ℝ, 0 < δ → δ < R →
      Tendsto
        (fun n : ℕ =>
          sSup
            ((fun t : ℝ =>
                |z n (Nat.floor ((n : ℝ) * t)) - t⁻¹|) ''
              Set.Icc δ R))
        atTop (𝓝 0)

end MathlibPlus.Open.ResearchFormalization.K0124
