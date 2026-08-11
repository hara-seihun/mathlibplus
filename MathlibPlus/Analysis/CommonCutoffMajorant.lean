import Mathlib

namespace MathlibPlus.Analysis.CommonCutoffMajorant

/-- Claim 1669: at a common cutoff, the sum of the selected states is bounded
by the sum of the independent finite per-index maxima. -/
theorem conservativeCommonCutoffMajorant
    {ι σ : Type*} [Fintype ι]
    (N₁ N₂ N : ℕ)
    (T : ι → σ → ℝ)
    (C : ι → ℕ → σ)
    (S : ι → Finset σ)
    (_hcut : N₁ ≤ N ∧ N ≤ N₂)
    (hS : ∀ i, (S i).Nonempty)
    (hC : ∀ i, C i N ∈ S i) :
    ∑ i, T i (C i N) ≤ ∑ i, (S i).sup' (hS i) (T i) := by
  refine Finset.sum_le_sum ?_
  intro i hi
  rw [Finset.le_sup'_iff]
  exact ⟨C i N, hC i, le_rfl⟩

end MathlibPlus.Analysis.CommonCutoffMajorant
