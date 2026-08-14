import Mathlib

open Filter
open scoped BigOperators Topology

namespace MathlibPlus.Analysis.Claim8900

/-- The trailing-block estimate from claim 8900, with the supremum taken over
`m < j ≤ N` and the error sum over the same block. -/
theorem trailingBlockError_bound_claim8900
    (R : ℕ → ℝ) {m N : ℕ} (hmn : m < N) :
    let s := Finset.Ioc m N
    let Ω := s.sup' (Finset.nonempty_Ioc.mpr hmn) (fun j => |R j - R N|)
    let E := (∑ j ∈ s, (R j - R N))
    |E| ≤ (N - m : ℝ) * Ω := by
  let s : Finset ℕ := Finset.Ioc m N
  have hs : s.Nonempty := by
    refine ⟨N, ?_⟩
    simp [s, hmn]
  let Ω : ℝ := s.sup' hs (fun j => |R j - R N|)
  let E : ℝ := (∑ j ∈ s, (R j - R N))
  have h_each : ∀ j ∈ s, |R j - R N| ≤ Ω := by
    intro j hj
    exact Finset.le_sup' (fun j => |R j - R N|) hj
  change |E| ≤ (N - m : ℝ) * Ω
  calc
    |E| ≤ ∑ j ∈ s, |R j - R N| := by
      dsimp [E]
      exact Finset.abs_sum_le_sum_abs (fun j => R j - R N) s
    _ ≤ ∑ j ∈ s, Ω := by
      apply Finset.sum_le_sum
      intro j hj
      exact h_each j hj
    _ = (s.card : ℝ) * Ω := by simp
    _ = (N - m : ℝ) * Ω := by
      rw [show s.card = N - m by exact Nat.card_Ioc m N]
      rw [Nat.cast_sub (Nat.le_of_lt hmn)]

/-- A Cesàro-small full-block error is small after division by the block length. -/
theorem cesaroError_normalized_claim8900
    (R : ℕ → ℝ)
    (hCesaro : Tendsto
      (fun N : ℕ => (1 / (N : ℝ)) *
        (∑ j ∈ Finset.Ioc 0 N, |R j - R N|))
      atTop (𝓝 0)) :
    Tendsto
      (fun N : ℕ => (1 / (N : ℝ)) *
        (∑ j ∈ Finset.Ioc 0 N, (R j - R N)))
      atTop (𝓝 0) := by
  have hbound : ∀ᶠ N : ℕ in atTop,
      |(1 / (N : ℝ)) * (∑ j ∈ Finset.Ioc 0 N, (R j - R N))| ≤
        (1 / (N : ℝ)) * (∑ j ∈ Finset.Ioc 0 N, |R j - R N|) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / (N : ℝ)))]
    gcongr
    exact Finset.abs_sum_le_sum_abs (fun j => R j - R N) (Finset.Ioc 0 N)
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  exact squeeze_zero' (Filter.Eventually.of_forall (fun N => abs_nonneg _)) hbound hCesaro

end MathlibPlus.Analysis.Claim8900
