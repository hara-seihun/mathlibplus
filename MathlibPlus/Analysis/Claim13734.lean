import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis.Claim13734

private lemma product_diff_identity (N : ℕ) (z w : ℕ → ℂ) :
    (∏ k ∈ Finset.range N, z k) - (∏ k ∈ Finset.range N, w k) =
      ∑ k ∈ Finset.range N,
        (z k - w k) * (∏ j ∈ Finset.range k, w j) *
          (∏ j ∈ Finset.Ico (k + 1) N, z j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hIco (k : ℕ) (hk : k < N) :
        Finset.Ico (k + 1) (N + 1) =
          insert N (Finset.Ico (k + 1) N) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hsum :
        (∑ k ∈ Finset.range N,
          (z k - w k) * (∏ j ∈ Finset.range k, w j) *
            (∏ j ∈ Finset.Ico (k + 1) (N + 1), z j)) =
          (∑ k ∈ Finset.range N,
            (z k - w k) * (∏ j ∈ Finset.range k, w j) *
              (∏ j ∈ Finset.Ico (k + 1) N, z j)) * z N := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k < N := Finset.mem_range.1 hk
      have hnot : N ∉ Finset.Ico (k + 1) N := by
        simp only [Finset.mem_Ico]
        omega
      rw [hIco k hkN, Finset.prod_insert hnot]
      ring
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ,
      hsum]
    simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
    rw [← ih]
    ring

/--
Claim 13734.  For finite complex sequences indexed by `Finset.range N`, the
product difference is bounded by the weighted telescoping sum.  The prefix
contains the `w`-factors and the suffix contains the `z`-factors, exactly as in
the source inequality.
-/
theorem finiteComplexProductDifference (N : ℕ) (z w : ℕ → ℂ) :
    ‖(∏ k ∈ Finset.range N, z k) - (∏ k ∈ Finset.range N, w k)‖ ≤
      ∑ k ∈ Finset.range N,
        ‖z k - w k‖ *
          (∏ j ∈ Finset.range k, ‖w j‖) *
          (∏ j ∈ Finset.Ico (k + 1) N, ‖z j‖) := by
  rw [product_diff_identity]
  calc
    ‖∑ k ∈ Finset.range N,
        (z k - w k) * (∏ j ∈ Finset.range k, w j) *
          (∏ j ∈ Finset.Ico (k + 1) N, z j)‖ ≤
        ∑ k ∈ Finset.range N,
          ‖(z k - w k) * (∏ j ∈ Finset.range k, w j) *
            (∏ j ∈ Finset.Ico (k + 1) N, z j)‖ := by
            exact norm_sum_le _ _
    _ = ∑ k ∈ Finset.range N,
        ‖z k - w k‖ * (∏ j ∈ Finset.range k, ‖w j‖) *
          (∏ j ∈ Finset.Ico (k + 1) N, ‖z j‖) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul, norm_mul, norm_prod, norm_prod]

end MathlibPlus.Analysis.Claim13734
