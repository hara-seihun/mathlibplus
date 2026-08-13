import Mathlib

open scoped BigOperators

namespace MathlibPlus.LinearAlgebra.Claim15996

/-- Claim 15996: a positive weighted row with exactly two nonzero blocks has
nonzero opposite block masses. -/
theorem oppositeMassOfTwoSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ω row : ι → ℝ) (i j : ι) (hij : i ≠ j)
    (hω : ∀ k, 0 < ω k)
    (hi : row i ≠ 0) (hj : row j ≠ 0)
    (hzero : ∀ k, k ≠ i → k ≠ j → row k = 0)
    (htotal : ∑ k, ω k * row k = 0) :
    ω i * row i ≠ 0 ∧
      ω j * row j ≠ 0 ∧
        ω i * row i = -(ω j * row j) := by
  have hsum_subset :
      (∑ k ∈ ({i, j} : Finset ι), ω k * row k) =
        ∑ k : ι, ω k * row k := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k hk hnot
    have hki : k ≠ i := by
      intro h
      apply hnot
      simpa [h]
    have hkj : k ≠ j := by
      intro h
      apply hnot
      simp [h]
    simp [hzero k hki hkj]
  have hsum : ω i * row i + ω j * row j = 0 := by
    calc
      ω i * row i + ω j * row j =
          ∑ k ∈ ({i, j} : Finset ι), ω k * row k := by
            symm
            exact Finset.sum_pair hij
      _ = ∑ k : ι, ω k * row k := hsum_subset
      _ = 0 := htotal
  have hmi : ω i * row i ≠ 0 :=
    mul_ne_zero (ne_of_gt (hω i)) hi
  have hmj : ω j * row j ≠ 0 :=
    mul_ne_zero (ne_of_gt (hω j)) hj
  exact ⟨hmi, hmj, by linarith⟩

end MathlibPlus.LinearAlgebra.Claim15996
