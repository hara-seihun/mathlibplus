import Mathlib

namespace MathlibPlus.Combinatorics.SplitSupportSaturation

/-- Claim 5472: after radius-three truncation, every split support for an
interval of length at least six is one of the five displayed pairs, and all
five pairs occur.  The interval `Icc 1 (L - 1)` is the exact finite form of
`1 ≤ i < L`. -/
theorem splitSupportSaturationAtSix (L : ℕ) (hL : 6 ≤ L) :
    (Finset.Icc 1 (L - 1)).image
        (fun i : ℕ => (min i 3, min (L - i) 3)) =
      {(1, 3), (2, 3), (3, 3), (3, 2), (3, 1)} := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have hi_lower : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hi_upper : i ≤ L - 1 := (Finset.mem_Icc.mp hi).2
    have hj_lower : 1 ≤ L - i := by omega
    by_cases hi3 : i ≤ 3
    · by_cases hj3 : L - i ≤ 3
      · have hi_eq : i = 3 := by omega
        have hj_eq : L - i = 3 := by omega
        have hL_eq : L = 6 := by omega
        subst L
        subst i
        norm_num
      · have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases hi_cases with rfl | rfl | rfl
        · left
          rw [Nat.min_eq_left (by omega : 1 ≤ 3),
            Nat.min_eq_right (by omega : 3 ≤ L - 1)]
        · right; left
          rw [Nat.min_eq_left (by omega : 2 ≤ 3),
            Nat.min_eq_right (by omega : 3 ≤ L - 2)]
        · right; right; left
          rw [Nat.min_eq_right (by omega : 3 ≤ 3),
            Nat.min_eq_right (by omega : 3 ≤ L - 3)]
    · have hi4 : 4 ≤ i := by omega
      by_cases hj3 : L - i ≤ 3
      · have hj_cases : L - i = 1 ∨ L - i = 2 ∨ L - i = 3 := by omega
        rcases hj_cases with hj_eq | hj_eq | hj_eq
        · right; right; right; right
          rw [Nat.min_eq_right (by omega : 3 ≤ i), hj_eq]
          norm_num
        · right; right; right; left
          rw [Nat.min_eq_right (by omega : 3 ≤ i), hj_eq]
          norm_num
        · right; right; left
          rw [Nat.min_eq_right (by omega : 3 ≤ i), hj_eq]
          norm_num
      · right; right; left
        rw [Nat.min_eq_right (by omega : 3 ≤ i),
          Nat.min_eq_right (by omega : 3 ≤ L - i)]
  · intro hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · apply Finset.mem_image.mpr
      refine ⟨1, ?_, ?_⟩
      · apply Finset.mem_Icc.mpr
        omega
      · have hL1 : 3 ≤ L - 1 := by omega
        rw [Nat.min_eq_left (by omega : 1 ≤ 3), Nat.min_eq_right hL1]
    · apply Finset.mem_image.mpr
      refine ⟨2, ?_, ?_⟩
      · apply Finset.mem_Icc.mpr
        omega
      · have hL2 : 3 ≤ L - 2 := by omega
        rw [Nat.min_eq_left (by omega : 2 ≤ 3), Nat.min_eq_right hL2]
    · apply Finset.mem_image.mpr
      refine ⟨3, ?_, ?_⟩
      · apply Finset.mem_Icc.mpr
        omega
      · have hL3 : 3 ≤ L - 3 := by omega
        rw [Nat.min_eq_right (by omega : 3 ≤ 3), Nat.min_eq_right hL3]
    · apply Finset.mem_image.mpr
      refine ⟨L - 2, ?_, ?_⟩
      · apply Finset.mem_Icc.mpr
        omega
      · have hL2 : 3 ≤ L - 2 := by omega
        have hcomp : L - (L - 2) = 2 := by omega
        rw [Nat.min_eq_right hL2, hcomp,
          Nat.min_eq_left (by omega : 2 ≤ 3)]
    · apply Finset.mem_image.mpr
      refine ⟨L - 1, ?_, ?_⟩
      · apply Finset.mem_Icc.mpr
        omega
      · have hL1 : 3 ≤ L - 1 := by omega
        have hcomp : L - (L - 1) = 1 := by omega
        rw [Nat.min_eq_right hL1, hcomp,
          Nat.min_eq_left (by omega : 1 ≤ 3)]

end MathlibPlus.Combinatorics.SplitSupportSaturation
