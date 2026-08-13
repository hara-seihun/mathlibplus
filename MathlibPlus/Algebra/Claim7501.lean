import Mathlib

namespace MathlibPlus.Algebra.Claim7501

/-!
The packet's pivot recurrence is written with the quotient sequence expanded as
its finite product.  This removes the packet's informal "where defined"
qualification: the recurrence factor is a nonzero rational for every natural
index, while the pivot value may itself vanish for special `α`.
-/

/-- The finite-product definition of `q` has the packet's ratio, and the
corresponding pivots satisfy the stated rational recurrence. -/
theorem pivotRecurrence (α : ℚ) (j : ℕ) :
    let factor : ℕ → ℚ := fun u =>
      2 * (4 * (u : ℚ) + 1) * (4 * (u : ℚ) + 3) ^ 2 * (4 * (u : ℚ) + 5)
    let q : ℕ → ℚ := fun m => 2 * (∏ u ∈ Finset.range m, factor u)
    let d : ℕ → ℚ := fun m =>
      (∏ u ∈ Finset.range (m + 1), (α + (u : ℚ))) *
        (∏ u ∈ Finset.range m, (2 * α - (2 * (u : ℚ) + 1))) / q m
    let r : ℕ → ℚ := fun u =>
      ((α + (u : ℚ) + 1) * (2 * α - (2 * (u : ℚ) + 1))) / factor u
    q 0 = 2 ∧ q (j + 1) / q j = factor j ∧ d (j + 1) = r j * d j := by
  dsimp
  let factor : ℕ → ℚ := fun u =>
    2 * (4 * (u : ℚ) + 1) * (4 * (u : ℚ) + 3) ^ 2 * (4 * (u : ℚ) + 5)
  let q : ℕ → ℚ := fun m => 2 * (∏ u ∈ Finset.range m, factor u)
  let d : ℕ → ℚ := fun m =>
    (∏ u ∈ Finset.range (m + 1), (α + (u : ℚ))) *
      (∏ u ∈ Finset.range m, (2 * α - (2 * (u : ℚ) + 1))) / q m
  let r : ℕ → ℚ := fun u =>
    ((α + (u : ℚ) + 1) * (2 * α - (2 * (u : ℚ) + 1))) / factor u
  change q 0 = 2 ∧ q (j + 1) / q j = factor j ∧ d (j + 1) = r j * d j
  have hfactor : ∀ u, factor u ≠ 0 := by
    intro u
    dsimp [factor]
    positivity
  have hq : ∀ m, q m ≠ 0 := by
    intro m
    dsimp [q]
    apply mul_ne_zero (by norm_num)
    rw [Finset.prod_ne_zero_iff]
    intro u hu
    exact hfactor u
  have hqstep : q (j + 1) = q j * factor j := by
    dsimp [q]
    rw [Finset.prod_range_succ]
    ring
  have ha :
      (∏ u ∈ Finset.range (j + 1 + 1), (α + (u : ℚ))) =
        (∏ u ∈ Finset.range (j + 1), (α + (u : ℚ))) * (α + ((j + 1 : ℕ) : ℚ)) := by
    rw [Finset.prod_range_succ]
  have hb :
      (∏ u ∈ Finset.range (j + 1), (2 * α - (2 * (u : ℚ) + 1))) =
        (∏ u ∈ Finset.range j, (2 * α - (2 * (u : ℚ) + 1))) *
          (2 * α - (2 * (j : ℚ) + 1)) := by
    rw [Finset.prod_range_succ]
  refine ⟨?_, ?_, ?_⟩
  · simp [q]
  · apply (div_eq_iff (hq j)).2
    rw [hqstep]
    ring
  · dsimp [d, r]
    rw [ha, hb, hqstep]
    field_simp [hq j, hfactor j]
    push_cast
    ring

end MathlibPlus.Algebra.Claim7501
