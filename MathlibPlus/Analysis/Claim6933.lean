import Mathlib

namespace MathlibPlus.Analysis.Claim6933

/-- A polynomial positive at both endpoints and without an interior zero stays
positive on the closed unit interval. -/
theorem positive_on_unit_interval_of_no_root (q : Polynomial ℝ)
    (h0 : 0 < q.eval 0) (h1 : 0 < q.eval 1)
    (hroot : ∀ x : ℝ, x ∈ Set.Ioo 0 1 → q.eval x ≠ 0) :
    ∀ x : ℝ, x ∈ Set.Icc 0 1 → 0 < q.eval x := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  by_cases hxeq0 : x = 0
  · simpa [hxeq0] using h0
  by_cases hxeq1 : x = 1
  · simpa [hxeq1] using h1
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxeq0)
  have hxlt : x < 1 := lt_of_le_of_ne hx1 hxeq1
  have hxnonneg : 0 ≤ q.eval x := by
    by_contra hneg
    have hneg' : q.eval x < 0 := lt_of_not_ge hneg
    have hzmem : (0 : ℝ) ∈ Set.Icc (q.eval x) (q.eval 0) :=
      ⟨le_of_lt hneg', le_of_lt h0⟩
    have himage :=
      intermediate_value_Icc' (show (0 : ℝ) ≤ x by linarith)
        (Polynomial.continuousOn q) hzmem
    rcases himage with ⟨y, hy, hyeq⟩
    have hypos : 0 < y := by
      have hy0 : 0 ≤ y := hy.1
      exact lt_of_le_of_ne hy0 (by
        intro hyzero
        subst y
        exact (ne_of_gt h0) (by simpa using hyeq))
    have hylt : y < x := by
      have hyx : y ≤ x := hy.2
      exact lt_of_le_of_ne hyx (by
        intro hyxeq
        subst y
        exact (ne_of_lt hneg') (by simpa using hyeq))
    exact hroot y ⟨hypos, hylt.trans hxlt⟩ hyeq
  have hxne : q.eval x ≠ 0 := hroot x ⟨hxpos, hxlt⟩
  exact lt_of_le_of_ne hxnonneg (Ne.symm hxne)

end MathlibPlus.Analysis.Claim6933
