import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/--
The literal quadratic-minimization core of admitted claim 21590.  A real
quadratic with positive leading coefficient has the displayed unique minimizer.
-/
theorem claim21590_quadratic_minimum (A B C : ℝ) (hA : 0 < A) :
    let q : ℝ → ℝ := fun c => A * c ^ 2 + B * c + C
    (∀ c, C - B ^ 2 / (4 * A) ≤ q c) ∧
      q (-B / (2 * A)) = C - B ^ 2 / (4 * A) ∧
        (∀ c, q c = C - B ^ 2 / (4 * A) → c = -B / (2 * A)) := by
  dsimp
  have hA0 : A ≠ 0 := ne_of_gt hA
  have h4A0 : 4 * A ≠ 0 := by positivity
  have h4A : 0 < 4 * A := by positivity
  have h2A0 : 2 * A ≠ 0 := by positivity
  have hmin :
      A * (-B / (2 * A)) ^ 2 + B * (-B / (2 * A)) + C =
        C - B ^ 2 / (4 * A) := by
    field_simp [hA0]
    ring
  refine ⟨?_, hmin, ?_⟩
  · intro c
    have hs : 0 ≤ (2 * A * c + B) ^ 2 := sq_nonneg _
    have hident :
        (A * c ^ 2 + B * c + C) - (C - B ^ 2 / (4 * A)) =
          (2 * A * c + B) ^ 2 / (4 * A) := by
      field_simp [hA0]
      ring
    have hfrac : 0 ≤ (2 * A * c + B) ^ 2 / (4 * A) :=
      div_nonneg hs (le_of_lt h4A)
    nlinarith [hident, hfrac]
  · intro c hc
    have hident :
        (A * c ^ 2 + B * c + C) - (C - B ^ 2 / (4 * A)) =
          (2 * A * c + B) ^ 2 / (4 * A) := by
      field_simp [hA0]
      ring
    have hzero : (2 * A * c + B) ^ 2 = 0 := by
      have : (2 * A * c + B) ^ 2 / (4 * A) = 0 := by
        rw [← hident, hc]
        ring
      exact (div_eq_zero_iff).mp this |>.resolve_right h4A0
    have hlin : 2 * A * c + B = 0 := sq_eq_zero_iff.mp hzero
    field_simp [hA0]
    nlinarith

end MathlibPlus.Algebra
