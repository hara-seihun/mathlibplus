import Mathlib

namespace MathlibPlus.MomentGeometry

/-- The two-by-two positive-quadratic consequence of the principal moment
matrix: its diagonal entries are nonnegative and its determinant is
nonnegative.  This is the algebraic core of admitted claim 13350; the
moment-representation clauses are intentionally not assumed here. -/
theorem principalMomentQuadratic_logConvex_claim13350
    (a₁ a₂ a₄ : ℝ)
    (hquad : ∀ x y : ℝ, 0 ≤ a₁ * x ^ 2 + 2 * a₂ * x * y + a₄ * y ^ 2) :
    0 ≤ a₁ ∧ 0 ≤ a₄ ∧ a₂ ^ 2 ≤ a₁ * a₄ := by
  have ha₁ : 0 ≤ a₁ := by
    simpa using hquad 1 0
  have ha₄ : 0 ≤ a₄ := by
    simpa using hquad 0 1
  have hdet : a₂ ^ 2 ≤ a₁ * a₄ := by
    by_cases ha₁pos : 0 < a₁
    · have hprod : 0 ≤ a₁ * (a₁ * a₄ - a₂ ^ 2) := by
        calc
          0 ≤ a₁ * (-a₂) ^ 2 + 2 * a₂ * (-a₂) * a₁ + a₄ * a₁ ^ 2 :=
            hquad (-a₂) a₁
          _ = a₁ * (a₁ * a₄ - a₂ ^ 2) := by ring
      by_contra hnot
      have hneg : a₁ * (a₁ * a₄ - a₂ ^ 2) < 0 := by
        apply mul_neg_of_pos_of_neg ha₁pos
        linarith
      exact (not_lt_of_ge hprod) hneg
    · have ha₁zero : a₁ = 0 := by linarith
      have ha₂zero : a₂ = 0 := by
        by_contra ha₂
        have hden : 2 * a₂ ≠ 0 := by
          intro h
          apply ha₂
          linarith
        let x : ℝ := -(a₄ + 1) / (2 * a₂)
        have hvalue :
            a₁ * x ^ 2 + 2 * a₂ * x * 1 + a₄ * 1 ^ 2 = -1 := by
          rw [ha₁zero]
          dsimp [x]
          field_simp [hden]
          ring
        have h := hquad x 1
        rw [hvalue] at h
        linarith
      rw [ha₁zero, ha₂zero]
      norm_num
  exact ⟨ha₁, ha₄, hdet⟩

end MathlibPlus.MomentGeometry
