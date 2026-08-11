import Mathlib

namespace MathlibPlus.Analysis.ComplexSuperheat

/-- Claim 3105 residue: the first nontrivial case, retained as a kernel-checked
residue for the all-`k` node. -/
theorem realPartExpansion_k_one (Y : ℝ) (hY : 0 ≤ Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X : ℝ, 1 ≤ X ∧
      ∀ x y : ℝ, X ≤ x → |y| ≤ Y →
        |(((x : ℂ) + (y : ℂ) * Complex.I) ^ (2 * 1)).re - x ^ (2 * 1)| ≤
          C * x ^ (2 * 1 - 2) := by
  refine ⟨Y ^ 2, sq_nonneg Y, 1, le_rfl, ?_⟩
  intro x y hx hy
  have hy_sq : y ^ 2 ≤ Y ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg y) hY).2 hy
    simpa only [sq_abs] using h
  simp only [Nat.mul_one, Nat.reduceSubDiff, pow_two, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  norm_num
  simpa [pow_two, mul_comm] using hy_sq

end MathlibPlus.Analysis.ComplexSuperheat
