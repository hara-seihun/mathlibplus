import Mathlib

/-!
# The elementary `2 + cosh` counterfeit

Kernel-checked elementary facts from Record 10 of legacy packet `C-0028`.
These facts do not assert the packet's separate recurrence-class, Laurent-right-limit,
or central-limit transfer claims.
-/

namespace MathlibPlus.CoshCounterfeit

/-- The packet's even entire counterfeit transform. -/
noncomputable def transform (z : ℂ) : ℂ :=
  2 + Complex.cosh z

/-- A concrete zero of the counterfeit away from the imaginary axis. -/
noncomputable def offAxisZero : ℂ :=
  (Real.arcosh 2 : ℂ) + (Real.pi : ℂ) * Complex.I

/-- The counterfeit is even. -/
theorem transform_even : Function.Even transform := by
  intro z
  rw [transform, transform, Complex.cosh_neg]

/-- The counterfeit is entire. -/
theorem transform_differentiable : Differentiable ℂ transform := by
  unfold transform
  fun_prop

/-- The counterfeit is strictly positive on the real axis. -/
theorem realAxisPositive (x : ℝ) :
    0 < (transform x).re := by
  rw [transform]
  norm_num
  nlinarith [Real.one_le_cosh x]

private lemma cosh_arcosh_two :
    Complex.cosh (Real.arcosh 2 : ℂ) = 2 := by
  apply Complex.ext
  · simpa using Real.cosh_arcosh (by norm_num : (1 : ℝ) ≤ 2)
  · simp

private lemma cosh_pi_mul_I :
    Complex.cosh ((Real.pi : ℂ) * Complex.I) = -1 := by
  rw [Complex.cosh_mul_I]
  apply Complex.ext <;> simp

private lemma sinh_pi_mul_I :
    Complex.sinh ((Real.pi : ℂ) * Complex.I) = 0 := by
  rw [Complex.sinh_mul_I]
  simp

/-- The displayed witness is a zero of `2 + cosh`. -/
theorem offAxisZero_isZero : transform offAxisZero = 0 := by
  rw [transform, offAxisZero, Complex.cosh_add, cosh_arcosh_two,
    cosh_pi_mul_I, sinh_pi_mul_I]
  ring

/-- The displayed zero has nonzero real part. -/
theorem offAxisZero_re_ne_zero : offAxisZero.re ≠ 0 := by
  rw [offAxisZero]
  norm_num
  exact ne_of_gt (Real.arcosh_pos (by norm_num))

/-- Consequently the counterfeit has a zero away from the imaginary axis. -/
theorem exists_offAxisZero :
    ∃ z : ℂ, transform z = 0 ∧ z.re ≠ 0 :=
  ⟨offAxisZero, offAxisZero_isZero, offAxisZero_re_ne_zero⟩

end MathlibPlus.CoshCounterfeit
