import Mathlib

namespace MathlibPlus.NumberTheory.Claim4476

/-- Additivity of the complex unit phase in its real spectral parameter. -/
theorem unitPhase_add_claim4476
    (x y : ℝ) {n : ℕ} (hn : n ≠ 0) :
    let u : ℝ → ℕ → ℂ := fun z k ↦
      if k = 0 then 0 else
        Complex.exp (Complex.I * (z : ℂ) * (Real.log (k : ℝ) : ℂ))
    u (x + y) n = u x n * u y n ∧
      u 0 n = 1 ∧ u (-x) n * u x n = 1 := by
  dsimp
  simp only [if_neg hn]
  constructor
  · rw [show Complex.I * ((x + y : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ) =
        Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ) +
          Complex.I * (y : ℂ) * (Real.log (n : ℝ) : ℂ) by
      push_cast
      ring]
    exact Complex.exp_add _ _
  constructor
  · simp
  · rw [← Complex.exp_add]
    rw [show Complex.I * ((-x : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ) +
          Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ) = 0 by
      push_cast
      ring]
    exact Complex.exp_zero

end MathlibPlus.NumberTheory.Claim4476
