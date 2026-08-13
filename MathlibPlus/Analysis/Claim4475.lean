import Mathlib

namespace MathlibPlus.Analysis.Claim4475

/-- The nonzero integer-argument multiplicativity of the phase `u_x` from
claim 4475.  The phase is the complex exponential of `i x log n`, with the
standard zero convention at `n = 0`. -/
theorem unitPhase_mul_claim4475 (x : ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    let u : ℕ → ℂ := fun k ↦
      if k = 0 then 0 else
        Complex.exp (Complex.I * (x : ℂ) * (Real.log (k : ℝ) : ℂ))
    u (m * n) = u m * u n := by
  dsimp
  simp only [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn]
  rw [show ((m * n : ℕ) : ℝ) = (m : ℝ) * (n : ℝ) by norm_num]
  rw [Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)]
  rw [show
    Complex.I * (x : ℂ) * ((Real.log (m : ℝ) + Real.log (n : ℝ) : ℝ) : ℂ) =
      Complex.I * (x : ℂ) * (Real.log (m : ℝ) : ℂ) +
        Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ) by
    push_cast
    ring]
  rw [Complex.exp_add]

end MathlibPlus.Analysis.Claim4475
