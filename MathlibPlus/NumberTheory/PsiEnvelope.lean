import Mathlib

/-!
# Square-root-exponential Chebyshev envelopes

This file formalizes the envelope definition and the complete strict decay comparison
in Records 1 and 3 of legacy packet `C-0067`. It does not introduce a placeholder for
Chebyshev's `ψ` or assert the packet's separate global analytic bound.
-/

namespace MathlibPlus.NumberTheory.PsiEnvelope

/-- The `(C,d)` square-root-exponential envelope
`C (log x)^(3/2) exp(-d sqrt(log x))` from packet `C-0067`. -/
noncomputable def psiEnvelope (C d x : ℝ) : ℝ :=
  C * (Real.log x) ^ (3 / 2 : ℝ) *
    Real.exp (-d * Real.sqrt (Real.log x))

/-- Record 3 of packet `C-0067`: the decay increase is exactly `85241/2500000`,
is positive, and with the amplitude fixed at `9.2202181` it gives a strictly smaller
envelope at every `x > 2`. -/
theorem psiDecayImprovement :
    (0.88178 : ℝ) - 0.8476836 = 85241 / 2500000 ∧
    0 < (85241 / 2500000 : ℝ) ∧
    ∀ x : ℝ, 2 < x →
      psiEnvelope 9.2202181 0.88178 x <
        psiEnvelope 9.2202181 0.8476836 x := by
  constructor
  · norm_num
  constructor
  · norm_num
  intro x hx
  have hx1 : 1 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hsqrt : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 hlog
  have hexp :
      Real.exp (-(0.88178 : ℝ) * Real.sqrt (Real.log x)) <
        Real.exp (-(0.8476836 : ℝ) * Real.sqrt (Real.log x)) := by
    rw [Real.exp_lt_exp]
    nlinarith
  have hprefactor :
      0 < (9.2202181 : ℝ) * (Real.log x) ^ (3 / 2 : ℝ) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hlog _)
  exact mul_lt_mul_of_pos_left hexp hprefactor

end MathlibPlus.NumberTheory.PsiEnvelope
