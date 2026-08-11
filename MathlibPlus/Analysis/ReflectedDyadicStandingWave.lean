import Mathlib

namespace MathlibPlus.Analysis

noncomputable section

/--
Formalization of admitted claim 13449.  The notation `2 ^ (-s)` is made
explicit as the principal exponential expression `exp (-s * log 2)`; the
source's `d₋` is its reflection at `1 - s`.
-/
theorem reflectedDyadicStandingWave :
    let dPlus : ℂ → ℂ := fun s => Complex.exp (-s * (Real.log 2 : ℂ))
    let dMinus : ℂ → ℂ := fun s => dPlus (1 - s)
    (∀ s : ℂ, dPlus s * dMinus s = (1 / 2 : ℂ)) ∧
      (∀ t : ℝ,
        dPlus ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) +
            dMinus ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
          (Real.sqrt 2 * Real.cos (t * Real.log 2) : ℂ)) ∧
      (∀ t : ℝ,
        dPlus ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) -
            dMinus ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
          (-Complex.I * Real.sqrt 2 * Real.sin (t * Real.log 2) : ℂ)) := by
  dsimp
  have dPlusOnWave : ∀ t : ℝ,
      Complex.exp (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I) * (Real.log 2 : ℂ)) =
        (Real.exp (-(Real.log 2) / 2) : ℂ) *
          (Real.cos (t * Real.log 2) -
            (Real.sin (t * Real.log 2) : ℂ) * Complex.I) := by
    intro t
    have he :
        -((1 / 2 : ℂ) + (t : ℂ) * Complex.I) * (Real.log 2 : ℂ) =
          (-(Real.log 2) / 2 : ℝ) +
            (-(t * Real.log 2) : ℝ) * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_add_mul_I, Complex.ofReal_exp]
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    simp [Real.cos_neg, Real.sin_neg] <;> ring
  have dMinusOnWave : ∀ t : ℝ,
      Complex.exp (-(1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) *
          (Real.log 2 : ℂ)) =
        (Real.exp (-(Real.log 2) / 2) : ℂ) *
          (Real.cos (t * Real.log 2) +
            (Real.sin (t * Real.log 2) : ℂ) * Complex.I) := by
    intro t
    have he :
        -(1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) * (Real.log 2 : ℂ) =
          (-(Real.log 2) / 2 : ℝ) +
            (t * Real.log 2 : ℝ) * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_add_mul_I, Complex.ofReal_exp]
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
  have hsqrt : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
    have : (0 : ℝ) ≤ 2 := by norm_num
    simpa using (Real.sq_sqrt this)
  have hsqrtpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hcoef : Real.exp (-(Real.log 2) / 2) = (Real.sqrt 2)⁻¹ := by
    have hlog : Real.log (Real.sqrt (2 : ℝ)) = Real.log 2 / 2 := by
      simpa using (Real.log_sqrt (show (0 : ℝ) ≤ 2 by norm_num))
    have he : -(Real.log 2) / 2 = -Real.log (Real.sqrt 2) := by
      rw [hlog]
      ring
    rw [he, Real.exp_neg, Real.exp_log hsqrtpos]
  have hsqrtC : (Real.sqrt (2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast hsqrt
  constructor
  · intro s
    rw [← Complex.exp_add]
    congr 1
    ring_nf
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  constructor
  · intro t
    rw [dPlusOnWave t, dMinusOnWave t, hcoef]
    push_cast
    field_simp
    ring_nf
    rw [hsqrtC]
  · intro t
    rw [dPlusOnWave t, dMinusOnWave t, hcoef]
    push_cast
    field_simp
    ring_nf
    rw [hsqrtC]

end
end MathlibPlus.Analysis
