import Mathlib

namespace MathlibPlus.Analysis.Claim10364

/-- Exact first coefficient and logarithmic derivative for one prime. -/
theorem exactPrimeLogarithmicDerivative (p : ℕ) (hp : Nat.Prime p) :
    let h : ℝ → ℝ := fun u =>
      (p : ℝ) ^ (-(1 - u)⁻¹)
    let f : ℝ → ℝ := fun u => -Real.log (1 - h u)
    h 0 = (p : ℝ)⁻¹ ∧
      deriv h 0 = -Real.log (p : ℝ) / p ∧
      deriv f 0 = -Real.log (p : ℝ) / (p - 1) := by
  dsimp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : Real.exp (Real.log (p : ℝ)) = (p : ℝ) :=
    Real.exp_log hp0
  have hlogneg : Real.exp (-Real.log (p : ℝ)) = (p : ℝ)⁻¹ := by
    rw [Real.exp_neg, hlog]
  have hzero_exp :
      Real.exp (Real.log (p : ℝ) * (-(1 - (0 : ℝ))⁻¹)) = (p : ℝ)⁻¹ := by
    simpa using hlogneg
  have hzero :
      (p : ℝ) ^ (-(1 - (0 : ℝ))⁻¹) = (p : ℝ)⁻¹ := by
    rw [Real.rpow_def_of_pos hp0]
    simpa using hzero_exp
  have hpow :
      (fun u : ℝ => (p : ℝ) ^ (-(1 - u)⁻¹)) =
        (fun u : ℝ => Real.exp (Real.log (p : ℝ) * (-(1 - u)⁻¹))) := by
    funext u
    exact Real.rpow_def_of_pos hp0 _
  have hid := hasDerivAt_id (0 : ℝ)
  have hden : HasDerivAt (fun u : ℝ => (1 : ℝ) - u) (-1) 0 := by
    simpa using hid.const_sub (1 : ℝ)
  have hinv : HasDerivAt (fun u : ℝ => (1 - u)⁻¹) 1 0 := by
    have hout := hasDerivAt_inv (x := (1 - 0 : ℝ)) (by norm_num)
    have h := HasDerivAt.comp 0 hout hden
    simpa [Function.comp_def] using h
  have harg :
      HasDerivAt (fun u : ℝ => Real.log (p : ℝ) * (-(1 - u)⁻¹))
        (-Real.log (p : ℝ)) 0 := by
    simpa [mul_neg] using hinv.neg.const_mul (Real.log (p : ℝ))
  have hh_exp :
      HasDerivAt
        (fun u : ℝ => Real.exp (Real.log (p : ℝ) * (-(1 - u)⁻¹)))
        (-Real.log (p : ℝ) / p) 0 := by
    have h := harg.exp
    rw [hzero_exp] at h
    convert h using 1 <;> field_simp
  have hh :
      HasDerivAt (fun u : ℝ => (p : ℝ) ^ (-(1 - u)⁻¹))
        (-Real.log (p : ℝ) / p) 0 := by
    rw [hpow]
    exact hh_exp
  have hnonzero :
      (1 - (p : ℝ) ^ (-(1 - (0 : ℝ))⁻¹)) ≠ 0 := by
    rw [hzero]
    have hp_inv_lt : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).2 hp1
    exact ne_of_gt (sub_pos.mpr hp_inv_lt)
  have hone :
      HasDerivAt
        (fun u : ℝ => 1 - (p : ℝ) ^ (-(1 - u)⁻¹))
        (Real.log (p : ℝ) / p) 0 := by
    simpa [div_eq_mul_inv] using hh.const_sub (1 : ℝ)
  have hlogone := hone.log hnonzero
  have hf := hlogone.neg
  have hf' :
      deriv (fun u : ℝ => -Real.log
        (1 - (p : ℝ) ^ (-(1 - u)⁻¹))) 0 =
        -Real.log (p : ℝ) / (p - 1) := by
    have hfd :
        deriv (fun u : ℝ => -Real.log
          (1 - (p : ℝ) ^ (-(1 - u)⁻¹))) 0 =
          -(Real.log (p : ℝ) / p /
            (1 - (p : ℝ) ^ (-(1 - (0 : ℝ))⁻¹))) := by
      exact hf.deriv
    rw [hfd, hzero]
    field_simp
  exact ⟨hzero, hh.deriv, hf'⟩

end MathlibPlus.Analysis.Claim10364
