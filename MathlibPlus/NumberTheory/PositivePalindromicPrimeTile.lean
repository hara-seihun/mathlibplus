import Mathlib

namespace MathlibPlus.NumberTheory

/-- The explicit positive palindromic prime-tile counterexample from claim 19573. -/
theorem positivePalindromicPrimeTile_claim19573 :
    let Δ : ℂ → ℂ := fun q => 5 + 2 * (q + q⁻¹)
    let ℓ : ℝ := Real.log 2
    (∀ q : ℂ, q ≠ 0 →
        q * Δ q = 2 * q ^ 2 + 5 * q + 2) ∧
      (∀ q : ℂ, 2 * q ^ 2 + 5 * q + 2 =
        (2 * q + 1) * (q + 2)) ∧
      (∀ q : ℂ, 2 * q ^ 2 + 5 * q + 2 = 0 ↔
        q = -(1 / 2 : ℂ) ∨ q = -2) ∧
      ‖-(1 / 2 : ℂ)‖ ≠ 1 ∧ ‖(-2 : ℂ)‖ ≠ 1 ∧
      0 < ℓ ∧
      let z₁ : ℂ := (1 : ℂ) - ((Real.pi / ℓ : ℝ) : ℂ) * Complex.I
      let z₂ : ℂ := (-1 : ℂ) - ((Real.pi / ℓ : ℝ) : ℂ) * Complex.I
      Complex.exp (-z₁ * (ℓ : ℂ)) = -(1 / 2 : ℂ) ∧
        Complex.exp (-z₂ * (ℓ : ℂ)) = (-2 : ℂ) ∧
        z₁.re = 1 ∧ z₂.re = -1 ∧
        (∀ z : ℂ, Complex.exp (-z * (ℓ : ℂ)) = -(1 / 2 : ℂ) → z.re = 1) ∧
        (∀ z : ℂ, Complex.exp (-z * (ℓ : ℂ)) = (-2 : ℂ) → z.re = -1) := by
  dsimp
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog_ne : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog
  have hlog_ne_c : (Real.log (2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog_ne
  have hq (q : ℂ) (hq0 : q ≠ 0) :
      q * (5 + 2 * (q + q⁻¹)) = 2 * q ^ 2 + 5 * q + 2 := by
    field_simp [hq0]
    ring
  have hfactor (q : ℂ) :
      2 * q ^ 2 + 5 * q + 2 = (2 * q + 1) * (q + 2) := by ring
  have hroots (q : ℂ) :
      2 * q ^ 2 + 5 * q + 2 = 0 ↔
        q = -(1 / 2 : ℂ) ∨ q = -2 := by
    rw [hfactor, mul_eq_zero]
    constructor
    · intro h
      rcases h with h | h
      · left
        have h' : q * 2 = -1 := by linear_combination h
        calc
          q = q * 2 / 2 := by ring
          _ = (-1 : ℂ) / 2 := by rw [h']
          _ = -(1 / 2 : ℂ) := by ring
      · right
        exact eq_neg_of_add_eq_zero_left h
    · intro h
      rcases h with h | h
      · left
        subst q
        norm_num
      · right
        subst q
        norm_num
  have hexp_neg_log : Complex.exp (-(Real.log (2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp,
      Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hexp_log : Complex.exp ((Real.log (2 : ℝ) : ℂ)) = (2 : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    norm_num
  have hexp_one : Complex.exp
      (-((1 : ℂ) - ((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I) *
        (Real.log 2 : ℂ)) = -(1 / 2 : ℂ) := by
    have harg :
        -((1 : ℂ) - ((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I) *
            (Real.log 2 : ℂ) =
          -(Real.log 2 : ℂ) + (Real.pi : ℂ) * Complex.I := by
      push_cast
      field_simp [hlog_ne_c]
      ring
    rw [harg, Complex.exp_add, hexp_neg_log, Complex.exp_pi_mul_I]
    norm_num
  have hexp_two : Complex.exp
      (-((-1 : ℂ) - ((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I) *
        (Real.log 2 : ℂ)) = (-2 : ℂ) := by
    have harg :
        -((-1 : ℂ) - ((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I) *
            (Real.log 2 : ℂ) =
          (Real.log 2 : ℂ) + (Real.pi : ℂ) * Complex.I := by
      push_cast
      field_simp [hlog_ne_c]
      ring
    rw [harg, Complex.exp_add, hexp_log, Complex.exp_pi_mul_I]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, hlog, ?_⟩
  · intro q hq0
    exact hq q hq0
  · intro q
    exact hfactor q
  · intro q
    exact hroots q
  · norm_num
  · norm_num
  have hnorm_exp (z : ℂ) :
      ‖Complex.exp (-z * (Real.log 2 : ℂ))‖ =
        Real.exp (-z.re * Real.log 2) := by
    have hr : ((Real.log (2 : ℝ) : ℂ).re) = Real.log 2 :=
      Complex.ofReal_re _
    have hi : ((Real.log (2 : ℝ) : ℂ).im) = 0 :=
      Complex.ofReal_im _
    rw [Complex.norm_exp]
    congr 1
    rw [Complex.mul_re, Complex.neg_re, hr, hi]
    ring
  · refine ⟨hexp_one, hexp_two, ?_, ?_, ?_, ?_⟩
    · change ((1 : ℂ) - ((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I).re = 1
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_sub,
        sub_zero]
      norm_num
    · change ((-1 : ℂ) - ((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I).re = -1
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_sub,
        sub_zero]
      norm_num
    · intro z hz
      have hz' : Real.exp (-z.re * Real.log 2) = (1 / 2 : ℝ) := by
        rw [← hnorm_exp z, hz]
        norm_num
      have htarget : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]
        norm_num
      have heq : -z.re * Real.log 2 = -Real.log 2 :=
        Real.exp_injective (hz'.trans htarget.symm)
      nlinarith [hlog]
    · intro z hz
      have hz' : Real.exp (-z.re * Real.log 2) = (2 : ℝ) := by
        rw [← hnorm_exp z, hz]
        norm_num
      have htarget : Real.exp (Real.log 2) = (2 : ℝ) :=
        Real.exp_log (by norm_num)
      have heq : -z.re * Real.log 2 = Real.log 2 :=
        Real.exp_injective (hz'.trans htarget.symm)
      nlinarith [hlog]

end MathlibPlus.NumberTheory
