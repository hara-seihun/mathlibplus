import Mathlib

namespace MathlibPlus.Analysis

private lemma complex_cos_ofReal (x : ℝ) :
    Complex.cos (x : ℂ) = (Real.cos x : ℂ) := by
  apply Complex.ext <;> simp

private lemma complex_sin_ofReal (x : ℝ) :
    Complex.sin (x : ℂ) = (Real.sin x : ℂ) := by
  apply Complex.ext <;> simp

private lemma odd_pi_cos (k : ℤ) :
    Real.cos (((2 * k + 1 : ℤ) : ℝ) * Real.pi) = -1 := by
  convert Real.cos_int_mul_two_pi_add_pi k using 1
  push_cast
  ring_nf

private lemma odd_pi_sin (k : ℤ) :
    Real.sin (((2 * k + 1 : ℤ) : ℝ) * Real.pi) = 0 := by
  simpa using Real.sin_int_mul_pi (2 * k + 1)

private lemma cosh_log_two :
    Complex.cosh (Real.log 2 : ℂ) = (5 / 4 : ℂ) := by
  apply Complex.ext
  · rw [Complex.cosh_ofReal_re, Real.cosh_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  · rw [Complex.cosh_ofReal_im]
    norm_num

private lemma cosh_odd_pi_shift (a : ℂ) (k : ℤ) :
    Complex.cosh (a +
      (((2 * k + 1 : ℤ) : ℝ) * Real.pi : ℝ) * Complex.I) =
      -Complex.cosh a := by
  rw [Complex.cosh_add]
  rw [Complex.cosh_mul_I, Complex.sinh_mul_I,
    complex_cos_ofReal, complex_sin_ofReal,
    odd_pi_cos, odd_pi_sin]
  simp

private lemma four_ofReal_re (x : ℝ) :
    (4 * (x : ℂ)).re = 4 * x := by
  norm_num [Complex.mul_re]

private lemma exp_pair_eq_cosh (w : ℂ) :
    2 * (Complex.exp w + Complex.exp (-w)) = 4 * Complex.cosh w := by
  simp only [Complex.cosh]
  ring

private lemma exp_factorization (w : ℂ) :
    let y : ℂ := Complex.exp w
    y * (5 + 2 * (Complex.exp w + Complex.exp (-w))) =
        2 * y ^ 2 + 5 * y + 2 ∧
      2 * y ^ 2 + 5 * y + 2 = (y + 2) * (2 * y + 1) := by
  dsimp
  have h : Complex.exp w * Complex.exp (-w) = 1 := by
    rw [← Complex.exp_add]
    simp
  constructor
  · calc
      Complex.exp w * (5 + 2 * (Complex.exp w + Complex.exp (-w))) =
          5 * Complex.exp w + 2 * (Complex.exp w) ^ 2 +
            2 * (Complex.exp w * Complex.exp (-w)) := by ring
      _ = 2 * (Complex.exp w) ^ 2 + 5 * Complex.exp w + 2 := by
        rw [h]
        ring
  · ring

private lemma log_two_ne_zero : (Real.log 2 : ℝ) ≠ 0 := by
  exact ne_of_gt (Real.log_pos (by norm_num))

private lemma log_two_mul_div (q : ℝ) :
    (Real.log 2 : ℂ) * ((q / Real.log 2 : ℝ) : ℂ) = (q : ℂ) := by
  rw [← Complex.ofReal_mul]
  field_simp [log_two_ne_zero]

/-- Claim 51132: the even transform is positive on the imaginary axis but has
explicit off-axis zero families. The exponential model `2^z` is represented by
`exp (log 2 * z)`, equivalently by the displayed hyperbolic-cosine expression. -/
theorem reflection_critical_axis_and_off_axis_zeros_claim51132 :
    let M : ℂ → ℂ := fun z =>
      5 + 2 * (Complex.exp ((Real.log 2 : ℂ) * z) +
        Complex.exp (-((Real.log 2 : ℂ) * z)))
    Function.Even M ∧
      (∀ z : ℂ,
        let y : ℂ := Complex.exp ((Real.log 2 : ℂ) * z)
        y * M z = 2 * y ^ 2 + 5 * y + 2 ∧
          2 * y ^ 2 + 5 * y + 2 = (y + 2) * (2 * y + 1)) ∧
      (∀ t : ℝ,
        M ((t : ℂ) * Complex.I) =
            (5 + 4 * Real.cos (t * Real.log 2) : ℝ) ∧
          1 ≤ (M ((t : ℂ) * Complex.I)).re) ∧
      ∀ k : ℤ,
        M ((1 : ℂ) +
            (((2 * k + 1 : ℤ) : ℝ) * Real.pi / Real.log 2 : ℝ) * Complex.I) = 0 ∧
        M ((-1 : ℂ) +
            (((2 * k + 1 : ℤ) : ℝ) * Real.pi / Real.log 2 : ℝ) * Complex.I) = 0 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    dsimp
    simp only [mul_neg, neg_neg, Complex.exp_neg]
    ring
  · intro z
    exact exp_factorization ((Real.log 2 : ℂ) * z)
  · intro t
    have harg :
        (Real.log 2 : ℂ) * ((t : ℂ) * Complex.I) =
          ((t * Real.log 2 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have hcos :
        Complex.cos ((t * Real.log 2 : ℝ) : ℂ) =
          (Real.cos (t * Real.log 2) : ℂ) :=
      complex_cos_ofReal _
    rw [harg, exp_pair_eq_cosh, Complex.cosh_mul_I]
    simp only [hcos]
    constructor
    · norm_num
    · rw [four_ofReal_re]
      nlinarith [Real.neg_one_le_cos (t * Real.log 2)]
  · intro k
    have hplusarg :
        (Real.log 2 : ℂ) *
            ((1 : ℂ) +
              (((2 * k + 1 : ℤ) : ℝ) * Real.pi / Real.log 2 : ℝ) * Complex.I) =
          (Real.log 2 : ℂ) +
            (((2 * k + 1 : ℤ) : ℝ) * Real.pi : ℝ) * Complex.I := by
      calc
        (Real.log 2 : ℂ) *
            ((1 : ℂ) +
              (((2 * k + 1 : ℤ) : ℝ) * Real.pi / Real.log 2 : ℝ) * Complex.I) =
            (Real.log 2 : ℂ) +
              (Real.log 2 : ℂ) *
                (((2 * k + 1 : ℤ) : ℝ) * Real.pi / Real.log 2 : ℝ) *
                  Complex.I := by ring
        _ = (Real.log 2 : ℂ) +
              (((2 * k + 1 : ℤ) : ℝ) * Real.pi : ℝ) * Complex.I := by
          rw [log_two_mul_div]
    have hminusarg :
        (Real.log 2 : ℂ) *
            ((-1 : ℂ) +
              (((2 * k + 1 : ℤ) : ℝ) * Real.pi / Real.log 2 : ℝ) * Complex.I) =
          -(Real.log 2 : ℂ) +
            (((2 * k + 1 : ℤ) : ℝ) * Real.pi : ℝ) * Complex.I := by
      calc
        (Real.log 2 : ℂ) *
            ((-1 : ℂ) +
              (((2 * k + 1 : ℤ) : ℝ) * Real.pi / Real.log 2 : ℝ) * Complex.I) =
            -(Real.log 2 : ℂ) +
              (Real.log 2 : ℂ) *
                (((2 * k + 1 : ℤ) : ℝ) * Real.pi / Real.log 2 : ℝ) *
                  Complex.I := by ring
        _ = -(Real.log 2 : ℂ) +
              (((2 * k + 1 : ℤ) : ℝ) * Real.pi : ℝ) * Complex.I := by
          rw [log_two_mul_div]
    constructor
    · rw [hplusarg, exp_pair_eq_cosh, cosh_odd_pi_shift, cosh_log_two]
      norm_num
    · rw [hminusarg, exp_pair_eq_cosh, cosh_odd_pi_shift]
      rw [Complex.cosh_neg, cosh_log_two]
      norm_num

end MathlibPlus.Analysis
