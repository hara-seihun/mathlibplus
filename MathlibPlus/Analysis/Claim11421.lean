import Mathlib

namespace MathlibPlus.Analysis.Claim11421

/-- Claim 11421: a nearest phase choice reaches the adverse real ray at every
scale `Y > 1`. -/
theorem phaseChoice_claim11421
    (Y t₀ φ₀ : ℝ) (m₀ : ℂ)
    (hY : 1 < Y)
    (hm : m₀ = (‖m₀‖ : ℂ) * Complex.exp (Complex.I * (φ₀ : ℂ)))
    (_hm0 : m₀ ≠ 0) :
    ∃ k : ℤ, let tY : ℝ := (φ₀ - Real.pi + 2 * Real.pi * k) / Real.log Y
      |tY - t₀| ≤ Real.pi / Real.log Y ∧
      Complex.exp (-Complex.I * (tY : ℂ) * (Real.log Y : ℂ)) * m₀ =
        -(‖m₀‖ : ℂ) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hL : 0 < Real.log Y := Real.log_pos hY
  let L : ℝ := Real.log Y
  let x : ℝ := (t₀ * L - φ₀ + Real.pi) / (2 * Real.pi)
  let k : ℤ := ⌊x + (1 / 2 : ℝ)⌋
  have hk_upper : (k : ℝ) ≤ x + (1 / 2 : ℝ) := by
    exact Int.floor_le (x + (1 / 2 : ℝ))
  have hk_lower : x - (1 / 2 : ℝ) < (k : ℝ) := by
    have h := Int.lt_floor_add_one (x + (1 / 2 : ℝ))
    linarith
  have hr_lower : -(1 / 2 : ℝ) ≤ x - (k : ℝ) := by linarith
  have hr_upper : x - (k : ℝ) ≤ (1 / 2 : ℝ) := by linarith
  have htwopi : 0 ≤ 2 * Real.pi := by positivity
  have hmul_upper : 2 * Real.pi * (x - (k : ℝ)) ≤ Real.pi := by
    calc
      2 * Real.pi * (x - (k : ℝ)) ≤ 2 * Real.pi * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hr_upper htwopi
      _ = Real.pi := by ring
  have hmul_lower : -Real.pi ≤ 2 * Real.pi * (x - (k : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hr_lower htwopi
    nlinarith [h]
  have hd :
      |-2 * Real.pi * (x - (k : ℝ))| ≤ Real.pi := by
    rw [abs_le]
    constructor <;> linarith
  have hrel :
      φ₀ - Real.pi + 2 * Real.pi * (k : ℝ) - t₀ * L =
        -2 * Real.pi * (x - (k : ℝ)) := by
    dsimp [x]
    field_simp [Real.pi_ne_zero]
    ring
  refine ⟨k, ?_⟩
  dsimp [L]
  constructor
  · have htd :
        (φ₀ - Real.pi + 2 * Real.pi * (k : ℝ)) / Real.log Y - t₀ =
          (-2 * Real.pi * (x - (k : ℝ))) / Real.log Y := by
      rw [← hrel]
      field_simp [ne_of_gt hL]
      ring
    rw [htd, abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right hd (le_of_lt hL)
  · have hexp :
        Complex.exp
            (-Complex.I *
                (((φ₀ - Real.pi + 2 * Real.pi * (k : ℝ)) / Real.log Y : ℝ) : ℂ) *
                (Real.log Y : ℂ)) *
            Complex.exp (Complex.I * (φ₀ : ℂ)) = -1 := by
      have hkexp := Complex.exp_int_mul_two_pi_mul_I (-k)
      have hsum :
          -Complex.I *
              (((φ₀ - Real.pi + 2 * Real.pi * (k : ℝ)) / Real.log Y : ℝ) : ℂ) *
              (Real.log Y : ℂ) + Complex.I * (φ₀ : ℂ) =
            (Real.pi : ℂ) * Complex.I + ((-k : ℤ) : ℂ) *
              (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast
        field_simp [ne_of_gt hL]
        ring
      rw [← Complex.exp_add, hsum, Complex.exp_add,
        Complex.exp_pi_mul_I, hkexp]
      ring
    calc
      Complex.exp
          (-Complex.I *
              (((φ₀ - Real.pi + 2 * Real.pi * (k : ℝ)) / Real.log Y : ℝ) : ℂ) *
              (Real.log Y : ℂ)) * m₀ =
          Complex.exp
              (-Complex.I *
                  (((φ₀ - Real.pi + 2 * Real.pi * (k : ℝ)) / Real.log Y : ℝ) : ℂ) *
                  (Real.log Y : ℂ)) *
            ((‖m₀‖ : ℂ) * Complex.exp (Complex.I * (φ₀ : ℂ))) := by
        congr 1
      _ = (‖m₀‖ : ℂ) *
            (Complex.exp
                (-Complex.I *
                    (((φ₀ - Real.pi + 2 * Real.pi * (k : ℝ)) / Real.log Y : ℝ) : ℂ) *
                    (Real.log Y : ℂ)) *
              Complex.exp (Complex.I * (φ₀ : ℂ))) := by ring
      _ = (‖m₀‖ : ℂ) * (-1) := by rw [hexp]
      _ = -(‖m₀‖ : ℂ) := by ring

end MathlibPlus.Analysis.Claim11421
