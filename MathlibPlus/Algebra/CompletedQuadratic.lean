import Mathlib

/-!
# Completed quadratic and primitive quotient

This file records the algebraic normalization and the explicit positive
non-real-rooted quadratic witness from admitted claims 13322 and 13330.
-/

namespace MathlibPlus.Algebra.CompletedQuadratic

noncomputable section

/-- The quadratic polynomial before completion. -/
def P (sigma pi z : ℝ) : ℝ := 1 + sigma * z + pi * z ^ 2

/-- The completed quadratic normalized at `alpha`. -/
def A (alpha b sigma pi z : ℝ) : ℝ :=
  b * P sigma pi z / P sigma pi alpha

/-- The polynomial primitive quotient, including its value at `alpha`. -/
def T (alpha b sigma pi z : ℝ) : ℝ :=
  b / P sigma pi alpha * (sigma + alpha * pi + pi * z)

theorem P_alpha_pos {alpha sigma pi : ℝ} (halpha : 0 < alpha)
    (hsigma : 0 < sigma) (hpi : 0 < pi) :
    0 < P sigma pi alpha := by
  dsimp [P]
  nlinarith [sq_nonneg alpha]

theorem A_at_alpha {alpha b sigma pi : ℝ} (halpha : 0 < alpha)
    (_hb : 0 < b) (hsigma : 0 < sigma) (hpi : 0 < pi) :
    A alpha b sigma pi alpha = b := by
  have hP : P sigma pi alpha ≠ 0 := ne_of_gt (P_alpha_pos halpha hsigma hpi)
  dsimp [A]
  field_simp [hP]

theorem T_mul_sub_eq_A_sub {alpha b sigma pi z : ℝ}
    (halpha : 0 < alpha) (_hb : 0 < b) (hsigma : 0 < sigma) (hpi : 0 < pi) :
    (z - alpha) * T alpha b sigma pi z = A alpha b sigma pi z - b := by
  have hP : P sigma pi alpha ≠ 0 := ne_of_gt (P_alpha_pos halpha hsigma hpi)
  dsimp [T, A, P]
  field_simp [hP]
  ring

theorem T_eq_div {alpha b sigma pi z : ℝ}
    (halpha : 0 < alpha) (_hb : 0 < b) (hsigma : 0 < sigma) (hpi : 0 < pi)
    (hz : z ≠ alpha) :
    T alpha b sigma pi z =
      (A alpha b sigma pi z - b) / (z - alpha) := by
  apply (eq_div_iff (sub_ne_zero.mpr hz)).2
  rw [mul_comm]
  exact T_mul_sub_eq_A_sub halpha _hb hsigma hpi

/-! The exact witness at `alpha = 1/4`, `b = 1/2`, `sigma = 2`, and
`pi = 101/100`. -/

/-- The witness quadratic, now viewed over `ℂ` so its two roots are explicit. -/
def counterfeitP (z : ℂ) : ℂ :=
  1 + 2 * z + (101 / 100) * z ^ 2

/-- The completed witness obtained by normalizing `counterfeitP` at `1/4`. -/
def counterfeitA (z : ℂ) : ℂ :=
  (1 / 2) * counterfeitP z / counterfeitP (1 / 4)

/-- The displayed primitive quotient of the witness. -/
def counterfeitT (z : ℂ) : ℂ :=
  2 * (404 * z + 901) / 2501

def counterfeitRootPlus : ℂ := (-100 + 10 * Complex.I) / 101

def counterfeitRootMinus : ℂ := (-100 - 10 * Complex.I) / 101

theorem counterfeitP_factor (z : ℂ) :
    counterfeitP z =
      (101 / 100) *
        ((z - counterfeitRootPlus) * (z - counterfeitRootMinus)) := by
  dsimp [counterfeitP, counterfeitRootPlus, counterfeitRootMinus]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem counterfeitP_roots (z : ℂ) :
    counterfeitP z = 0 ↔
      z = counterfeitRootPlus ∨ z = counterfeitRootMinus := by
  rw [counterfeitP_factor]
  constructor
  · intro hz
    have htail :
        (z - counterfeitRootPlus) * (z - counterfeitRootMinus) = 0 := by
      exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
    rcases mul_eq_zero.mp htail with hplus | hminus
    · exact Or.inl (sub_eq_zero.mp hplus)
    · exact Or.inr (sub_eq_zero.mp hminus)
  · rintro (rfl | rfl) <;> simp

theorem counterfeitA_expanded (z : ℂ) :
    counterfeitA z = 8 * (101 * z ^ 2 + 200 * z + 100) / 2501 := by
  dsimp [counterfeitA, counterfeitP]
  norm_num
  ring

theorem counterfeitA_at_alpha : counterfeitA (1 / 4) = (1 / 2 : ℂ) := by
  rw [counterfeitA_expanded]
  norm_num

theorem counterfeitT_is_primitive_quotient (z : ℂ) :
    counterfeitA z - (1 / 2 : ℂ) =
      (z - 1 / 4) * counterfeitT z := by
  rw [counterfeitA_expanded]
  dsimp [counterfeitT]
  ring

theorem counterfeit_discriminant :
    (2 : ℝ) ^ 2 - 4 * (101 / 100 : ℝ) = -(1 / 25 : ℝ) := by
  norm_num

theorem counterfeit_roots_are_nonreal :
    (counterfeitRootPlus.im ≠ 0) ∧ (counterfeitRootMinus.im ≠ 0) := by
  constructor <;> norm_num [counterfeitRootPlus, counterfeitRootMinus]

theorem counterfeit_coefficients_positive :
    (0 : ℝ) < 1 ∧
    (0 : ℝ) < 2 ∧
    (0 : ℝ) < (101 / 100 : ℝ) ∧
    (0 : ℝ) < (8 * 100 / 2501 : ℝ) ∧
    (0 : ℝ) < (8 * 200 / 2501 : ℝ) ∧
    (0 : ℝ) < (8 * 101 / 2501 : ℝ) ∧
    (0 : ℝ) < (2 * 901 / 2501 : ℝ) ∧
    (0 : ℝ) < (2 * 404 / 2501 : ℝ) := by
  norm_num

end

end MathlibPlus.Algebra.CompletedQuadratic
