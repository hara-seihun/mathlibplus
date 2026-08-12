import Mathlib

namespace MathlibPlus.Algebra.Claim19351

/-- Claim 19351: the displayed cross-ratio is strictly increasing on `[0, 1]`. -/
theorem crossRatioVariation_claim19351 :
    let X : ℝ → ℝ :=
      (fun _ : ℝ => (8 : ℝ)) * ((fun x => x - 7) * (fun x => x + 7)) /
        ((fun x => x + 5) * (fun x => 5 * x - 19))
    ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      X ρ = 8 * (ρ - 7) * (ρ + 7) / ((ρ + 5) * (5 * ρ - 19)) ∧
        HasDerivAt X
          (48 * (ρ + 1) * (ρ + 49) /
            ((ρ + 5) ^ 2 * (5 * ρ - 19) ^ 2)) ρ ∧
        0 < 48 * (ρ + 1) * (ρ + 49) /
          ((ρ + 5) ^ 2 * (5 * ρ - 19) ^ 2) := by
  dsimp only
  intro ρ h0 h1
  have hp : ρ + 5 ≠ 0 := by linarith
  have hq : 5 * ρ - 19 ≠ 0 := by linarith
  have hp5 : (ρ + 5) * (5 * ρ - 19) ≠ 0 := mul_ne_zero hp hq
  have hρ : HasDerivAt (fun x : ℝ => x) 1 ρ := hasDerivAt_id ρ
  have hleft : HasDerivAt (fun x : ℝ => x - 7) 1 ρ := hρ.sub_const 7
  have hright : HasDerivAt (fun x : ℝ => x + 7) 1 ρ := hρ.add_const 7
  have hnum := (hasDerivAt_const (x := ρ) 8).mul (hleft.mul hright)
  have hdenleft : HasDerivAt (fun x : ℝ => x + 5) 1 ρ := hρ.add_const 5
  have hdenright : HasDerivAt (fun x : ℝ => 5 * x - 19) 5 ρ := by
    simpa using (hρ.const_mul 5).sub_const 19
  have hden := hdenleft.mul hdenright
  have hquot := hnum.div hden hp5
  have hquot' := hquot
  simp only [Pi.mul_apply, zero_mul, zero_add, one_mul, mul_one] at hquot'
  have hderiv :
      (8 * ((ρ + 7) + (ρ - 7)) * ((ρ + 5) * (5 * ρ - 19)) -
        8 * ((ρ - 7) * (ρ + 7)) *
          ((5 * ρ - 19) + (ρ + 5) * 5)) /
          ((ρ + 5) * (5 * ρ - 19)) ^ 2 =
        48 * (ρ + 1) * (ρ + 49) /
          ((ρ + 5) ^ 2 * (5 * ρ - 19) ^ 2) := by
    field_simp [hp5]
    ring
  rw [hderiv] at hquot'
  constructor
  · simp only [Pi.mul_apply, Pi.div_apply]
    ring
  constructor
  · simpa [Pi.mul_apply, Pi.div_apply] using hquot'
  · have hρ1 : 0 < ρ + 1 := by linarith
    have hρ49 : 0 < ρ + 49 := by linarith
    have hdenpos : 0 < (ρ + 5) ^ 2 * (5 * ρ - 19) ^ 2 := by
      exact mul_pos (sq_pos_of_ne_zero hp) (sq_pos_of_ne_zero hq)
    exact div_pos (by positivity) hdenpos

end MathlibPlus.Algebra.Claim19351
