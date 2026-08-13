import Mathlib

namespace MathlibPlus.Analysis.Claim4163

/-- The squared modulus of the reciprocal Cayley denominator and the normalized
exterior-square rate, written in real coordinates.  The nonzero denominator is
made explicit; no zero-set or analytic interpretation is added. -/
theorem cayley_peak_coordinates_claim4163
    (β γ : ℝ) (hρ : (β : ℂ) + (γ : ℂ) * Complex.I ≠ 1) :
    let ρ : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I
    let a : ℂ := ρ / (ρ - 1)
    let b : ℂ := 1 / (ρ - 1)
    let d : ℝ := ‖b‖ ^ 2
    let κ : ℝ := ‖a‖ ^ 2 - 1
    d = 1 / ((β - 1) ^ 2 + γ ^ 2) ∧
      κ = (2 * β - 1) / ((β - 1) ^ 2 + γ ^ 2) := by
  dsimp
  let ρ : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I
  have hne : ρ - 1 ≠ 0 := by
    intro hz
    apply hρ
    exact sub_eq_zero.mp hz
  have hden : Complex.normSq (ρ - 1) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hne)
  have hden_coord : Complex.normSq (ρ - 1) = (β - 1) ^ 2 + γ ^ 2 := by
    simp [ρ, Complex.normSq_apply]
    ring
  have hρ_norm : Complex.normSq ρ = β ^ 2 + γ ^ 2 := by
    simp [ρ, Complex.normSq_apply]
    ring
  have hcoord : (β - 1) ^ 2 + γ ^ 2 ≠ 0 := by
    intro h
    apply hden
    rw [hden_coord, h]
  change ‖(1 / (ρ - 1))‖ ^ 2 = 1 / ((β - 1) ^ 2 + γ ^ 2) ∧
    ‖ρ / (ρ - 1)‖ ^ 2 - 1 =
      (2 * β - 1) / ((β - 1) ^ 2 + γ ^ 2)
  constructor
  · rw [Complex.sq_norm, Complex.normSq_div, Complex.normSq_one,
      hden_coord]
  · rw [Complex.sq_norm, Complex.normSq_div, hρ_norm, hden_coord]
    field_simp [hcoord]
    ring

end MathlibPlus.Analysis.Claim4163
