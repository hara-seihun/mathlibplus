import Mathlib

namespace MathlibPlus.Algebra.ClaimIdentities

/-- Claim 13800: exact exponent gap and its consequence below `η = 1`. -/
theorem exactExponentGap (δ η : ℝ) :
    ((1 + δ - η) - (δ - 1) = 2 - η) ∧
      (η < 1 →
        ((1 + δ - η) - (δ - 1) > 1 ∧ δ - 1 < 1 + δ - η)) := by
  constructor
  · ring
  · intro hη
    constructor <;> linarith

/-- Claim 15660: the slope/rate pair recovers the squared height. -/
theorem slopeAndRateRecoverSquaredHeight (β γ d κ : ℝ)
    (hd : d = 1 / ((β - 1) ^ 2 + γ ^ 2))
    (hd0 : d ≠ 0)
    (hκ : κ = (2 * β - 1) * d) :
    γ ^ 2 = 1 / d - (1 - κ / d) ^ 2 / 4 := by
  have hden : (β - 1) ^ 2 + γ ^ 2 ≠ 0 := by
    intro hden
    rw [hden] at hd
    norm_num at hd
    exact hd0 hd
  have hprod : d * ((β - 1) ^ 2 + γ ^ 2) = 1 := by
    rw [hd]
    field_simp [hden]
  rw [hκ]
  field_simp [hd0]
  nlinarith [hprod]

/-- Claim 1427: exact target improvements in the historical claim.
Finite decimals are represented exactly in `ℚ`. -/
theorem exactTargetImprovements :
    let target : ℚ := 0.2043672
    let historical : ℚ := 0.1853
    let baseline : ℚ := 0.2043
    target - historical = 11917 / 625000 ∧
      target - baseline = 42 / 625000 := by
  norm_num

/-- Claim 11711: a symmetric two-way coupling contributes twice its squared
off-diagonal entry to the trace of the square. -/
theorem twoWayCouplingTrace (a e b : ℝ) :
    Matrix.trace ((!![a, e; e, b] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2) =
      a ^ 2 + b ^ 2 + 2 * e ^ 2 := by
  simp [Matrix.trace, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The trace contribution is strict when the coupling is nonzero. -/
theorem twoWayCouplingTrace_strict (a e b : ℝ) (he : e ≠ 0) :
    a ^ 2 + b ^ 2 <
      Matrix.trace ((!![a, e; e, b] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2) := by
  rw [twoWayCouplingTrace]
  nlinarith [sq_pos_of_ne_zero he]

end MathlibPlus.Algebra.ClaimIdentities
