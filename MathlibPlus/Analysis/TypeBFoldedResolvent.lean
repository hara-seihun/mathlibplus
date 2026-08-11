import Mathlib

namespace MathlibPlus.Analysis.TypeBFoldedResolvent

/--
The exact negative minor from legacy claim 19459 (packet R-0286).  The
indicator in the source kernel is represented by a real-valued `if`.
The network-level consequence is not encoded because no network object is
part of the admitted claim's formal interface.
-/
theorem typeBFoldedMinor (c y₁ y₂ z₁ z₂ : ℝ)
    (_hc : 0 < c)
    (_hz₁ : 0 < z₁) (_hy₁ : 0 < y₁) (_hz₂ : 0 < z₂) (_hy₂ : 0 < y₂)
    (h₁₂ : z₁ < y₁) (h₂₃ : y₁ < z₂) (h₃₄ : z₂ < y₂) :
    let K : ℝ → ℝ → ℝ := fun y z =>
      Real.exp (-(z - y) / c) * (if z ≥ y then 1 else 0) +
        Real.exp (-(z + y) / c)
    let M : Matrix (Fin 2) (Fin 2) ℝ :=
      !![K y₁ z₁, K y₁ z₂; K y₂ z₁, K y₂ z₂]
    Matrix.det M = -Real.exp (-(z₁ + y₂ + z₂ - y₁) / c) ∧
      Matrix.det M < 0 := by
  dsimp
  have hz₁y₁ : ¬ z₁ ≥ y₁ := not_le_of_gt h₁₂
  have hy₁z₂ : z₂ ≥ y₁ := le_of_lt h₂₃
  have hz₁y₂ : ¬ z₁ ≥ y₂ :=
    not_le_of_gt (lt_trans h₁₂ (lt_trans h₂₃ h₃₄))
  have hz₂y₂ : ¬ z₂ ≥ y₂ := not_le_of_gt h₃₄
  have hdet :
      Real.exp (-(z₁ + y₁) / c) * Real.exp (-(z₂ + y₂) / c) -
          (Real.exp (-(z₂ - y₁) / c) + Real.exp (-(z₂ + y₁) / c)) *
            Real.exp (-(z₁ + y₂) / c) =
        -Real.exp (-(z₁ + y₂ + z₂ - y₁) / c) := by
    have h₁ :
        Real.exp (-(z₁ + y₁) / c) * Real.exp (-(z₂ + y₂) / c) =
          Real.exp (-(z₁ + y₁) / c + -(z₂ + y₂) / c) := by
      rw [Real.exp_add]
    have h₂ :
        Real.exp (-(z₂ - y₁) / c) * Real.exp (-(z₁ + y₂) / c) =
          Real.exp (-(z₂ - y₁) / c + -(z₁ + y₂) / c) := by
      rw [Real.exp_add]
    have h₃ :
        Real.exp (-(z₂ + y₁) / c) * Real.exp (-(z₁ + y₂) / c) =
          Real.exp (-(z₂ + y₁) / c + -(z₁ + y₂) / c) := by
      rw [Real.exp_add]
    calc
      _ = Real.exp (-(z₁ + y₁) / c + -(z₂ + y₂) / c) -
            (Real.exp (-(z₂ - y₁) / c) + Real.exp (-(z₂ + y₁) / c)) *
              Real.exp (-(z₁ + y₂) / c) := by rw [h₁]
      _ = Real.exp (-(z₁ + y₁) / c + -(z₂ + y₂) / c) -
            (Real.exp (-(z₂ - y₁) / c + -(z₁ + y₂) / c) +
              Real.exp (-(z₂ + y₁) / c + -(z₁ + y₂) / c)) := by
        rw [add_mul, h₂, h₃]
      _ = -Real.exp (-(z₁ + y₂ + z₂ - y₁) / c) := by
        rw [show -(z₁ + y₁) / c + -(z₂ + y₂) / c =
              -(z₂ + y₁) / c + -(z₁ + y₂) / c by ring]
        rw [show -(z₂ - y₁) / c + -(z₁ + y₂) / c =
              -(z₁ + y₂ + z₂ - y₁) / c by ring]
        ring
  have hmatrix :
      (!![Real.exp (-(z₁ - y₁) / c) *
              (if z₁ ≥ y₁ then 1 else 0) + Real.exp (-(z₁ + y₁) / c),
          Real.exp (-(z₂ - y₁) / c) *
              (if z₂ ≥ y₁ then 1 else 0) + Real.exp (-(z₂ + y₁) / c);
         Real.exp (-(z₁ - y₂) / c) *
              (if z₁ ≥ y₂ then 1 else 0) + Real.exp (-(z₁ + y₂) / c),
          Real.exp (-(z₂ - y₂) / c) *
              (if z₂ ≥ y₂ then 1 else 0) + Real.exp (-(z₂ + y₂) / c)] :
          Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.exp (-(z₁ + y₁) / c),
          Real.exp (-(z₂ - y₁) / c) + Real.exp (-(z₂ + y₁) / c);
         Real.exp (-(z₁ + y₂) / c), Real.exp (-(z₂ + y₂) / c)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Fin.isValue, hz₁y₁, hy₁z₂, hz₁y₂, hz₂y₂,
        if_false, if_true, mul_zero, zero_add, mul_one, one_mul, add_zero]
  rw [hmatrix]
  constructor
  · simpa [Matrix.det_fin_two] using hdet
  · calc
      Matrix.det
          (!![Real.exp (-(z₁ + y₁) / c),
              Real.exp (-(z₂ - y₁) / c) + Real.exp (-(z₂ + y₁) / c);
             Real.exp (-(z₁ + y₂) / c), Real.exp (-(z₂ + y₂) / c)] :
            Matrix (Fin 2) (Fin 2) ℝ) =
          -Real.exp (-(z₁ + y₂ + z₂ - y₁) / c) := by
            simpa [Matrix.det_fin_two] using hdet
      _ < 0 := neg_lt_zero.mpr (Real.exp_pos _)

end MathlibPlus.Analysis.TypeBFoldedResolvent
