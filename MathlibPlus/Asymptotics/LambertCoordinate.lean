import Mathlib

namespace MathlibPlus.Asymptotics

/-- The exact Lambert-coordinate relations and normalization identity from claim 8783.
The interpolation's principal `W₀` branch is represented by its positive-real
inverse property; the theorem records the resulting value relation and the
displayed logarithmic normalization without asserting the surrounding
asymptotic claim. -/
theorem logarithmicCoordinateIdentities_claim8783
    (κ j T w : ℝ) (W₀ : ℝ → ℝ)
    (hκ : 0 < κ) (hj : 0 < j) (hT : 0 < T)
    (hW₀ : ∀ x : ℝ, 0 < x →
      0 < W₀ x ∧ W₀ x * Real.exp (W₀ x) = x)
    (hw : w = W₀ (j / κ)) :
    let a : ℝ := 1 / (4 * κ * Real.exp w)
    let L_T : ℝ := Real.log (T / (2 * κ))
    (j = κ * w * Real.exp w) ∧
      (1 / T) / (2 * a) = Real.exp (w - L_T) := by
  dsimp
  have hrel : W₀ (j / κ) * Real.exp (W₀ (j / κ)) = j / κ :=
    (hW₀ (j / κ) (div_pos hj hκ)).2
  rw [← hw] at hrel
  constructor
  · calc
      j = κ * (j / κ) := by field_simp
      _ = κ * (w * Real.exp w) := by rw [← hrel]
      _ = κ * w * Real.exp w := by ring
  · have harg : 0 < T / (2 * κ) := by positivity
    rw [Real.exp_sub, Real.exp_log harg]
    field_simp
    norm_num

end MathlibPlus.Asymptotics
