import Mathlib

namespace MathlibPlus.Algebra.Claim39916

/-- The vertical correction in the rank-one shear formula. -/
def rho {H : Type*} [Mul H] (χ : H → ℝ) (c : H → ℝ) (q : ℝ → ℝ)
    (h k : H) (a u : ℝ) : ℝ :=
  c (h * k) * q (u + χ h * a) - χ h * c k * q a - c h * q u

/-- The additive normalized-derivative core, written as the three displayed
vertical contributions of claim 39916. -/
def normalizedDerivative {H : Type*} [Mul H]
    (χ : H → ℝ) (c : H → ℝ) (q : ℝ → ℝ)
    (h k : H) (x w : ℝ × ℝ) : ℝ × ℝ :=
  w + (0, c (h * k) * q (w.1 + χ h * x.1)) -
    (0, χ h * c k * q x.1) - (0, c h * q w.1)

theorem normalizedDerivative_eq_verticalTranslation
    {H : Type*} [Mul H] (χ : H → ℝ) (c : H → ℝ) (q : ℝ → ℝ)
    (h k : H) (a b u v : ℝ) :
    normalizedDerivative χ c q h k (a, b) (u, v) =
      (u, v + rho χ c q h k a u) := by
  ext <;> dsimp [normalizedDerivative, rho] <;> ring

theorem normalizedDerivative_independent_of_second_base_coordinate
    {H : Type*} [Mul H] (χ : H → ℝ) (c : H → ℝ) (q : ℝ → ℝ)
    (h k : H) (a b b' u v : ℝ) :
    normalizedDerivative χ c q h k (a, b) (u, v) =
      normalizedDerivative χ c q h k (a, b') (u, v) := by
  rfl

end MathlibPlus.Algebra.Claim39916
