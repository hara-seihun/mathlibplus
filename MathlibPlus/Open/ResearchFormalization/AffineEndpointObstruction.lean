import Mathlib

namespace MathlibPlus.Open.AffineEndpointObstruction

open Matrix

noncomputable def t (n : ℕ) : ℝ := Real.exp (-(3 : ℝ) * n / 2)
noncomputable def a (n : ℕ) : ℝ := 1 / 2 + t n
noncomputable def m (n : ℕ) : ℝ := 1 / 2 + 3 / 2 * t n
noncomputable def b (n : ℕ) : ℝ := 1 / 2 + 2 * t n

noncomputable def affineMatrix (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1; a n, b n]

def claim59570 : Prop :=
  ∀ n : ℕ,
    a n < m n ∧ m n < b n ∧
    Matrix.det (affineMatrix n) = b n - a n ∧
    b n - a n = t n ∧
    |a n - 1 / 2| = t n ∧ |b n - 1 / 2| = 2 * t n ∧
    1 / 2 < a n ∧ 1 / 2 < b n

end MathlibPlus.Open.AffineEndpointObstruction
