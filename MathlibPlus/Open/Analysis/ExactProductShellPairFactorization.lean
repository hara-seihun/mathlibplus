import Mathlib

namespace MathlibPlus.Open

noncomputable section

def exactProductShellPairFactorization : Prop :=
  let x_n : ℕ → ℝ → ℝ := fun n t =>
    Real.pi * (n : ℝ)^2 * Real.exp (2 * t)
  let phi_n : ℕ → ℝ → ℝ := fun n t =>
    2 * Real.exp (t / 2) * x_n n t *
      (2 * x_n n t - 3) * Real.exp (-x_n n t)
  ∀ (n m : ℕ), 0 < n → 0 < m →
    ∀ (y d x : ℝ),
      let k : ℕ := n * m
      let X : ℝ := Real.pi * (k : ℝ) * Real.exp (2 * y)
      let u : ℝ := 2 * d + Real.log ((n : ℝ) / (m : ℝ))
      phi_n n (y + d) * phi_n m (y - d) =
        4 * Real.exp y * X ^ 2 *
          (4 * X ^ 2 - 12 * X * Real.cosh u + 9) *
          Real.exp (-2 * X * Real.cosh u) ∧
        Complex.exp (2 * Complex.I * (x * d : ℂ)) =
          Complex.cpow (((n : ℝ) / (m : ℝ) : ℂ)) (-Complex.I * x) *
            Complex.exp (Complex.I * x * (u : ℂ))

end

end MathlibPlus.Open
