import Mathlib

namespace MathlibPlus.Open.Analysis

def rankinSelbergSquareOfEisensteinCoefficients : Prop :=
  ∀ (x : ℝ) (s : ℂ), s.re > 1 →
    let τ : ℝ → ℕ → ℂ := fun x k =>
      ∑' p : {p : ℕ × ℕ // p.1 * p.2 = k ∧ 0 < p.1 ∧ 0 < p.2},
        (((p.1.1 : ℂ) / (p.1.2 : ℂ)) ^ (-(x : ℂ) * Complex.I))
    (∑' n : {n : ℕ // 0 < n},
      (τ x n.1)^2 * ((n.1 : ℂ) ^ (-s))) =
      (riemannZeta (s - 2 * Complex.I * (x : ℂ)) *
        riemannZeta (s + 2 * Complex.I * (x : ℂ)) *
        (riemannZeta s)^2) / riemannZeta (2 * s)

end MathlibPlus.Open.Analysis
