import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Tail estimate for the second adjacent gap. -/
def claim3056_tailEstimate : Prop :=
  ∀ (A : ℂ → ℂ) (a c r : ℕ → ℝ) (α : ℝ),
    (∀ z : ℂ,
      HasSum (fun n : ℕ => (a n : ℂ) * z ^ n) (A z)) →
    Differentiable ℂ A →
    (∀ n : ℕ, 0 < a n) →
    0 < α →
    (∀ n : ℕ, 1 ≤ n →
      (a n) ^ 2 >
        ((n + 1 : ℝ) / (n : ℝ)) * a (n - 1) * a (n + 1)) →
    (∀ n : ℕ, 1 ≤ n → r n = a n / a (n - 1)) →
    (∀ n : ℕ,
      c n = ∑' j : ℕ, a (n + 1 + j) * α ^ j) →
    let δ : ℝ := α * r 1
    (∀ k : ℕ, 2 ≤ k →
        c (k - 1) - r (k + 1) * c (k - 2) >
          a (k - 1) * r (k + 1) *
            ((1 : ℝ) / (k : ℝ) -
              (α * r k) ^ 2 / (1 - α * r k))) ∧
      (δ ^ 2 + δ < 1 →
        ∀ k : ℕ, 2 ≤ k →
          ((1 : ℝ) / (k : ℝ) -
              (α * r k) ^ 2 / (1 - α * r k) ≥
            ((k : ℝ) - δ - δ ^ 2) /
              ((k : ℝ) * ((k : ℝ) - δ)) ∧
            0 < ((k : ℝ) - δ - δ ^ 2) /
              ((k : ℝ) * ((k : ℝ) - δ)) ∧
            0 < a k * c (k - 1) - a (k + 1) * c (k - 2)))

end MathlibPlus.Open.Analysis
