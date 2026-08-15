import Mathlib

namespace MathlibPlus.Open.Analysis

/--
The first adjacent divided-difference gap is positive under the
ultra-Turán contraction.
-/
def claim3055_firstAdjacentGapPositive : Prop :=
  ∀ (A : ℂ → ℂ) (a c r : ℕ → ℝ) (α : ℝ) (k : ℕ),
    (∀ z : ℂ, A z = ∑' n : ℕ, (a n : ℂ) * z ^ n) →
    Differentiable ℂ A →
    0 < α →
    (∀ n : ℕ, 0 < a n) →
    (∀ n : ℕ, c n = ∑' j : ℕ, a (n + 1 + j) * α ^ j) →
    (∀ n : ℕ, 1 ≤ n → r n = a n / a (n - 1)) →
    (∀ n : ℕ,
      1 ≤ n →
        a n ^ 2 > (((n : ℝ) + 1) / (n : ℝ)) * a (n - 1) * a (n + 1)) →
    1 ≤ k →
    let w : ℕ → ℝ := fun j => a (k + 1 + j) * α ^ j / c k
    0 < c k ∧
      (∀ j : ℕ, 0 < w j) ∧
      Summable w ∧
      (∑' j : ℕ, w j = 1) ∧
      Summable (fun j : ℕ => w j * r (k + 2 + j)) ∧
      c (k + 1) / c k = ∑' j : ℕ, w j * r (k + 2 + j) ∧
      c (k + 1) / c k < r (k + 2) ∧
      r (k + 2) < r k ∧
      c k * a k - c (k + 1) * a (k - 1) > 0

end MathlibPlus.Open.Analysis
