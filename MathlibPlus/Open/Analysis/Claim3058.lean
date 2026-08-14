import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def claim3058_genericAllShiftRankTwoEndpoint : Prop :=
  ∀ (A : ℝ → ℝ) (a : ℕ → ℝ) (α : ℝ),
    (∀ n : ℕ, 0 < a n) →
    (∀ x : ℝ, HasSum (fun n : ℕ => a n * x ^ n) (A x)) →
    0 < α →
    (∀ n : ℕ, 1 ≤ n →
      a n ^ 2 > ((n + 1 : ℝ) / (n : ℝ)) * a (n - 1) * a (n + 1)) →
    let δ : ℝ := α * a 1 / a 0
    δ ^ 2 + δ < 1 →
    2 * a 0 > A α →
    ∀ k : ℕ, 1 ≤ k →
      let b : ℝ := A α
      let c : ℕ → ℝ := fun n => ∑' j : ℕ, a (n + 1 + j) * α ^ j
      let d : ℤ → ℝ := fun n =>
        if h : 0 ≤ n then c n.toNat else b * α ^ ((-n).toNat - 1)
      let Δ₀ : ℝ := d (k - 1) * d (k - 1) - d k * d (k - 2)
      let Δ₁ : ℝ := d k * d (k - 1) - d (k + 1) * d (k - 2)
      let Δ₂ : ℝ := d k * d k - d (k + 1) * d (k - 1)
      0 < Δ₀ ∧ 0 < Δ₁ ∧ 0 < Δ₂ ∧ α * Δ₁ < Δ₀ ∧ α * Δ₂ < Δ₁

end MathlibPlus.Open.Analysis
