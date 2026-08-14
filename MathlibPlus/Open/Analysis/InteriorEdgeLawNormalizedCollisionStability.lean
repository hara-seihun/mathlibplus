import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Exact admitted collision-stability estimate for a finite family of weights. -/
def normalized_collision_stability
    (α : Type*) (I : Finset α) (w m : α → ℝ) (δ : ℝ) : Prop :=
  (∀ i ∈ I, 0 ≤ w i) →
  0 < (∑ i ∈ I, w i) →
  0 ≤ δ →
  δ < 1 →
  (∀ i ∈ I, (1 - δ) * w i ≤ m i) →
  (∀ i ∈ I, m i ≤ (1 + δ) * w i) →
    (((1 - δ) / (1 + δ)) ^ 2 *
          ((∑ i ∈ I, w i ^ 2) / (∑ i ∈ I, w i) ^ 2) ≤
        (∑ i ∈ I, m i ^ 2) / (∑ i ∈ I, m i) ^ 2 ∧
      (∑ i ∈ I, m i ^ 2) / (∑ i ∈ I, m i) ^ 2 ≤
        ((1 + δ) / (1 - δ)) ^ 2 *
          ((∑ i ∈ I, w i ^ 2) / (∑ i ∈ I, w i) ^ 2))

end MathlibPlus.Open.Analysis
