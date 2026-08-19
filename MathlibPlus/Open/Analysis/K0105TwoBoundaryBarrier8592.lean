import MathlibPlus.Open.Analysis.WeightedGreenBatch

namespace MathlibPlus.Open.Analysis.K0105

/-- The two-boundary resistance barrier on a source-free Jacobi block. -/
def twoBoundaryPositivityBarrier8592 : Prop :=
  ∀ (n : ℕ) (α β : ℕ → ℝ) (a b : ℕ),
    positiveWeightedGreenJacobi n α β →
    1 ≤ a → a ≤ b → b ≤ n - 2 →
    (∀ l : ℕ, a ≤ l → l ≤ b →
      weightedGreenSource α β l = 0) →
    (∀ k : ℕ, a - 1 ≤ k → k ≤ b + 1 →
      0 < weightedGreenY n α β a k) →
    ∀ k : ℕ, a ≤ k → k ≤ b →
      -1 /
          (β (k + 1) *
            (weightedGreenResistance a β (b + 1) -
              weightedGreenResistance a β k)) <
        weightedGreenPivot n α β k / β (k + 1) - 1 ∧
      weightedGreenPivot n α β k / β (k + 1) - 1 ≤
        1 /
          (β (k + 1) * weightedGreenResistance a β k)

end MathlibPlus.Open.Analysis.K0105
