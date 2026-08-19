import MathlibPlus.Open.Analysis.WeightedGreenBatch

namespace MathlibPlus.Open.Analysis.K0105

/-- Positive leading continuants and pivots, with the Jacobi continuant recurrence. -/
def positiveJacobiContinuantsAndPivots8583 : Prop :=
  ∀ (n : ℕ) (α β : ℕ → ℝ),
    positiveWeightedGreenJacobi n α β →
      (∀ k : ℕ, k ≤ n →
        0 < weightedGreenLeadingDet n α β k) ∧
      (∀ k : ℕ, k < n →
        0 < weightedGreenPivot n α β k) ∧
      (∀ k : ℕ, 1 ≤ k → k + 1 ≤ n →
        weightedGreenLeadingDet n α β (k + 1) =
          α k * weightedGreenLeadingDet n α β k -
            β k ^ 2 * weightedGreenLeadingDet n α β (k - 1))

end MathlibPlus.Open.Analysis.K0105
