import MathlibPlus.Open.Research.Batch_01a00468_FreeJacobi

namespace MathlibPlus.Open.Research.FormalizationBatch.K0101Claim8530

open MathlibPlus.Open.Research.Batch_01a00468_FreeJacobi

/-- The positive-horizon barrier for the normalized incoming defect of a free
Jacobi block. -/
def positiveHorizonBarrier_claim8530 : Prop :=
  ∀ (a b : ℕ) (c : ℝ) (α β q : ℕ → ℝ),
    freeJacobiData a b c α β q →
      let m : ℕ := b - a + 1
      let d : ℝ := q (a - 1) / c - 1
      d > -1 / ((m + 1 : ℕ) : ℝ)

end MathlibPlus.Open.Research.FormalizationBatch.K0101Claim8530
