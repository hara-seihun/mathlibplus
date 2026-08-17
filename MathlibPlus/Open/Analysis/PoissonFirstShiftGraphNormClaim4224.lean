import MathlibPlus.Open.Analysis.ResearchFormalizationBatch_01a001aa

namespace MathlibPlus.Open.Analysis.PoissonFirstShiftGraphNormClaim4224

/-- The Poisson zeroth, first-shift, and graph norm square identities on the
reviewed finite graph-norm carrier. -/
def poissonFirstShiftGraphNorm : Prop :=
  ∀ (x : ℝ),
    0 < x →
    ∀ (u : ℕ → ℂ),
      poissonGraphFinite_claim4227 x u →
      poissonM0_claim4227 x u ^ 2 =
          ∑' n : ℕ, poissonWeight_claim4227 x n * ‖u n‖ ^ 2 ∧
        poissonM1_claim4227 x u ^ 2 =
          ∑' n : ℕ, poissonWeight_claim4227 x n * ‖u (n + 1)‖ ^ 2 ∧
        poissonGraphNorm_claim4227 x u ^ 2 =
          poissonM0_claim4227 x u ^ 2 + poissonM1_claim4227 x u ^ 2

end MathlibPlus.Open.Analysis.PoissonFirstShiftGraphNormClaim4224
