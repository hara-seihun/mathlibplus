import MathlibPlus.Open.ResearchFormalizationBatch

namespace MathlibPlus.Algebra

/-- Claim 2578, source-bound to the canonical fixed-at-zero Chebyshev family:
the degree-one residual is the exact first member of the fixed-degree hierarchy. -/
def scalarWallDegreeOne_claim2578 : Prop :=
  let degreeOne := MathlibPlus.Open.ResearchFormalizationBatch.chebyshevRescaling 1
  let degreeOneResidual :=
    MathlibPlus.Open.ResearchFormalizationBatch.intervalSupNorm degreeOne
  degreeOne.natDegree ≤ 1 ∧
    degreeOne.eval 0 = 1 ∧
    degreeOneResidual =
      2 / ((9 : ℝ) + ((9 : ℝ)⁻¹)) ∧
    degreeOneResidual = 9 / 41 ∧
    (∀ n : ℕ,
      MathlibPlus.Open.ResearchFormalizationBatch.intervalSupNorm
          (MathlibPlus.Open.ResearchFormalizationBatch.chebyshevRescaling n) =
        2 / ((9 : ℝ) ^ n + ((9 : ℝ) ^ n)⁻¹))

end MathlibPlus.Algebra
