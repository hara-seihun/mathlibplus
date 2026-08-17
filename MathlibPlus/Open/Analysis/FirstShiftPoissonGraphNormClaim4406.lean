import MathlibPlus.Open.Analysis.ResearchFormalizationBatch_01a001aa
import MathlibPlus.Open.Analysis.AdmittedBatch0306D0011

namespace MathlibPlus.Open.Analysis.FirstShiftPoissonGraphNormClaim4406

open MathlibPlus.Open.Analysis.AdmittedBatch0306D0011

noncomputable def finiteMZeroSquared (x : ℝ) (N : ℕ) (u : ℕ → ℂ) : ℝ :=
  Finset.sum (Finset.range (N + 1))
    (fun n => poissonWeight x n * Complex.normSq (u n))

noncomputable def finiteMOneSquared (x : ℝ) (N : ℕ) (u : ℕ → ℂ) : ℝ :=
  Finset.sum (Finset.range N)
    (fun n => poissonWeight x n * Complex.normSq (u (n + 1)))

/-- The first-shift Poisson graph norm identities, together with the reviewed
finite truncations and their nonnegativity on the nonnegative-x carrier. -/
def claim4406 : Prop :=
  ∀ (x : ℝ),
    0 ≤ x →
    ∀ (u : ℕ → ℂ),
      poissonGraphFinite_claim4227 x u →
      poissonM0_claim4227 x u ^ 2 =
          ∑' n : ℕ, poissonWeight_claim4227 x n * ‖u n‖ ^ 2 ∧
        poissonM1_claim4227 x u ^ 2 =
          ∑' n : ℕ, poissonWeight_claim4227 x n * ‖u (n + 1)‖ ^ 2 ∧
        poissonGraphNorm_claim4227 x u ^ 2 =
          poissonM0_claim4227 x u ^ 2 + poissonM1_claim4227 x u ^ 2 ∧
        0 ≤ poissonM0_claim4227 x u ∧
        0 ≤ poissonM1_claim4227 x u ∧
        0 ≤ poissonGraphNorm_claim4227 x u ∧
        ∀ N : ℕ,
          0 ≤ finiteMZeroSquared x N u ∧
          0 ≤ finiteMOneSquared x N u ∧
          0 ≤ finiteGraphNormSquared x N u

end MathlibPlus.Open.Analysis.FirstShiftPoissonGraphNormClaim4406
