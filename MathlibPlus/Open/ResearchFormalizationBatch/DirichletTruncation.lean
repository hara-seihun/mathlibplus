import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.DirichletTruncation

/-- Norm-divergence formulation of a pole at a point. -/
private def hasNormPoleAt (f : ℂ → ℂ) (z : ℂ) : Prop :=
  Filter.Tendsto (fun w => ‖f w‖) (nhdsWithin z {z}ᶜ) Filter.atTop

/-- The ordinary finite Dirichlet truncation, using the positive-real
logarithm branch for its terms. -/
private noncomputable def finiteDirichletTruncation (N : ℕ) (s : ℂ) : ℂ :=
  Finset.sum (Finset.range N)
    (fun n => Complex.exp (-s * Complex.log ((n + 1 : ℕ) : ℂ)))

/-- At a negative even point the finite truncation is positive and hence
cannot remove the Gamma seed pole there. -/
def finiteDirichletTruncationLeavesGammaPoleUncancelled : Prop :=
  ∀ (N k : ℕ),
    1 ≤ N →
    1 ≤ k →
      0 < Finset.sum (Finset.range N)
        (fun n => (((n + 1 : ℕ) : ℝ) ^ (2 * k))) ∧
      finiteDirichletTruncation N (-(2 * k : ℂ)) =
        (((Finset.sum (Finset.range N)
          (fun n => (((n + 1 : ℕ) : ℝ) ^ (2 * k))) : ℝ) : ℂ)) ∧
      hasNormPoleAt
        (fun s : ℂ => finiteDirichletTruncation N s * Complex.Gamma (s / 2))
        (-(2 * k : ℂ))

end MathlibPlus.Open.ResearchFormalizationBatch.DirichletTruncation
