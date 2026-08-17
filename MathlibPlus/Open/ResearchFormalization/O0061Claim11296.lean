import MathlibPlus.Open.ResearchFormalizationBatch.QuartetInertia

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.O0061Claim11296

open MathlibPlus.Open.ResearchFormalizationBatch

/-- Claim 11296: with the off-axis quartet parameters fixed by
`quartetPPlus` and `quartetPMinus`, the exact Loewner-kernel defect has the
rank-three Krein factorization on positive nodes. -/
def claim11296 : Prop :=
  ∀ (N : ℕ) (δ T : ℝ) (nodes : Fin N → ℝ),
    (∀ i, 0 < nodes i) →
    let a : Fin N → ℝ := quartetRealFeature δ T nodes
    let b : Fin N → ℝ := quartetImaginaryFeature δ T nodes
    let u₀ : Fin N → ℝ := quartetZeroFeature T nodes
    let B : Matrix (Fin N) (Fin N) ℝ :=
      quartetKernelDefect δ T nodes
    B = (fun i j =>
      (8 * quartetUPlus δ T (nodes i) * quartetUPlus δ T (nodes j) +
        8 * quartetUMinus δ T (nodes i) * quartetUMinus δ T (nodes j) -
        16 * ((quartetUZero T (nodes i) : ℂ) *
          quartetUZero T (nodes j))).re) ∧
      B = (fun i j =>
        16 * (a i * a j - b i * b j - u₀ i * u₀ j)) ∧
      matrixRankAtMostThree B

end MathlibPlus.Open.ResearchFormalization.O0061Claim11296
