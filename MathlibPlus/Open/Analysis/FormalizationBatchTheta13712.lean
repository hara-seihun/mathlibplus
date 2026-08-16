import MathlibPlus.Open.Analysis.FormalizationBatchTheta

namespace MathlibPlus.Open.Analysis.FormalizationBatchTheta13712

/-- Tensor-product completion identity, retaining the Fourier, completion, and
correlation equalities in the admitted claim. -/
def claim_13712 : Prop :=
  ∀ (x u : ℝ),
    let h : ℝ → ℝ → ℂ := fun (x u : ℝ) =>
      ∫ d : ℝ,
        (↑(MathlibPlus.Open.Analysis.FormalizationBatchTheta.thetaPrimitive
          (u / 2 + d) *
          MathlibPlus.Open.Analysis.FormalizationBatchTheta.thetaPrimitive
            (u / 2 - d)) : ℂ) *
          Complex.exp (2 * Complex.I * (x : ℂ) * (d : ℂ))
    let L : ℝ → ℝ → ℂ := fun (x u : ℝ) =>
      iteratedDeriv 4 (h x) u +
          ((2 * x ^ 2 - 1 / 2 : ℝ) : ℂ) * iteratedDeriv 2 (h x) u +
          (((x ^ 2 + 1 / 4 : ℝ) ^ 2 : ℝ) : ℂ) * h x u
    let D : ℝ → ℝ := fun t =>
      iteratedDeriv 2
          MathlibPlus.Open.Analysis.FormalizationBatchTheta.thetaPrimitive t -
        (1 / 4 : ℝ) *
          MathlibPlus.Open.Analysis.FormalizationBatchTheta.thetaPrimitive t
    L x u =
        ∫ d : ℝ,
          (↑(D (u / 2 + d) * D (u / 2 - d)) : ℂ) *
            Complex.exp (2 * Complex.I * (x : ℂ) * (d : ℂ)) ∧
      (∫ d : ℝ,
          (↑(D (u / 2 + d) * D (u / 2 - d)) : ℂ) *
            Complex.exp (2 * Complex.I * (x : ℂ) * (d : ℂ))) =
        ∫ d : ℝ,
          (↑(MathlibPlus.Open.Analysis.FormalizationBatchTheta.Phi
            (u / 2 + d) *
            MathlibPlus.Open.Analysis.FormalizationBatchTheta.Phi
              (u / 2 - d)) : ℂ) *
            Complex.exp (2 * Complex.I * (x : ℂ) * (d : ℂ)) ∧
      (∫ d : ℝ,
          (↑(MathlibPlus.Open.Analysis.FormalizationBatchTheta.Phi
            (u / 2 + d) *
            MathlibPlus.Open.Analysis.FormalizationBatchTheta.Phi
              (u / 2 - d)) : ℂ) *
            Complex.exp (2 * Complex.I * (x : ℂ) * (d : ℂ))) =
        MathlibPlus.Open.Analysis.FormalizationBatchTheta.correlation (u / 2) x

end MathlibPlus.Open.Analysis.FormalizationBatchTheta13712
