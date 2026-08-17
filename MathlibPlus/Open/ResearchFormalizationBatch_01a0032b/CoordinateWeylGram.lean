import MathlibPlus.Open.ResearchFormalizationBatch_01a0032b.Weyl

namespace MathlibPlus.Open.Batch_01a0032b

noncomputable section

/-- Claim 7583: positivity of the coordinate Weyl form transfers to every
finite upper-half-plane Gram of its bilateral Fourier--Laplace compression. -/
def coordinatePositivityTransfersToWeylGram : Prop :=
  ∀ (Φ : ℝ → ℝ) (η : ℝ),
    superExponentialRealSource Φ →
      nonnegativeRealQuadraticForm (coordinateWeylKernel Φ η) →
        ∀ (m : ℕ) (z : Fin m → ℂ),
          (∀ j, 0 < (z j).im) →
            complexMatrixPSD
              (fun i j => weylCompressionIntegral Φ η (z i) (z j))

end

end MathlibPlus.Open.Batch_01a0032b
