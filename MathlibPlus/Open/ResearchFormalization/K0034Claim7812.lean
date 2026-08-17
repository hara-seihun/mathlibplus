import MathlibPlus.Open.Analysis.ClosedPhasePairedTranslationKernel
import MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120
import MathlibPlus.Open.ResearchFormalization.SpectralDyadic
import MathlibPlus.Open.ResearchFormalizationK0034

namespace MathlibPlus.Open.ResearchFormalization.K0034Claim7812

open MathlibPlus.Open.Analysis
open MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120
open MathlibPlus.Open.ResearchFormalization.SpectralDyadic
open MathlibPlus.Open.ResearchFormalizationK0034

noncomputable section

/-- Schur completion of the phase-paired translation kernel on the critical line. -/
def claim7812 : Prop :=
  ∀ (a τ : ℝ), 0 < a →
    matrixValuedPositiveDefinite
      (fun z =>
        schurProduct (dyadicG (criticalS τ))
          (phaseCoefficientKernel a τ z))

end

end MathlibPlus.Open.ResearchFormalization.K0034Claim7812
