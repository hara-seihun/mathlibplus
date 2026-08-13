import MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting.DerivativeAndNormalization
import MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.FksHistoryAndNormalization

namespace MathlibPlus.AnalyticNumberTheory

/-- The two normalization nodes cannot hold simultaneously: their certified
margins place the same normalized coefficient on disjoint intervals. -/
theorem normalizationCertificates_not_both :
    ¬ (Open.AnalyticNumberTheory.PrimeCounting.directedNormalizationInequalities ∧
      Open.AnalyticNumberTheory.PrimeSums.alternativeEnvelopeNormalizationCheck) := by
  intro h
  dsimp [Open.AnalyticNumberTheory.PrimeCounting.directedNormalizationInequalities,
    Open.AnalyticNumberTheory.PrimeSums.alternativeEnvelopeNormalizationCheck] at h
  norm_num at h
  linarith [h.1.1, h.2.2.1]

end MathlibPlus.AnalyticNumberTheory
