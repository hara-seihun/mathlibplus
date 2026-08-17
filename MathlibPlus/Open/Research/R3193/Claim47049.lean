import MathlibPlus.Open.Research.R3193.Claim47053

namespace MathlibPlus.Open.Research.R3193

noncomputable section

/-- Claim 47049: in the exact shared-bit Rademacher model, a component's
    complete transcript determines its own output.  For every other component,
    the transcript posterior mean is `p A` on the common branch and zero on
    either private branch, and the variance of that posterior mean is `p^3`. -/
def claim47049 : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (j : Fin n),
    (∀ ω : RademacherSample n,
      componentValue n j ω =
        transcriptValue (componentTranscript n j ω)) ∧
    (∀ l : Fin n, l ≠ j →
      (∀ ω : RademacherSample n,
        posteriorComponentMean n j l ω =
          if commonIndicator n j ω = 1 then
            p * rademacherValue ω.a
          else 0) ∧
        uniformVariance (posteriorComponentMean n j l) = p ^ 3)

end

end MathlibPlus.Open.Research.R3193
