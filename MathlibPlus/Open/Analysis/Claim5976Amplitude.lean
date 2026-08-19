import Mathlib

namespace MathlibPlus.Open.Analysis.Claim5976

noncomputable section

/-- The reciprocal logarithmic B-process amplitude map. -/
noncomputable def reciprocalAmplitude_claim5976
    (U : ℝ) (q : ℝ → ℂ) (m : ℝ) : ℂ :=
  ((Real.sqrt U : ℝ) : ℂ) / (m : ℂ) * q (U / m)

/-- Applying the reciprocal amplitude map twice returns the original amplitude
at positive frequency and positive argument. -/
def reciprocalAmplitudeInvolution_claim5976 : Prop :=
  ∀ (U m : ℝ), 0 < U → 0 < m →
    ∀ q : ℝ → ℂ,
      reciprocalAmplitude_claim5976 U
          (reciprocalAmplitude_claim5976 U q) m = q m

end
end MathlibPlus.Open.Analysis.Claim5976
