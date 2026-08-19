import Mathlib

namespace MathlibPlus.Analysis.Claim17808

noncomputable def gammaCompletionFactor (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (1 + s / 2)

end MathlibPlus.Analysis.Claim17808
