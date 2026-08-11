import MathlibPlus.Basic

namespace MathlibPlus.Analysis.CompletedGammaFactor

/-!
The completed gamma factor and its spectral coordinate from admitted claim 3603.
The source does not state a domain for the spectral parameter, so `z` is kept
complex here rather than adding a realness hypothesis.  Complex exponentiation
uses Mathlib's principal `Complex.cpow` branch.
-/

/-- `A(s) = 1/2 * s * (s - 1) * π^(-s/2) * Γ(s/2)`. -/
noncomputable def completedGammaFactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)

/-- The spectral coordinate `s = 1/2 + i z`. -/
noncomputable def spectralCoordinate (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * z

end MathlibPlus.Analysis.CompletedGammaFactor
