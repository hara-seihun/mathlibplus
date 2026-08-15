import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeSums

/-- The normalized absolute error of the Chebyshev `ψ` function. -/
noncomputable def normalizedAbsolutePsiError (x : ℝ) : ℝ :=
  |Chebyshev.psi x - x| / x

/-- The square-root-exponential envelope at `x`, with `L = log x`. -/
noncomputable def squareRootExponentialPsiEnvelope (C d x : ℝ) : ℝ :=
  C * (Real.log x) ^ (3 / 2 : ℝ) * Real.exp (-d * Real.sqrt (Real.log x))

/-- The assertion that the normalized `ψ` error has the displayed envelope on `x > 2`. -/
def HasSquareRootExponentialPsiEnvelope (C d : ℝ) : Prop :=
  ∀ x : ℝ, 2 < x →
    normalizedAbsolutePsiError x ≤ squareRootExponentialPsiEnvelope C d x

end MathlibPlus.Open.AnalyticNumberTheory.PrimeSums
