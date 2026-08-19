import Mathlib

namespace MathlibPlus.Open.Analysis.Claim48438

/-- The exact two-wall kernel from the source. -/
noncomputable def H48438 (b q t : ℝ) : ℝ :=
  Real.exp (-b * t - q * Real.exp (-t)) +
    Real.exp (b * t - q * Real.exp t)

/-- Iterated signed q-derivative `(-∂q)^k` of the actual kernel. -/
noncomputable def signedQDerivative48438 (b t : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun q => H48438 b q t
  | k + 1 => fun q =>
      -deriv (signedQDerivative48438 b t k) q

/-- Claim 48438: every iterated signed q-derivative transports the wall
parameter from `a` to `a+k`. -/
def claim48438_signedQDerivativeTransport : Prop :=
  ∀ (a q t : ℝ) (k : ℕ),
    signedQDerivative48438 a t k q = H48438 (a + k) q t

end MathlibPlus.Open.Analysis.Claim48438
