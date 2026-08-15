import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Batch_01a0032b

noncomputable section

/-- Claim 10119: Gaussian monomial orthogonality for planar area measure. -/
def gaussianMonomialOrthogonality : Prop :=
  ∀ (m n : ℕ),
    (1 / Real.pi : ℂ) *
        ∫ z : ℂ, (Real.exp (-‖z‖ ^ 2) : ℂ) * z ^ n * (star z) ^ m =
      (Nat.factorial n : ℂ) * if n = m then 1 else 0

end

end MathlibPlus.Open.Batch_01a0032b
