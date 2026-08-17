import Mathlib
import MathlibPlus.Analysis.CDialCounterfeit

namespace MathlibPlus.Open.FormalizationBatch.R0101Claim17947

open scoped BigOperators

noncomputable section

/-- The logarithmic coordinate on the positive divisor fibre. -/
private def divisorLogCoordinate (k m : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((k : ℝ) / (m : ℝ) ^ 2)

/-- The finite divisor character with the source normalization
`exp (q * ell_{k,m})`; at `q = 2 i tau` this is the phase
`exp (2 i tau * ell_{k,m})`. -/
private noncomputable def divisorCharacterSum (k : ℕ) (q : ℂ) : ℂ :=
  ∑ m ∈ k.divisors,
    Complex.exp (q * (divisorLogCoordinate k m : ℂ))

/-- The divisor-fibered Macdonald kernel supplied by the exact bridge. -/
private noncomputable def divisorFiber (k : ℕ) (q : ℂ) (A : ℝ) : ℂ :=
  MathlibPlus.Analysis.CDialCounterfeit.modifiedBesselK (q / 2) (A : ℂ) *
    divisorCharacterSum k q

/-- Claim 17947: complementary-divisor reflection makes both the finite
character and its Macdonald fibre even in the order parameter. -/
def claim17947 : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (q : ℂ) (A : ℝ), 0 < A →
    divisorCharacterSum k (-q) = divisorCharacterSum k q ∧
      divisorFiber k (-q) A = divisorFiber k q A

end

end MathlibPlus.Open.FormalizationBatch.R0101Claim17947
