import Mathlib
import MathlibPlus.NumberTheory.Claim9757

open scoped BigOperators

namespace MathlibPlus.NumberTheory.Claim9769

/-- Harmonic smoothing identity from the Mertens function to `B`. -/
def harmonicSmoothingIdentity : Prop :=
  let h : ℕ → ℚ := MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff
  let B : ℕ → ℚ := fun x => ∑ n ∈ Finset.Icc 1 x, h n
  let M : ℕ → ℤ := fun x => ∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.moebius n
  ∀ x : ℕ,
    B x = ∑ m ∈ Finset.Icc 1 x, (m : ℚ)⁻¹ * (M (x / m) : ℚ)

end MathlibPlus.NumberTheory.Claim9769
