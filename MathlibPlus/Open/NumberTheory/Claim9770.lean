import Mathlib
import MathlibPlus.NumberTheory.Claim9757

namespace MathlibPlus.Open.NumberTheory.Claim9770

open scoped BigOperators

noncomputable section

private def mobiusQ (n : ℕ) : ℚ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℚ)

private def B (x : ℕ) : ℚ :=
  Finset.sum (Finset.Icc 1 x)
    (fun n => MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff n)

private def mertens (x : ℕ) : ℚ :=
  Finset.sum (Finset.Icc 1 x) (fun m => mobiusQ m)

def inverseHarmonicIdentity : Prop :=
  ∀ x : ℕ,
    mertens x =
      Finset.sum (Finset.Icc 1 x)
        (fun m => (mobiusQ m / (m : ℚ)) * B (x / m))

end

end MathlibPlus.Open.NumberTheory.Claim9770
