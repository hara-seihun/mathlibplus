import Mathlib

namespace MathlibPlus.Open.Analysis.Claim4608

/--
A signed exponent spectrum is reflection-invariant precisely when it is even.
The spectrum is represented by a function `p` on real exponents; its value
codomain is left abstract because the source supplies no coefficient type.
No support or normalization hypothesis is added.
-/
def reflectionInvariantPacket_claim4608 {Y : Type*} (p : ℝ → Y) : Prop :=
  ∀ α : ℝ, p (-α) = p α

end MathlibPlus.Open.Analysis.Claim4608
