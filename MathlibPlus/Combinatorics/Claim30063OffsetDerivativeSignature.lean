import Mathlib

namespace MathlibPlus.Combinatorics

/-- The offset derivative signature from admitted claim 30063, with `C₇` represented
by `ZMod 7` and the induced label map retaining its permutation type. -/
def offsetDerivativeSignature_claim30063
    (δ : ZMod 7 ≃ ZMod 7) (v : ZMod 7) : ZMod 7 → ZMod 7 :=
  fun w => δ (v + 2 * w) - δ v

end MathlibPlus.Combinatorics
