import Mathlib

namespace MathlibPlus.Analysis.Claim17473

/-- Claim 17473: the flat-cap deformation of `H` by `E`. -/
def flatCapDeformation {Z R : Type*} [Ring R]
    (H E : Z → R) (τ : R) : Z → R :=
  fun z => H z + (1 - τ) * E z

end MathlibPlus.Analysis.Claim17473
