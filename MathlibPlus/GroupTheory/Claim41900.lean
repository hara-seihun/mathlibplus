import Mathlib

namespace MathlibPlus.GroupTheory

/-- Every permutation of a three-point fibre is affine after identifying the
fibre with `ZMod 3`.  The multiplier is required to be nonzero, exactly as in
the affine profile of claim 41900. -/
theorem everyPermutation_zmod3_affine_claim41900
    (σ : Equiv.Perm (ZMod 3)) :
    ∃ a b : ZMod 3, a ≠ 0 ∧ ∀ x : ZMod 3, σ x = a * x + b := by
  native_decide +revert

end MathlibPlus.GroupTheory
