import Mathlib.Data.ZMod.Basic

namespace MathlibPlus.GroupTheory

/-- Claim 39862: on a two-point fiber, the bijections are exactly the affine
maps over `ZMod 2`; the nonzero-slope condition is the affine-permutation
condition. -/
theorem allBijectionsZModTwoAffine_claim39862 :
    ∀ f : ZMod 2 → ZMod 2, Function.Bijective f ↔
      ∃ a b : ZMod 2, a ≠ 0 ∧ ∀ x : ZMod 2, f x = a * x + b := by
  decide

end MathlibPlus.GroupTheory
