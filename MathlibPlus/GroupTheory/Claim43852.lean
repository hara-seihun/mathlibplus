import Mathlib

namespace MathlibPlus.GroupTheory.Claim43852

/--
The fibre chart from claim R-2881.  The group assumptions model a finite
semidirect product `W ⋊ H`; the conclusion is the carrier-level fact that a
row-wise permutation gives a bijection and fixes the origin in the identity
fibre.
-/
theorem fibreChart_bijective
    {W H : Type*} [Fintype W] [Fintype H]
    [AddCommGroup W] [Group H] [DistribMulAction H W]
    (F : H → W → W)
    (hF : ∀ h, Function.Bijective (F h))
    (_hOne : F 1 = id)
    (hZero : ∀ h, F h 0 = 0) :
    Function.Bijective (fun wh : W × H => (F wh.2 wh.1, wh.2)) ∧
      (fun wh : W × H => (F wh.2 wh.1, wh.2)) (0, 1) = (0, 1) := by
  constructor
  · constructor
    · intro x y hxy
      rcases x with ⟨xw, xh⟩
      rcases y with ⟨yw, yh⟩
      have hh : xh = yh := congrArg Prod.snd hxy
      subst yh
      have hw : F xh xw = F xh yw := congrArg Prod.fst hxy
      exact Prod.ext ((hF xh).1 hw) rfl
    · intro y
      rcases y with ⟨yw, yh⟩
      rcases (hF yh).2 yw with ⟨xw, hxw⟩
      refine ⟨(xw, yh), ?_⟩
      exact Prod.ext hxw rfl
  · exact Prod.ext (hZero 1) rfl

end MathlibPlus.GroupTheory.Claim43852
