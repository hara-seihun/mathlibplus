import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1647Claim39933

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

private def isAffineOnTriad (σ : Equiv.Perm (ZMod 3)) : Prop :=
  ∃ a : (ZMod 3)ˣ, ∃ b : ZMod 3,
    ∀ x : ZMod 3, σ x = (a : ZMod 3) * x + b

/-- Claim 39933: every permutation of the three-point cyclic fiber is an
 affine map, and both the full symmetric and affine permutation groups have
 six elements. -/
def triadPermutationIsAffine_claim39933 : Prop :=
  letI : Fintype {σ : Equiv.Perm (ZMod 3) // isAffineOnTriad σ} :=
    Fintype.ofFinite _
  Fintype.card (Equiv.Perm (ZMod 3)) = 6 ∧
    Fintype.card {σ : Equiv.Perm (ZMod 3) // isAffineOnTriad σ} = 6 ∧
    (∀ σ : Equiv.Perm (ZMod 3), isAffineOnTriad σ)

end

end MathlibPlus.Open.ResearchFormalization.R1647Claim39933
