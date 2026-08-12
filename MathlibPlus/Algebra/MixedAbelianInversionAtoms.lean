import Mathlib

namespace MathlibPlus.Algebra.MixedAbelianInversionAtoms

/--
Claim 37083.  The additive coordinate model
`(ℤ/2ℤ)^3 × (ℤ/3ℤ)^2` represents `C₂³ × C₃²`; negation is inversion.
The explicit radix code is only a canonical representative selector for the
non-fixed two-element inversion orbits, so its count is the count of pair
atoms rather than an additional mathematical hypothesis.
-/
theorem mixedAbelianOrder72InverseAtoms :
    let G := ((ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 3 × ZMod 3))
    let code : G → Nat := fun x =>
      (((((ZMod.val x.1.1) * 2 + ZMod.val x.1.2.1) * 2 + ZMod.val x.1.2.2) * 3 +
          ZMod.val x.2.1) * 3 + ZMod.val x.2.2)
    (∀ x : G, x ≠ 0 → x ≠ -x → code x ≠ code (-x)) ∧
      Fintype.card G = 72 ∧
      Fintype.card {x : G // x ≠ 0} = 71 ∧
      Fintype.card {x : G // x ≠ 0 ∧ -x = x} = 7 ∧
      Fintype.card {x : G // x ≠ 0 ∧ x ≠ -x} = 64 ∧
      Fintype.card {x : G // x ≠ 0 ∧ x ≠ -x ∧ code x < code (-x)} = 32 := by
  native_decide

end MathlibPlus.Algebra.MixedAbelianInversionAtoms
