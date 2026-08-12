import Mathlib

namespace MathlibPlus.Algebra.Claim6733

/-- The affine four-cycle identity, with the four source factors represented by
arbitrary elements of an additive commutative group. -/
theorem affineFourCycle_claim6733 {R : Type _} [AddCommGroup R]
    (F_A F_B F_C F_D : R) :
    F_A + F_B - F_C - F_D = 0 ↔ F_A + F_B = F_C + F_D := by
  constructor
  · intro h
    calc
      F_A + F_B = (F_A + F_B - F_C - F_D) + (F_C + F_D) := by abel
      _ = 0 + (F_C + F_D) := by rw [h]
      _ = F_C + F_D := by abel
  · intro h
    rw [h]
    abel

end MathlibPlus.Algebra.Claim6733
