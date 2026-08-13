import Mathlib

namespace MathlibPlus.Algebra.Claim19516

/-- The literal contact tensor and zipper differ in the free two-generator module. -/
theorem literalMinusZipper_identity :
    let R := Polynomial ℚ
    let S : R × R := (1, 0)
    let T : R × R := (0, 1)
    let L : R → R × R := fun w => w • S + w • T
    let Z : R → R × R := fun w => S + (2 * w - 1) • T
    ∀ w : R, L w - Z w = (w - 1) • (S - T) := by
  dsimp
  intro w
  ext <;> simp <;> ring


end MathlibPlus.Algebra.Claim19516

namespace MathlibPlus.Algebra

/-- Under the scalar augmentation sending both connectivity generators to one,
the contact and zipper expressions both evaluate to `2 * w`. -/
theorem scalar_augmentation_erases_discrepancy_claim19518
    {R A : Type*} [Ring R] [Ring A]
    (ε : R →+* A) (S T : R) (w : A)
    (hS : ε S = 1) (hT : ε T = 1) :
    (w * ε S + w * ε T = 2 * w) ∧
      (ε S + (2 * w - 1) * ε T = 2 * w) := by
  constructor
  · simp only [hS, hT, mul_one]
    rw [two_mul]
  · simp only [hS, hT, mul_one]
    exact add_sub_cancel 1 (2 * w)

end MathlibPlus.Algebra
