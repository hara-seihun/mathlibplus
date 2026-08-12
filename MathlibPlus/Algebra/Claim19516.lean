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
