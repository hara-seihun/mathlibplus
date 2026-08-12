import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MathlibPlus.GroupTheory

/-- Claim 29699: the non-coprime `C₂ × C₂` translation shear has trivial
relative derivatives but swaps the two points on the nonidentity fibre. -/
theorem claim29699_nonCoprime_shear :
    let τ : ZMod 2 → ZMod 2 := id
    let f : (ZMod 2 × ZMod 2) → (ZMod 2 × ZMod 2) :=
      fun (a, h) => (a + τ h, h)
    Nat.gcd 2 2 ≠ 1 ∧
      τ 0 = 0 ∧
      τ 1 = 1 ∧
      (∀ h k : ZMod 2, τ (h + k) - τ k - τ h = 0) ∧
      (∀ a h k : ZMod 2,
        (a + (τ (h + k) - τ k - τ h), h) = (a, h)) ∧
      f (0, 1) = (1, 1) ∧
      f (1, 1) = (0, 1) := by
  dsimp
  decide

end MathlibPlus.GroupTheory
