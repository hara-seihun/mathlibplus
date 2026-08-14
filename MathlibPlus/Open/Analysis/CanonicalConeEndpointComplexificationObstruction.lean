import Mathlib

namespace MathlibPlus.Open

/--
The quadratic real map and its identity-indexed real family have the stated
nonnegativity property, while its complexification has a nonreal zero.
-/
def canonicalConeEndpointComplexificationObstruction : Prop :=
  let P : ℝ → ℝ := fun x => x ^ 2 + 1
  let H : ℕ → ℝ → ℝ := fun _ q => q
  let F : ℂ → ℂ := fun z => z ^ 2 + 1
  P 0 ≠ 0 ∧
    (∀ N : ℕ, ∀ y : ℝ, H N (P (-y) / P 0) ≥ 0) ∧
    (∀ x : ℝ, F (x : ℂ) = (P x : ℂ)) ∧
    (∀ z : ℂ, F (-z) = F z) ∧
    (∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z)) ∧
    F 0 = 1 ∧
    F Complex.I = 0 ∧
    Complex.im Complex.I ≠ 0

end MathlibPlus.Open
