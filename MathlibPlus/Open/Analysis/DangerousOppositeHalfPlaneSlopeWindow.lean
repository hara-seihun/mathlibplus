import Mathlib

namespace MathlibPlus.Open.Analysis

/--
The real-part quadratic in the root-cone expression has a compact dangerous
opposite-half-plane slope window.  Outside that window its nonnegativity is
automatic; inside it is exactly the imaginary-separation requirement.
-/
def dangerousOppositeHalfPlaneSlopeWindow : Prop :=
  (∀ x y : ℝ,
    x ^ 2 + 6 * x * y + y ^ 2 =
      (x + (3 + 2 * Real.sqrt 2) * y) *
        (x + (3 - 2 * Real.sqrt 2) * y)) ∧
  (∀ α β : ℂ,
    let x : ℝ := α.re
    let y : ℝ := β.re
    let separation : ℝ := α.im - β.im
    let q : ℝ := x ^ 2 + 6 * x * y + y ^ 2
    ((x * y ≥ 0 ∨
        (x * y < 0 ∧
          (abs x / abs y ≤ 3 - 2 * Real.sqrt 2 ∨
            3 + 2 * Real.sqrt 2 ≤ abs x / abs y))) →
      0 ≤ separation ^ 2 + q) ∧
    (x * y < 0 →
      (q < 0 ↔
        3 - 2 * Real.sqrt 2 < abs x / abs y ∧
          abs x / abs y < 3 + 2 * Real.sqrt 2)) ∧
    ((x * y < 0 ∧
        3 - 2 * Real.sqrt 2 < abs x / abs y ∧
          abs x / abs y < 3 + 2 * Real.sqrt 2) →
      (0 ≤ separation ^ 2 + q ↔ -q ≤ separation ^ 2)))

end MathlibPlus.Open.Analysis
