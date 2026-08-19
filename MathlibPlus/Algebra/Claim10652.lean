import Mathlib

namespace MathlibPlus.Algebra.ClaimIdentities

/-- Claim 10652: the explicit even quartic has four off-axis zeros, and its
square-root-descended logarithmic derivative has the displayed rational form. -/
def degreeFourOffAxisCounterfeit_claim10652 : Prop :=
  let Y : ℂ → ℂ := fun z => z ^ 4 + 6 * z ^ 2 + 25
  let H : ℂ → ℂ := fun x => 4 * (x + 3) / (x ^ 2 + 6 * x + 25)
  (∀ x : ℂ,
      x ^ 2 + 6 * x + 25 = 0 ↔
        x = -3 + 4 * Complex.I ∨ x = -3 - 4 * Complex.I) ∧
    (∀ z : ℂ,
      Y z = 0 ↔
        z = 1 + 2 * Complex.I ∨ z = -(1 + 2 * Complex.I) ∨
        z = 1 - 2 * Complex.I ∨ z = -(1 - 2 * Complex.I)) ∧
    (∀ z : ℂ, Y z = 0 → z.re ≠ 0 ∧ z.im ≠ 0) ∧
    (∀ x z : ℂ, z ≠ 0 → x = z ^ 2 → Y z ≠ 0 →
      (4 * z ^ 3 + 12 * z) / (z * Y z) = H x)

end MathlibPlus.Algebra.ClaimIdentities
