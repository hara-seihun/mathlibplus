import Mathlib

namespace MathlibPlus.Algebra.Claim24950

/-- The difference of the two endpoint-pair products is the displayed affine
polynomial in the free variable. -/
theorem pairStateDifference_eq_affine {R : Type*} [CommRing R]
    (a b c d w : R) :
    (w + c) * (w + d) - (w + a) * (w + b) =
      (c + d - a - b) * w + (c * d - a * b) := by
  ring

/-- In a gcd monoid, the content of the two affine coefficients has the exact
common-divisor specification used by the source.  The GCD monoid interface
also records that this specification is only canonical up to association. -/
theorem pairStateContent_gcd_spec {R : Type*} [CommRing R] [GCDMonoid R]
    (a b c d : R) :
    let α := c + d - a - b
    let β := c * d - a * b
    (α ≠ 0 ∨ β ≠ 0) →
      (gcd α β ∣ α ∧ gcd α β ∣ β ∧
        ∀ z : R, z ∣ α → z ∣ β → z ∣ gcd α β) := by
  dsimp
  intro _
  exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _, fun z hzα hzβ => dvd_gcd hzα hzβ⟩

end MathlibPlus.Algebra.Claim24950
