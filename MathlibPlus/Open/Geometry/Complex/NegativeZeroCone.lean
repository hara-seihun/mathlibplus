import Mathlib

namespace MathlibPlus.Open.Geometry.Complex

/-- For `0 ≤ ε < π/12`, the negative-zero sector is convex, closed under
nonnegative real scaling, and invariant under complex conjugation. -/
def negativeZeroCone_claim530 : Prop :=
  ∀ ε : ℝ, 0 ≤ ε → ε < Real.pi / 12 →
    let S : Set ℂ := {z | |Complex.arg (-z)| ≤ ε}
    Convex ℝ S ∧
      (∀ r : ℝ, 0 ≤ r → ∀ z : ℂ, z ∈ S → r • z ∈ S) ∧
      (∀ z : ℂ, z ∈ S ↔ starRingEnd ℂ z ∈ S)

end MathlibPlus.Open.Geometry.Complex
