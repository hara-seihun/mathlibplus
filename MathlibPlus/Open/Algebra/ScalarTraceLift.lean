import Mathlib

namespace MathlibPlus.Open.Algebra

/-- Claim 4520.  The trace variable is real and the reciprocal roots are
complex; nonzeroness is stated explicitly because Lean's inverse is total. -/
def scalarTraceLiftAndReciprocalRoots : Prop :=
  (∀ (T : ℝ) (z : ℂ),
      z ≠ 0 → z + z⁻¹ = (T : ℂ) →
        z = ((T : ℂ) + Complex.sqrt ((T : ℂ)^2 - 4)) / 2 ∨
        z = ((T : ℂ) - Complex.sqrt ((T : ℂ)^2 - 4)) / 2) ∧
  (∀ (T : ℝ), -2 < T → T < 2 →
      ∀ z : ℂ, z ≠ 0 → z + z⁻¹ = (T : ℂ) → ‖z‖ = 1) ∧
  (∀ (T : ℝ), 2 < T →
      let lam : ℝ := (T + Real.sqrt (T^2 - 4)) / 2
      1 < lam ∧
        ∀ z : ℂ, z ≠ 0 →
          (z + z⁻¹ = (T : ℂ) ↔
            z = (lam : ℂ) ∨ z = ((lam⁻¹ : ℝ) : ℂ)))

end MathlibPlus.Open.Algebra
