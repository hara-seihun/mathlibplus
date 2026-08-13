import Mathlib

namespace MathlibPlus.Algebra.AdmittedClaimsBatch20260811

/-- Claim 12275: the prime differential remains an isomorphism after
complexification of the two-term integer complex. -/
theorem claim12275_complexifiedPrimeMapBijective (p : ℕ) (hp : Nat.Prime p) :
    Function.Bijective (fun z : Complex => (p : Complex) * z) := by
  have hp0 : (p : Complex) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  constructor
  · intro z w h
    exact mul_left_cancel₀ hp0 h
  · intro z
    refine ⟨(p : Complex)⁻¹ * z, ?_⟩
    change (p : Complex) * ((p : Complex)⁻¹ * z) = z
    rw [← mul_assoc, mul_inv_cancel₀ hp0, one_mul]

/-- Claim 43286: the fourth-coefficient fold is the displayed rational
polynomial identity under the source's relation for `V * D₃`. -/
theorem claim43286_fourthCoefficientFold (V A₂ D₃ : ℚ)
    (h : V * D₃ = A₂ ^ 2 + V ^ 4 / 12) :
    let Q := A₂ + V ^ 2 / 2
    V * D₃ + A₂ ^ 2 / 2 + V ^ 2 * A₂ / 2 + V ^ 4 / 24 =
      (6 * Q ^ 2 - 4 * Q * V ^ 2 + V ^ 4) / 4 := by
  dsimp
  rw [h]
  ring

end MathlibPlus.Algebra.AdmittedClaimsBatch20260811
