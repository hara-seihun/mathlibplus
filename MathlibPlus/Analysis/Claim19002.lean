import Mathlib

namespace MathlibPlus.Analysis

/-- Reciprocal, boundary-unitary, and real-type identities for the scattering
ratio in claim 19002.  The packet supplies no canonical definition of `E`, so
its stated real-type and imaginary-axis nonvanishing properties are exposed as
its exact interface rather than silently choosing an analytic model. -/
theorem reciprocalScatteringRatio_claim19002
    (E : ℂ → ℂ)
    (hreal : ∀ z : ℂ, E (starRingEnd ℂ z) = starRingEnd ℂ (E z))
    (himag : ∀ t : ℝ, E ((t : ℂ) * Complex.I) ≠ 0) :
    let S : ℂ → ℂ := fun z => E (-z) / E z
    (∀ z : ℂ, E z ≠ 0 → E (-z) ≠ 0 →
      S (-z) = (S z)⁻¹) ∧
    (∀ t : ℝ, ‖S ((t : ℂ) * Complex.I)‖ = 1) ∧
    (∀ z : ℂ, E z ≠ 0 → E (starRingEnd ℂ z) ≠ 0 →
      S (starRingEnd ℂ z) = starRingEnd ℂ (S z)) := by
  dsimp
  constructor
  · intro z _ _
    rw [inv_div]
    congr 1
    simp only [neg_neg]
  constructor
  · intro t
    have hEt : E ((t : ℂ) * Complex.I) ≠ 0 := himag t
    have hEt_norm : ‖E ((t : ℂ) * Complex.I)‖ ≠ 0 :=
      (norm_ne_zero_iff.mpr hEt)
    have hminus :
        E (-((t : ℂ) * Complex.I)) =
          starRingEnd ℂ (E ((t : ℂ) * Complex.I)) := by
      rw [← hreal ((t : ℂ) * Complex.I)]
      congr 1
      simp
    rw [Complex.norm_div, hminus, Complex.norm_conj, div_self hEt_norm]
  · intro z _ _
    rw [map_div₀]
    rw [← hreal (-z), ← hreal z]
    congr 1

end MathlibPlus.Analysis
