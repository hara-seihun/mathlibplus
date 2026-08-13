import Mathlib

namespace MathlibPlus.Algebra

/-- The endpoint-rooted order-two scalar polynomial from claim 55902. -/
def endpointPolynomial55902 {R : Type*} [CommRing R]
    (x₁ x₂ w : R) : R :=
  1 + w * x₁ + w ^ 2 * (x₂ + x₁ ^ 2)

/-- The displayed active-face defect factors algebraically for every commutative ring. -/
theorem endpointPolynomial_defect_factor_claim55902
    {R : Type*} [CommRing R] (x₁ x₂ w : R) :
    endpointPolynomial55902 x₁ x₂ w -
        2 * endpointPolynomial55902 x₁ x₂ w ^ 2 +
        endpointPolynomial55902 x₁ x₂ w ^ 3 =
      endpointPolynomial55902 x₁ x₂ w *
        (endpointPolynomial55902 x₁ x₂ w - 1) ^ 2 := by
  ring

/-- The factorized defect is not the zero function over the rationals. -/
theorem endpointPolynomial_defect_nonzero_claim55902 :
    ¬ (∀ x₁ x₂ w : ℚ,
      endpointPolynomial55902 x₁ x₂ w -
          2 * endpointPolynomial55902 x₁ x₂ w ^ 2 +
          endpointPolynomial55902 x₁ x₂ w ^ 3 = 0) := by
  intro h
  have h0 := h 0 1 1
  norm_num [endpointPolynomial55902] at h0

end MathlibPlus.Algebra
