import Mathlib.Algebra.Polynomial.Laurent

/-!
# Claim 9556: reciprocal Laurent element and polynomial

The Laurent element `u + u⁻¹ - 3` becomes the ordinary polynomial
`u^2 - 3u + 1` after multiplication by the unit `u`.
-/

open scoped LaurentPolynomial

namespace MathlibPlus.Algebra.Claim9556

/-- In `ℚ[u,u⁻¹]`, multiplication by the Laurent unit `u` sends
`u + u⁻¹ - 3` to `u^2 - 3u + 1`. -/
theorem reciprocalLaurentElement :
    let u : ℚ[T;T⁻¹] := LaurentPolynomial.T 1
    let f : ℚ[T;T⁻¹] := u + LaurentPolynomial.T (-1) - 3
    let g : ℚ[T;T⁻¹] := u ^ 2 - 3 * u + 1
    IsUnit u ∧ u * f = g := by
  dsimp
  constructor
  · exact LaurentPolynomial.isUnit_T 1
  · rw [sub_eq_add_neg, sub_eq_add_neg]
    rw [mul_add, mul_add, mul_neg]
    rw [← LaurentPolynomial.T_add (1 : ℤ) 1,
      ← LaurentPolynomial.T_add (1 : ℤ) (-1)]
    simp
    ring

end MathlibPlus.Algebra.Claim9556
