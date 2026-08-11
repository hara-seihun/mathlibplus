import Mathlib

/-!
# Laurent involution and finite-divisor moments

The coefficient-level Laurent involution and finite power-sum functional from
admitted claim 129.
-/

open scoped LaurentPolynomial ComplexConjugate BigOperators

namespace MathlibPlus.Algebra.LaurentInvolution

open AddMonoidAlgebra LaurentPolynomial

/-- Conjugate the coefficients of a complex Laurent polynomial and reverse every
exponent. This is the finite Laurent-polynomial meaning of
`p*(u) = conj (p (1 / conj u))`. -/
noncomputable def laurentStar (p : ℂ[T;T⁻¹]) : ℂ[T;T⁻¹] :=
  LaurentPolynomial.invert
    ((AddMonoidAlgebra.mapRingHom ℤ (starRingEnd ℂ)) p)

/-- The coefficient of `u⁻ⁿ` in `p*` is the conjugate of the coefficient of `uⁿ`
in `p`. -/
@[simp] theorem starCoeff (p : ℂ[T;T⁻¹]) (n : ℤ) :
    (laurentStar p).coeff (-n) = star (p.coeff n) := by
  simp [laurentStar]

@[simp] theorem laurentStar_add (p q : ℂ[T;T⁻¹]) :
    laurentStar (p + q) = laurentStar p + laurentStar q := by
  simp [laurentStar]

@[simp] theorem laurentStar_C_mul_T (a : ℂ) (n : ℤ) :
    laurentStar (LaurentPolynomial.C a * LaurentPolynomial.T n) =
      LaurentPolynomial.C (star a) * LaurentPolynomial.T (-n) := by
  unfold laurentStar
  rw [← LaurentPolynomial.single_eq_C_mul_T a n]
  rw [AddMonoidAlgebra.mapRingHom_single]
  rw [LaurentPolynomial.single_eq_C_mul_T]
  simp

/-- Evaluation realizes the advertised functional identity
`p*(u) = conj (p (1 / conj u))`; the inverse of the conjugate unit is exactly
`1 / conj u`. -/
theorem eval_laurentStar (p : ℂ[T;T⁻¹]) (u : ℂˣ) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) u (laurentStar p) =
      star (LaurentPolynomial.eval₂ (RingHom.id ℂ) (star u)⁻¹ p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq]
  | C_mul_T n a =>
      rw [laurentStar_C_mul_T]
      simp [LaurentPolynomial.eval₂_C_mul_T, star_mul]
      ac_rfl

/-- Evaluation at every point of a finite complex divisor, summed with
multiplicity. Repeated entries of `w` encode repeated divisor points. -/
noncomputable def finiteDivisorMoment {m : ℕ} (w : Fin m → ℂˣ) :
    ℂ[T;T⁻¹] →ₗ[ℂ] ℂ :=
  ∑ r : Fin m, LaurentPolynomial.leval ℂ (w r)

/-- On the Laurent monomial `uⁿ`, the finite-divisor moment functional is the
power sum `sum_r w_rⁿ`. Linearity on all Laurent polynomials is built into
`finiteDivisorMoment`. -/
@[simp] theorem finiteDivisorMoment_T {m : ℕ} (w : Fin m → ℂˣ) (n : ℤ) :
    finiteDivisorMoment w (LaurentPolynomial.T n) =
      ∑ r : Fin m, ((w r) ^ n : ℂˣ).val := by
  simp [finiteDivisorMoment]

end MathlibPlus.Algebra.LaurentInvolution
