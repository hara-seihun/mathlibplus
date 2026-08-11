import Mathlib

/-!
# Centered curve numerator and descended Loewner kernel

This file formalizes admitted claim 248.  Mathlib does not yet expose a zeta-numerator
API for smooth projective curves over finite fields, so the curve's canonical data are
passed without weakening as its field cardinality `q`, genus `g`, and integral
numerator polynomial `P`.  The diagonal branch is the confluent derivative of the
first displayed divided difference.
-/

namespace MathlibPlus.Algebra.DescendedLoewner

/-- `X_C(z) = exp(g log(q) z) P_C(q^(-1/2) exp(-log(q) z))`. -/
noncomputable def centeredNumerator (q g : ℕ) (P : Polynomial ℤ) (z : ℂ) : ℂ :=
  Complex.exp ((g : ℂ) * (Real.log q : ℂ) * z) *
    Polynomial.eval₂ (Int.castRingHom ℂ)
      (Complex.cpow (q : ℂ) (-(1 : ℂ) / 2) *
        Complex.exp (-(Real.log q : ℂ) * z)) P

/-- The logarithmic derivative `L_C = X_C' / X_C`. -/
noncomputable def curveLogDerivative (q g : ℕ) (P : Polynomial ℤ) (z : ℂ) : ℂ :=
  deriv (centeredNumerator q g P) z / centeredNumerator q g P z

/-- The descended function `H_C(x) = L_C(sqrt(x)) / sqrt(x)` on real coordinates. -/
noncomputable def descendedH (q g : ℕ) (P : Polynomial ℤ) (x : ℝ) : ℂ :=
  curveLogDerivative q g P (Real.sqrt x) / Real.sqrt x

/-- The curve Loewner kernel.  Off the diagonal this is the first displayed divided
difference.  On the diagonal it is its confluent derivative
`2 (L_C(x) / x - L_C'(x))`. -/
noncomputable def descendedKernel (q g : ℕ) (P : Polynomial ℤ) (x y : ℝ) : ℂ :=
  if x = y then
    2 * (curveLogDerivative q g P x / x - deriv (curveLogDerivative q g P) x)
  else
    4 * (y * curveLogDerivative q g P x - x * curveLogDerivative q g P y) /
      (y ^ 2 - x ^ 2)

/-- Away from the confluent diagonal, the two formulas in claim 248 agree exactly. -/
theorem descendedKernelIdentity
    (q g : ℕ) (P : Polynomial ℤ) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    descendedKernel q g P x y =
      -4 * x * y *
        (descendedH q g P (x ^ 2) - descendedH q g P (y ^ 2)) /
          (x ^ 2 - y ^ 2) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hsquares : (x : ℂ) ^ 2 ≠ (y : ℂ) ^ 2 := by
    intro h
    have hr : x ^ 2 = y ^ 2 := by exact_mod_cast h
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hr) with heq | hneg
    · exact hxy heq
    · nlinarith
  simp only [descendedKernel, hxy, if_false, descendedH,
    Real.sqrt_sq_eq_abs, abs_of_pos hx, abs_of_pos hy]
  field_simp
  ring

/-- The diagonal value is the confluent branch of the displayed boundary divided
difference. -/
theorem descendedKernel_diagonal (q g : ℕ) (P : Polynomial ℤ) (x : ℝ) :
    descendedKernel q g P x x =
      2 * (curveLogDerivative q g P x / x - deriv (curveLogDerivative q g P) x) := by
  simp [descendedKernel]

end MathlibPlus.Algebra.DescendedLoewner
