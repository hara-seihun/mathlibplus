import MathlibPlus.Basic

open Polynomial

namespace MathlibPlus.Algebra.Claim2747

/-!
Formalization of admitted claim 2747 (source record C-0185).  The source's
coefficient agreement through degree six is stated over an arbitrary
commutative ring and is equivalent to divisibility of the correction by the
seventh power of the polynomial variable.
-/

/-- Agreement of the coefficients in degrees `0, ..., 6` is exactly
    divisibility of the difference by `X ^ 7`. -/
theorem lowModePreservation_iff {R : Type*} [CommRing R]
    (Pstar P0 : R[X]) :
    (∀ j : ℕ, j ≤ 6 → Pstar.coeff j = P0.coeff j) ↔
      X ^ 7 ∣ Pstar - P0 := by
  rw [X_pow_dvd_iff]
  constructor
  · intro h d hd
    have hd6 : d ≤ 6 := by omega
    have hcoeff := h d hd6
    rw [coeff_sub]
    exact sub_eq_zero.mpr hcoeff
  · intro h j hj
    have hcoeff := h j (by omega)
    rw [coeff_sub] at hcoeff
    exact sub_eq_zero.mp hcoeff

end MathlibPlus.Algebra.Claim2747
