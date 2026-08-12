import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring

namespace MathlibPlus.Algebra

/--
Claim 27189: the top coefficient of a cross-ratio identity between affine
cavities is the corresponding cross-ratio identity between their slopes.
The four cavities are represented exactly as `C * X + a`.
-/
theorem affineCavityCrossRatio_topCoefficient_claim27189
    {R : Type*} [CommRing R]
    (Cr Cs Ct E ar as atc e μ : R)
    (h :
      ((Polynomial.C Cr * Polynomial.X + Polynomial.C ar) -
          (Polynomial.C E * Polynomial.X + Polynomial.C e)) *
        ((Polynomial.C Cs * Polynomial.X + Polynomial.C as) -
          (Polynomial.C Ct * Polynomial.X + Polynomial.C atc)) =
      Polynomial.C μ *
        (((Polynomial.C Cr * Polynomial.X + Polynomial.C ar) -
            (Polynomial.C Ct * Polynomial.X + Polynomial.C atc)) *
          ((Polynomial.C Cs * Polynomial.X + Polynomial.C as) -
            (Polynomial.C E * Polynomial.X + Polynomial.C e)))) :
    (Cr - E) * (Cs - Ct) = μ * ((Cr - Ct) * (Cs - E)) := by
  have hdiff (a b c d : R) :
      (Polynomial.C a * Polynomial.X + Polynomial.C b) -
          (Polynomial.C c * Polynomial.X + Polynomial.C d) =
        Polynomial.C (a - c) * Polynomial.X + Polynomial.C (b - d) := by
    rw [map_sub, map_sub]
    ring
  rw [hdiff Cr ar E e, hdiff Cs as Ct atc, hdiff Cr ar Ct atc,
    hdiff Cs as E e] at h
  have hcoeff (a b c d : R) :
      ((Polynomial.C a * Polynomial.X + Polynomial.C b) *
          (Polynomial.C c * Polynomial.X + Polynomial.C d)).coeff 2 = a * c := by
    have hp :
        (Polynomial.C a * Polynomial.X + Polynomial.C b) *
            (Polynomial.C c * Polynomial.X + Polynomial.C d) =
          Polynomial.C (a * c) * Polynomial.X ^ 2 +
            Polynomial.C (a * d + b * c) * Polynomial.X + Polynomial.C (b * d) := by
      simp only [map_mul, map_add]
      ring
    rw [hp]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
    norm_num
  have hc := congrArg (fun p : Polynomial R => p.coeff 2) h
  rw [hcoeff (Cr - E) (ar - e) (Cs - Ct) (as - atc),
    Polynomial.coeff_C_mul, hcoeff (Cr - Ct) (ar - atc) (Cs - E) (as - e)] at hc
  exact hc

end MathlibPlus.Algebra
