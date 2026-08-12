import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim25146

/-- Scaling the second polynomial argument by `h` scales its fixed-degree
resultant by the degree power of the first argument. -/
theorem resultant_content_formula {R : Type*} [CommRing R]
    (F Q : Polynomial R) (h : R) :
    Polynomial.resultant F (Polynomial.C h * Q) F.natDegree Q.natDegree =
      h ^ F.natDegree * Polynomial.resultant F Q F.natDegree Q.natDegree := by
  exact Polynomial.resultant_C_mul_right F Q F.natDegree Q.natDegree h

/-- In particular the corresponding content power divides the resultant. -/
theorem resultant_content_power_dvd {R : Type*} [CommRing R]
    (F Q : Polynomial R) (h : R) :
    h ^ F.natDegree ∣
      Polynomial.resultant F (Polynomial.C h * Q) F.natDegree Q.natDegree := by
  rw [resultant_content_formula]
  exact dvd_mul_right _ _

end MathlibPlus.Algebra.Claim25146
